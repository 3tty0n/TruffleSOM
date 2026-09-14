package trufflesom.compiler.bdsl;

import static trufflesom.vm.SymbolTable.symFalse;
import static trufflesom.vm.SymbolTable.symNil;
import static trufflesom.vm.SymbolTable.symTrue;

import java.util.ArrayList;
import java.util.List;

import com.oracle.truffle.api.bytecode.BytecodeConfig;
import com.oracle.truffle.api.bytecode.BytecodeLocal;
import com.oracle.truffle.api.bytecode.LocalAccessor;

import trufflesom.compiler.Variable.Local;
import trufflesom.interpreter.LexicalScope;
import trufflesom.interpreter.Method;
import trufflesom.interpreter.SomLanguage;
import trufflesom.interpreter.bdsl.SomBytecodeRootNode;
import trufflesom.interpreter.bdsl.SomBytecodeRootNodeGen;
import trufflesom.interpreter.nodes.AbstractMessageSendNode;
import trufflesom.interpreter.nodes.ArgumentReadNode.LocalArgumentReadNode;
import trufflesom.interpreter.nodes.ArgumentReadNode.LocalArgumentWriteNode;
import trufflesom.interpreter.nodes.ArgumentReadNode.NonLocalArgumentReadNode;
import trufflesom.interpreter.nodes.ArgumentReadNode.NonLocalArgumentWriteNode;
import trufflesom.interpreter.nodes.ExpressionNode;
import trufflesom.interpreter.nodes.FieldNode.FieldReadNode;
import trufflesom.interpreter.nodes.FieldNode.FieldWriteNode;
import trufflesom.interpreter.nodes.GlobalNode;
import trufflesom.interpreter.nodes.LocalVariableNode.LocalVariableReadNode;
import trufflesom.interpreter.nodes.LocalVariableNode.LocalVariableWriteNode;
import trufflesom.interpreter.nodes.MessageSendNode.BdslSuperSendNode;
import trufflesom.interpreter.nodes.NonLocalVariableNode.NonLocalVariableReadNode;
import trufflesom.interpreter.nodes.NonLocalVariableNode.NonLocalVariableWriteNode;
import trufflesom.interpreter.nodes.ReturnNonLocalNode;
import trufflesom.interpreter.nodes.ReturnNonLocalNode.CatchNonLocalReturnNode;
import trufflesom.interpreter.nodes.ReturnNonLocalNode.ReturnLocalNode;
import trufflesom.interpreter.nodes.SequenceNode;
import trufflesom.interpreter.nodes.UninitializedMessageSendNode;
import trufflesom.interpreter.nodes.literals.BlockNode;
import trufflesom.interpreter.nodes.literals.BlockNode.BlockNodeWithContext;
import trufflesom.interpreter.nodes.literals.LiteralNode;
import trufflesom.interpreter.nodes.specialized.BooleanInlinedLiteralNode.AndInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.BooleanInlinedLiteralNode.OrInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.IfInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.IfNilInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.IfNilNotNilInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.IfNotNilInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.IfNotNilNilInlinedLiteralNode;
import trufflesom.interpreter.nodes.specialized.IfTrueIfFalseInlinedLiteralsNode;
import trufflesom.interpreter.nodes.specialized.IntDownToDoInlinedLiteralsNode;
import trufflesom.interpreter.nodes.specialized.IntToDoInlinedLiteralsNode;
import trufflesom.interpreter.nodes.specialized.whileloops.WhileInlinedLiteralsNode;
import trufflesom.vm.constants.Nil;
import trufflesom.vmobjects.SInvokable.SMethod;
import trufflesom.vmobjects.SSymbol;


/**
 * Translates a parsed SOM method, including its nested blocks, into Truffle Bytecode DSL root
 * nodes and installs them as the invokables of the method and of its blocks. The AST the SOM
 * parser produced is only read, never executed, so both interpreters agree on which sends exist
 * and which control flow the parser inlined.
 */
public final class AstToBytecodeDsl {

  /** Translates {@code method} and all of its (transitively) embedded blocks. */
  public static void install(final SMethod method) {
    List<Object[]> installed = new ArrayList<>();
    SomBytecodeRootNodeGen.create(SomLanguage.getCurrent(), BytecodeConfig.DEFAULT, b -> {
      installed.clear();
      new AstToBytecodeDsl(b, installed).translateRoot(method, true);
    });

    for (Object[] pair : installed) {
      ((SMethod) pair[0]).setInvokable((SomBytecodeRootNode) pair[1]);
    }
  }

  private final SomBytecodeRootNodeGen.Builder b;
  private final List<Object[]>                 installed;
  private final List<BytecodeLocal[]>          scopes;

  private AstToBytecodeDsl(final SomBytecodeRootNodeGen.Builder builder,
      final List<Object[]> installed) {
    this.b = builder;
    this.installed = installed;
    this.scopes = new ArrayList<>();
  }

  // ------------------------------------------------------------------ roots

  private void translateRoot(final SMethod sMethod, final boolean isMethod) {
    Method method = astMethodOf(sMethod);

    b.beginRoot();
    pushScope(method.getScope());

    ExpressionNode body = method.getBody();
    BytecodeLocal marker = null;
    if (body instanceof CatchNonLocalReturnNode c) {
      marker = local(0, c.getOnStackMarkerVar());
      body = c.getFirstMethodBodyNode();
    }

    b.beginBlock();
    if (marker != null) {
      b.emitInitOnStackMarker(marker);
    }
    b.beginReturn();
    translate(body);
    b.endReturn();
    b.endBlock();

    SomBytecodeRootNode root = b.endRoot();
    popScope();

    if (marker != null) {
      root.setCatchesNonLocalReturn(LocalAccessor.constantOf(marker));
    }
    root.setAstMethod(method);
    root.setInvokableInfo(method.getName(), method.getSource(), method.getSourceCoordinate());
    installed.add(new Object[] {sMethod, root});
  }

  private static Method astMethodOf(final SMethod sMethod) {
    return sMethod.getInvokable() instanceof SomBytecodeRootNode bc
        ? bc.getAstMethod()
        : (Method) sMethod.getInvokable();
  }

  private void pushScope(final LexicalScope scope) {
    int numLocals = scope.getNumberOfLocals();
    BytecodeLocal[] locals = new BytecodeLocal[numLocals];
    for (int i = 0; i < numLocals; i += 1) {
      locals[i] = b.createLocal();
    }
    scopes.add(locals);
  }

  private void popScope() {
    scopes.remove(scopes.size() - 1);
  }

  private BytecodeLocal local(final int contextLevel, final Local variable) {
    return scopes.get(scopes.size() - 1 - contextLevel)[variable.getIndex()];
  }

  /** A fresh helper local in the innermost scope, for the inlined counting loops. */
  private BytecodeLocal temp() {
    return b.createLocal();
  }

  // ------------------------------------------------------------------ expressions

  private void translate(final ExpressionNode node) {
    if (node instanceof BlockNode block) {
      translateBlock(block);
    } else if (node instanceof LiteralNode) {
      b.emitLoadConstant(node.executeGeneric(null));
    } else if (node instanceof GlobalNode global) {
      translateGlobal(global);
    } else if (node instanceof SequenceNode seq) {
      b.beginBlock();
      for (ExpressionNode e : seq.getExpressions()) {
        translate(e);
      }
      b.endBlock();
    } else if (node instanceof LocalVariableReadNode read) {
      b.emitLoadLocal(local(0, read.getLocal()));
    } else if (node instanceof LocalVariableWriteNode write) {
      BytecodeLocal l = local(0, write.getLocal());
      b.beginBlock();
      b.beginStoreLocal(l);
      translate(write.getExp());
      b.endStoreLocal();
      b.emitLoadLocal(l);
      b.endBlock();
    } else if (node instanceof NonLocalVariableReadNode read) {
      b.beginLoadLocalMaterialized(local(read.getContextLevel(), read.getLocal()));
      b.emitGetContext(read.getContextLevel());
      b.endLoadLocalMaterialized();
    } else if (node instanceof NonLocalVariableWriteNode write) {
      BytecodeLocal l = local(write.getContextLevel(), write.getLocal());
      b.beginBlock();
      b.beginStoreLocalMaterialized(l);
      b.emitGetContext(write.getContextLevel());
      translate(write.getExp());
      b.endStoreLocalMaterialized();
      b.beginLoadLocalMaterialized(l);
      b.emitGetContext(write.getContextLevel());
      b.endLoadLocalMaterialized();
      b.endBlock();
    } else if (node instanceof LocalArgumentReadNode read) {
      b.emitLoadArgument(read.argumentIndex);
    } else if (node instanceof LocalArgumentWriteNode write) {
      b.beginStoreArgument(write.getArgumentIndex());
      translate(write.getValueNode());
      b.endStoreArgument();
    } else if (node instanceof NonLocalArgumentWriteNode write) {
      b.beginStoreOuterArgument(write.getArgumentIndex());
      b.emitGetContext(write.getContextLevel());
      translate(write.getValueNode());
      b.endStoreOuterArgument();
    } else if (node instanceof NonLocalArgumentReadNode read) {
      b.beginLoadOuterArgument(read.arg.index);
      b.emitGetContext(read.getContextLevel());
      b.endLoadOuterArgument();
    } else if (node instanceof FieldReadNode read) {
      b.beginFieldRead(read.getFieldIndex());
      translate(read.getSelf());
      b.endFieldRead();
    } else if (node instanceof FieldWriteNode write) {
      b.beginFieldWrite(write.getFieldIndex());
      translate(write.getSelf());
      translate(write.getValue());
      b.endFieldWrite();
    } else if (node instanceof BdslSuperSendNode superSend) {
      b.beginSuperSend(superSend.getMethod());
      for (ExpressionNode arg : superSend.getArgumentNodes()) {
        translate(arg);
      }
      b.endSuperSend();
    } else if (node instanceof UninitializedMessageSendNode send) {
      translateSend(send.getSelector(), send.getArgumentNodes());
    } else if (node instanceof AbstractMessageSendNode send) {
      throw new UnsupportedOperationException(
          "Unexpected message send node in the Bytecode DSL translator: " + send.getClass());
    } else if (node instanceof ReturnNonLocalNode ret) {
      translateNonLocalReturn(ret.getContextLevel(), ret.getOnStackMarkerVar(),
          ret.getExpression());
    } else if (node instanceof ReturnLocalNode ret) {
      translateNonLocalReturn(0, ret.getOnStackMarkerVar(), ret.getExpression());
    } else {
      translateInlined(node);
    }
  }

  private void translateSend(final SSymbol selector, final ExpressionNode[] args) {
    b.beginSend(selector);
    for (ExpressionNode arg : args) {
      translate(arg);
    }
    b.endSend();
  }

  private void translateGlobal(final GlobalNode global) {
    SSymbol name = global.getGlobalName();
    if (name == symNil) {
      b.emitLoadConstant(Nil.nilObject);
    } else if (name == symTrue) {
      b.emitLoadConstant(Boolean.TRUE);
    } else if (name == symFalse) {
      b.emitLoadConstant(Boolean.FALSE);
    } else {
      b.emitGlobalRead(name);
    }
  }

  private void translateBlock(final BlockNode block) {
    SMethod blockMethod = block.getMethod();
    translateRoot(blockMethod, false);
    b.emitCreateBlock(blockMethod, block instanceof BlockNodeWithContext);
  }

  private void translateNonLocalReturn(final int contextLevel, final Local markerVar,
      final ExpressionNode expression) {
    b.beginNonLocalReturn(contextLevel);
    if (contextLevel == 0) {
      b.emitLoadLocal(local(0, markerVar));
    } else {
      b.beginLoadLocalMaterialized(local(contextLevel, markerVar));
      b.emitGetContext(contextLevel);
      b.endLoadLocalMaterialized();
    }
    translate(expression);
    b.endNonLocalReturn();
  }

  // ------------------------------------------------------------- inlined control flow

  private void translateCondition(final ExpressionNode condition, final boolean expected) {
    if (expected) {
      b.beginAsBool();
    } else {
      b.beginNotBool();
    }
    translate(condition);
    if (expected) {
      b.endAsBool();
    } else {
      b.endNotBool();
    }
  }

  private void translateInlined(final ExpressionNode node) {
    if (node instanceof IfInlinedLiteralNode n) {
      b.beginConditional();
      translateCondition(n.getConditionNode(), n.getExpectedBool());
      translate(n.getBodyNode());
      b.emitLoadConstant(Nil.nilObject);
      b.endConditional();
    } else if (node instanceof IfTrueIfFalseInlinedLiteralsNode n) {
      b.beginConditional();
      translateCondition(n.getConditionNode(), true);
      translate(n.getTrueNode());
      translate(n.getFalseNode());
      b.endConditional();
    } else if (node instanceof AndInlinedLiteralNode n) {
      b.beginConditional();
      translateCondition(n.getReceiverNode(), true);
      translateCondition(n.getArgumentNode(), true);
      b.emitLoadConstant(Boolean.FALSE);
      b.endConditional();
    } else if (node instanceof OrInlinedLiteralNode n) {
      b.beginConditional();
      translateCondition(n.getReceiverNode(), true);
      b.emitLoadConstant(Boolean.TRUE);
      translateCondition(n.getArgumentNode(), true);
      b.endConditional();
    } else if (node instanceof IfNilInlinedLiteralNode n) {
      translateIfNil(n.getRcvr(), n.getArg1(), null, true);
    } else if (node instanceof IfNotNilInlinedLiteralNode n) {
      translateIfNil(n.getRcvr(), n.getArg1(), null, false);
    } else if (node instanceof IfNilNotNilInlinedLiteralNode n) {
      translateIfNil(n.getRcvr(), n.getArg1(), n.getArg2(), true);
    } else if (node instanceof IfNotNilNilInlinedLiteralNode n) {
      translateIfNil(n.getRcvr(), n.getArg2(), n.getArg1(), true);
    } else if (node instanceof WhileInlinedLiteralsNode n) {
      b.beginBlock();
      b.beginWhile();
      translateCondition(n.getConditionNode(), n.getExpectedBool());
      translate(n.getBodyNode());
      b.endWhile();
      b.emitLoadConstant(Nil.nilObject);
      b.endBlock();
    } else if (node instanceof IntToDoInlinedLiteralsNode n) {
      translateCountingLoop(n.getFrom(), n.getTo(), n.getBody(), n.getLoopIdxVar(), true);
    } else if (node instanceof IntDownToDoInlinedLiteralsNode n) {
      translateCountingLoop(n.getFrom(), n.getTo(), n.getBody(), n.getLoopIdxVar(), false);
    } else {
      throw new UnsupportedOperationException(
          "The Bytecode DSL translator does not handle " + node.getClass().getName());
    }
  }

  /**
   * {@code rcvr ifNil: whenNil ifNotNil: whenNotNil}, where a missing branch yields the
   * receiver.
   */
  private void translateIfNil(final ExpressionNode rcvr, final ExpressionNode whenNil,
      final ExpressionNode whenNotNil, final boolean nilFirst) {
    BytecodeLocal r = temp();
    b.beginBlock();
    b.beginStoreLocal(r);
    translate(rcvr);
    b.endStoreLocal();

    b.beginConditional();
    if (nilFirst) {
      b.beginIsNil();
    } else {
      b.beginIsNotNil();
    }
    b.emitLoadLocal(r);
    if (nilFirst) {
      b.endIsNil();
    } else {
      b.endIsNotNil();
    }
    translate(whenNil);
    if (whenNotNil == null) {
      b.emitLoadLocal(r);
    } else {
      translate(whenNotNil);
    }
    b.endConditional();
    b.endBlock();
  }

  /** The parser-inlined {@code to:do:} / {@code downTo:do:}, as a Bytecode DSL loop. */
  private void translateCountingLoop(final ExpressionNode from, final ExpressionNode to,
      final ExpressionNode body, final Local loopIdxVar, final boolean up) {
    BytecodeLocal idx = local(0, loopIdxVar);
    BytecodeLocal start = temp();
    BytecodeLocal limit = temp();

    b.beginBlock();

    b.beginStoreLocal(start);
    translate(from);
    b.endStoreLocal();

    b.beginStoreLocal(limit);
    translate(to);
    b.endStoreLocal();

    b.beginStoreLocal(idx);
    b.emitLoadLocal(start);
    b.endStoreLocal();

    b.beginWhile();
    if (up) {
      b.beginLessOrEqual();
    } else {
      b.beginGreaterOrEqual();
    }
    b.emitLoadLocal(idx);
    b.emitLoadLocal(limit);
    if (up) {
      b.endLessOrEqual();
    } else {
      b.endGreaterOrEqual();
    }

    b.beginBlock();
    translate(body);
    b.beginStoreLocal(idx);
    b.beginStep();
    b.emitLoadLocal(idx);
    b.emitLoadConstant(up ? 1L : -1L);
    b.endStep();
    b.endStoreLocal();
    b.endBlock();
    b.endWhile();

    b.emitLoadLocal(start);
    b.endBlock();
  }
}
