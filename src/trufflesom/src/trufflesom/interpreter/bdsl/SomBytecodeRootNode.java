package trufflesom.interpreter.bdsl;

import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.bytecode.BytecodeNode;
import com.oracle.truffle.api.bytecode.BytecodeRootNode;
import com.oracle.truffle.api.bytecode.ConstantOperand;
import com.oracle.truffle.api.bytecode.EpilogReturn;
import com.oracle.truffle.api.bytecode.LocalAccessor;
import com.oracle.truffle.api.bytecode.GenerateBytecode;
import com.oracle.truffle.api.bytecode.Operation;
import com.oracle.truffle.api.bytecode.Variadic;
import com.oracle.truffle.api.dsl.Bind;
import com.oracle.truffle.api.dsl.Cached;
import com.oracle.truffle.api.dsl.Fallback;
import com.oracle.truffle.api.dsl.NeverDefault;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.exception.AbstractTruffleException;
import com.oracle.truffle.api.frame.FrameDescriptor;
import com.oracle.truffle.api.frame.MaterializedFrame;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.ControlFlowException;
import com.oracle.truffle.api.nodes.DirectCallNode;
import com.oracle.truffle.api.nodes.LoopNode;
import com.oracle.truffle.api.source.Source;

import trufflesom.compiler.MethodGenerationContext;
import trufflesom.interpreter.FrameOnStackMarker;
import trufflesom.interpreter.Invokable;
import trufflesom.interpreter.Method;
import trufflesom.interpreter.ReturnException;
import trufflesom.interpreter.SomLanguage;
import trufflesom.interpreter.nodes.ContextualNode;
import trufflesom.interpreter.nodes.ExpressionNode;
import trufflesom.interpreter.nodes.GlobalNode;
import trufflesom.interpreter.nodes.dispatch.AbstractDispatchNode;
import trufflesom.interpreter.nodes.dispatch.GenericDispatchNode;
import trufflesom.interpreter.nodes.dispatch.UninitializedDispatchNode;
import trufflesom.interpreter.objectstorage.FieldAccessorNode;
import trufflesom.interpreter.objectstorage.FieldAccessorNode.AbstractReadFieldNode;
import trufflesom.interpreter.objectstorage.FieldAccessorNode.AbstractWriteFieldNode;
import trufflesom.vm.Classes;
import trufflesom.vm.SendPlacement;
import trufflesom.vm.constants.Nil;
import trufflesom.vmobjects.SAbstractObject;
import trufflesom.vmobjects.SBlock;
import trufflesom.vmobjects.SClass;
import trufflesom.vmobjects.SInvokable;
import trufflesom.vmobjects.SInvokable.SMethod;
import trufflesom.vmobjects.SObject;
import trufflesom.vmobjects.SSymbol;


/**
 * The third TruffleSOM interpreter: a Truffle Bytecode DSL interpreter, selected with
 * {@code -Dsom.interp=BDSL}. Its bytecode is produced by
 * {@link trufflesom.compiler.bdsl.AstToBytecodeDsl} from the AST the normal SOM parser builds,
 * so both interpreters see the same call sites and the same parser-level inlining.
 */
@GenerateBytecode(languageClass = SomLanguage.class, enableUncachedInterpreter = false,
    boxingEliminationTypes = {long.class, double.class, boolean.class}, enableQuickening = true,
    enableMaterializedLocalAccesses = true, enableBlockScoping = false,
    defaultLocalValue = "nilValue()")
public abstract class SomBytecodeRootNode extends Invokable implements BytecodeRootNode {

  /** The parsed AST this bytecode was built from; kept so the DSL can reparse. */
  @CompilationFinal private Method astMethod;

  @CompilationFinal private boolean       catchesNonLocalReturn;
  @CompilationFinal private LocalAccessor  markerAccessor;

  protected SomBytecodeRootNode(final SomLanguage language,
      final FrameDescriptor.Builder frameDescriptor) {
    super(language, frameDescriptor.build());
  }

  protected static Object nilValue() {
    return Nil.nilObject;
  }

  public Method getAstMethod() {
    return astMethod;
  }

  public void setAstMethod(final Method method) {
    this.astMethod = method;
  }

  public void setCatchesNonLocalReturn(final LocalAccessor accessor) {
    this.catchesNonLocalReturn = true;
    this.markerAccessor = accessor;
  }

  private FrameOnStackMarker marker(final VirtualFrame frame,
      final BytecodeNode bytecodeNode) {
    Object m = markerAccessor.getObject(bytecodeNode, frame);
    return m instanceof FrameOnStackMarker fm ? fm : null;
  }

  @Override
  public Object interceptControlFlowException(final ControlFlowException ex,
      final VirtualFrame frame, final BytecodeNode bytecodeNode, final int bci)
      throws Throwable {
    if (catchesNonLocalReturn && ex instanceof ReturnException r) {
      FrameOnStackMarker m = marker(frame, bytecodeNode);
      if (m != null) {
        m.frameNoLongerOnStack();
        if (r.reachedTarget(m)) {
          return r.result();
        }
      }
    }
    throw ex;
  }

  @Override
  public Throwable interceptInternalException(final Throwable t, final VirtualFrame frame,
      final BytecodeNode bytecodeNode, final int bci) {
    clearMarker(frame, bytecodeNode);
    return t;
  }

  @Override
  public AbstractTruffleException interceptTruffleException(final AbstractTruffleException ex,
      final VirtualFrame frame, final BytecodeNode bytecodeNode, final int bci) {
    clearMarker(frame, bytecodeNode);
    return ex;
  }

  void clearMarker(final VirtualFrame frame, final BytecodeNode bytecodeNode) {
    if (catchesNonLocalReturn) {
      FrameOnStackMarker m = marker(frame, bytecodeNode);
      if (m != null) {
        m.frameNoLongerOnStack();
      }
    }
  }

  /** Takes the frame off the stack for non-local returns, as the AST does in a finally. */
  @EpilogReturn
  public static final class ClearOnStackMarker {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final Object returnValue,
        @Bind final BytecodeNode bytecodeNode, @Bind final SomBytecodeRootNode root) {
      root.clearMarker(frame, bytecodeNode);
      return returnValue;
    }
  }

  // ------------------------------------------------------------------ Invokable

  @Override
  public void setInvokableInfo(final String name, final Source source, final long sourceCoord) {
    super.setInvokableInfo(name, source, sourceCoord);
  }

  @Override
  public ExpressionNode inline(final MethodGenerationContext targetMgenc,
      final SMethod toBeInlined) {
    throw new UnsupportedOperationException(
        "The Bytecode DSL interpreter does not support load-time method inlining");
  }

  @Override
  public void propagateLoopCountThroughoutLexicalScope(final long count) {
    LoopNode.reportLoopCount(this,
        count > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) count);
  }

  @Override
  public boolean isTrivial() {
    return false;
  }

  @Override
  public boolean isCloningAllowed() {
    return false;
  }

  @Override
  protected boolean isCloneUninitializedSupported() {
    return false;
  }

  @Override
  public String getName() {
    return name == null ? "<bdsl>" : name;
  }

  @Override
  public String toString() {
    return getName();
  }

  // ------------------------------------------------------------------ operations

  /** Walks the {@code SBlock} chain to the enclosing method's materialized frame. */
  @Operation
  @ConstantOperand(type = int.class)
  public static final class GetContext {
    @Specialization
    public static MaterializedFrame doIt(final VirtualFrame frame, final int contextLevel) {
      return ContextualNode.determineContext(frame, contextLevel);
    }
  }

  /** Reads an argument of an enclosing method's frame. */
  @Operation
  @ConstantOperand(type = int.class)
  public static final class LoadOuterArgument {
    @Specialization
    public static Object doIt(final int index, final MaterializedFrame ctx) {
      return ctx.getArguments()[index];
    }
  }

  @Operation
  @ConstantOperand(type = int.class)
  public static final class StoreArgument {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final int index, final Object value) {
      frame.getArguments()[index] = value;
      return value;
    }
  }

  @Operation
  @ConstantOperand(type = int.class)
  public static final class StoreOuterArgument {
    @Specialization
    public static Object doIt(final int index, final MaterializedFrame ctx,
        final Object value) {
      ctx.getArguments()[index] = value;
      return value;
    }
  }

  /** A message send, with the AST interpreter's inline-cache chain behind it. */
  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class Send {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final SSymbol selector,
        @Variadic final Object[] arguments,
        @Cached("createDispatch(selector)") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, arguments);
    }

    @NeverDefault
    protected static AbstractDispatchNode createDispatch(final SSymbol selector) {
      return SendPlacement.JIT
          ? new GenericDispatchNode(selector)
          : new UninitializedDispatchNode(selector);
    }
  }

  /** A super send; the target is resolved when the bytecode is built, as in the AST. */
  @Operation
  @ConstantOperand(type = SInvokable.class)
  public static final class SuperSend {
    @Specialization
    public static Object doIt(final SInvokable method, @Variadic final Object[] arguments,
        @Cached("createCall(method)") final DirectCallNode call) {
      return call.call(arguments);
    }

    @NeverDefault
    protected static DirectCallNode createCall(final SInvokable method) {
      return DirectCallNode.create(method.getCallTarget());
    }
  }

  @Operation
  @ConstantOperand(type = int.class)
  public static final class FieldRead {
    @Specialization
    public static Object doIt(final int fieldIndex, final Object self,
        @Cached("createRead(fieldIndex)") final AbstractReadFieldNode read) {
      return read.read((SObject) self);
    }

    @NeverDefault
    protected static AbstractReadFieldNode createRead(final int fieldIndex) {
      return FieldAccessorNode.createRead(fieldIndex);
    }
  }

  @Operation
  @ConstantOperand(type = int.class)
  public static final class FieldWrite {
    @Specialization
    public static Object doIt(final int fieldIndex, final Object self, final Object value,
        @Cached("createWrite(fieldIndex)") final AbstractWriteFieldNode write) {
      return write.write((SObject) self, value);
    }

    @NeverDefault
    protected static AbstractWriteFieldNode createWrite(final int fieldIndex) {
      return FieldAccessorNode.createWrite(fieldIndex);
    }
  }

  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class GlobalRead {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final SSymbol globalName,
        @Cached("createGlobal(globalName)") final GlobalNode global) {
      return global.executeGeneric(frame);
    }

    @NeverDefault
    protected static GlobalNode createGlobal(final SSymbol globalName) {
      return GlobalNode.create(globalName, null);
    }
  }

  @Operation
  @ConstantOperand(type = SMethod.class)
  @ConstantOperand(type = boolean.class)
  public static final class CreateBlock {
    @Specialization
    public static SBlock doIt(final VirtualFrame frame, final SMethod blockMethod,
        final boolean withContext,
        @Cached("blockClass(blockMethod)") final SClass blockClass) {
      return new SBlock(blockMethod, blockClass, withContext ? frame.materialize() : null);
    }

    @NeverDefault
    protected static SClass blockClass(final SMethod blockMethod) {
      return Classes.getBlockClass(blockMethod.getNumberOfArguments());
    }
  }

  /** Installs this activation's frame-on-stack marker, for a method that has a {@code ^}
   * inside one of its blocks. */
  @Operation
  @ConstantOperand(type = LocalAccessor.class)
  public static final class InitOnStackMarker {
    @Specialization
    public static void doIt(final VirtualFrame frame, final LocalAccessor marker,
        @Bind final BytecodeNode bytecodeNode) {
      marker.setObject(bytecodeNode, frame, new FrameOnStackMarker());
    }
  }

  /** {@code ^expr} inside a block; mirrors {@code ReturnNonLocalNode}. */
  @Operation
  @ConstantOperand(type = int.class)
  public static final class NonLocalReturn {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final int contextLevel,
        final Object markerObj, final Object value) {
      FrameOnStackMarker marker = (FrameOnStackMarker) markerObj;
      if (marker != null && marker.isOnStack()) {
        throw new ReturnException(value, marker);
      }
      return escaped(frame, contextLevel);
    }

    private static Object escaped(final VirtualFrame frame, final int contextLevel) {
      SBlock block = (SBlock) frame.getArguments()[0];
      Object self = contextLevel == 0
          ? frame.getArguments()[0]
          : ContextualNode.determineContext(frame, contextLevel).getArguments()[0];
      return SAbstractObject.sendEscapedBlock(self, block);
    }
  }

  @Operation
  public static final class AsBool {
    @Specialization
    public static boolean doBool(final boolean value) {
      return value;
    }

    @Fallback
    public static boolean doOther(final Object value) {
      throw new IllegalStateException("Expected a boolean, but got " + value);
    }
  }

  @Operation
  public static final class NotBool {
    @Specialization
    public static boolean doBool(final boolean value) {
      return !value;
    }

    @Fallback
    public static boolean doOther(final Object value) {
      throw new IllegalStateException("Expected a boolean, but got " + value);
    }
  }

  @Operation
  public static final class IsNil {
    @Specialization
    public static boolean doIt(final Object value) {
      return value == Nil.nilObject;
    }
  }

  @Operation
  public static final class IsNotNil {
    @Specialization
    public static boolean doIt(final Object value) {
      return value != Nil.nilObject;
    }
  }

  /** {@code from <= to} for the inlined {@code to:do:}. */
  @Operation
  public static final class LessOrEqual {
    @Specialization
    public static boolean doLong(final long a, final long b) {
      return a <= b;
    }

    @Specialization
    public static boolean doLongDouble(final long a, final double b) {
      return a <= b;
    }

    @Specialization
    public static boolean doDouble(final double a, final double b) {
      return a <= b;
    }

    @Specialization
    public static boolean doDoubleLong(final double a, final long b) {
      return a <= b;
    }
  }

  /** {@code from >= to} for the inlined {@code downTo:do:}. */
  @Operation
  public static final class GreaterOrEqual {
    @Specialization
    public static boolean doLong(final long a, final long b) {
      return a >= b;
    }

    @Specialization
    public static boolean doLongDouble(final long a, final double b) {
      return a >= b;
    }

    @Specialization
    public static boolean doDouble(final double a, final double b) {
      return a >= b;
    }

    @Specialization
    public static boolean doDoubleLong(final double a, final long b) {
      return a >= b;
    }
  }

  @Operation
  public static final class Step {
    @Specialization
    public static long doLong(final long value, final long step) {
      return value + step;
    }

    @Specialization
    public static double doDouble(final double value, final long step) {
      return value + step;
    }
  }

}
