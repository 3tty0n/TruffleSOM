package trufflesom.interpreter.bdsl;

import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.bytecode.BytecodeNode;
import com.oracle.truffle.api.bytecode.BytecodeRootNode;
import com.oracle.truffle.api.bytecode.ConstantOperand;
import com.oracle.truffle.api.bytecode.EpilogReturn;
import com.oracle.truffle.api.bytecode.ForceQuickening;
import com.oracle.truffle.api.bytecode.LocalAccessor;
import com.oracle.truffle.api.bytecode.GenerateBytecode;
import com.oracle.truffle.api.bytecode.Operation;
import com.oracle.truffle.api.bytecode.Variadic;
import com.oracle.truffle.api.dsl.Bind;
import com.oracle.truffle.api.dsl.Cached;
import com.oracle.truffle.api.dsl.Fallback;
import com.oracle.truffle.api.dsl.NeverDefault;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.profiles.InlinedBranchProfile;
import com.oracle.truffle.api.nodes.Node;
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
import trufflesom.primitives.arithmetic.AdditionPrim;
import trufflesom.primitives.arithmetic.BitXorPrim;
import trufflesom.primitives.arithmetic.DividePrim;
import trufflesom.primitives.arithmetic.DoubleDivPrim;
import trufflesom.primitives.arithmetic.GreaterThanOrEqualPrim;
import trufflesom.primitives.arithmetic.GreaterThanPrim;
import trufflesom.primitives.arithmetic.LessThanOrEqualPrim;
import trufflesom.primitives.arithmetic.LessThanPrim;
import trufflesom.primitives.arithmetic.LogicAndPrim;
import trufflesom.primitives.arithmetic.ModuloPrim;
import trufflesom.primitives.arithmetic.MultiplicationPrim;
import trufflesom.primitives.arithmetic.RemainderPrim;
import trufflesom.primitives.arithmetic.SubtractionPrim;
import trufflesom.primitives.basics.EqualsEqualsPrim;
import trufflesom.primitives.basics.EqualsPrim;
import trufflesom.primitives.basics.IntegerPrims.AbsPrim;
import trufflesom.primitives.basics.IntegerPrims.As32BitSignedValue;
import trufflesom.primitives.basics.IntegerPrims.As32BitUnsignedValue;
import trufflesom.primitives.basics.IntegerPrims.AsDoubleValue;
import trufflesom.primitives.basics.IntegerPrims.LeftShiftPrim;
import trufflesom.primitives.basics.IntegerPrims.MaxIntPrim;
import trufflesom.primitives.basics.IntegerPrims.MinIntPrim;
import trufflesom.primitives.basics.IntegerPrims.NegatedValue;
import trufflesom.primitives.basics.IntegerPrims.UnsignedRightShiftPrim;
import trufflesom.primitives.basics.UnequalUnequalPrim;
import trufflesom.primitives.basics.UnequalsPrim;
import trufflesom.interpreter.nodes.specialized.NotMessageNode;
import trufflesom.vm.Classes;
import trufflesom.vm.SymbolTable;
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
    @ForceQuickening
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
    @ForceQuickening
    public static MaterializedFrame doIt(final VirtualFrame frame, final int contextLevel) {
      return ContextualNode.determineContext(frame, contextLevel);
    }
  }

  /** Reads an argument of an enclosing method's frame. */
  @Operation
  @ConstantOperand(type = int.class)
  public static final class LoadOuterArgument {
    @Specialization
    @ForceQuickening
    public static Object doIt(final int index, final MaterializedFrame ctx) {
      return ctx.getArguments()[index];
    }
  }

  @Operation
  @ConstantOperand(type = int.class)
  public static final class StoreArgument {
    @Specialization
    @ForceQuickening
    public static Object doIt(final VirtualFrame frame, final int index, final Object value) {
      frame.getArguments()[index] = value;
      return value;
    }
  }

  @Operation
  @ConstantOperand(type = int.class)
  public static final class StoreOuterArgument {
    @Specialization
    @ForceQuickening
    public static Object doIt(final int index, final MaterializedFrame ctx,
        final Object value) {
      ctx.getArguments()[index] = value;
      return value;
    }
  }

  @NeverDefault
  protected static AbstractDispatchNode dispatchFor(final SSymbol selector) {
    return SendPlacement.JIT
        ? new GenericDispatchNode(selector)
        : new UninitializedDispatchNode(selector);
  }

  /** A message send, with the AST interpreter's inline-cache chain behind it. */
  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class Send {
    @Specialization
    @ForceQuickening
    public static Object doIt(final VirtualFrame frame, final SSymbol selector,
        @Variadic final Object[] arguments,
        @Cached("createDispatch(selector)") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, arguments);
    }

    @NeverDefault
    protected static AbstractDispatchNode createDispatch(final SSymbol selector) {
      return dispatchFor(selector);
    }
  }

  /** A message send with 0 arguments, so no argument array is built before dispatch. */
  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class Send0 {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final SSymbol selector, final Object rcvr,
        @Cached("createDispatch(selector)") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {rcvr});
    }

    @NeverDefault
    protected static AbstractDispatchNode createDispatch(final SSymbol selector) {
      return dispatchFor(selector);
    }
  }

  /** A message send with 1 argument, so no argument array is built before dispatch. */
  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class Send1 {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final SSymbol selector, final Object rcvr, final Object a1,
        @Cached("createDispatch(selector)") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {rcvr, a1});
    }

    @NeverDefault
    protected static AbstractDispatchNode createDispatch(final SSymbol selector) {
      return dispatchFor(selector);
    }
  }

  /** A message send with 2 arguments, so no argument array is built before dispatch. */
  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class Send2 {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final SSymbol selector, final Object rcvr, final Object a1, final Object a2,
        @Cached("createDispatch(selector)") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {rcvr, a1, a2});
    }

    @NeverDefault
    protected static AbstractDispatchNode createDispatch(final SSymbol selector) {
      return dispatchFor(selector);
    }
  }

  /** A message send with 3 arguments, so no argument array is built before dispatch. */
  @Operation
  @ConstantOperand(type = SSymbol.class)
  public static final class Send3 {
    @Specialization
    public static Object doIt(final VirtualFrame frame, final SSymbol selector, final Object rcvr, final Object a1, final Object a2, final Object a3,
        @Cached("createDispatch(selector)") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {rcvr, a1, a2, a3});
    }

    @NeverDefault
    protected static AbstractDispatchNode createDispatch(final SSymbol selector) {
      return dispatchFor(selector);
    }
  }

  /** A super send; the target is resolved when the bytecode is built, as in the AST. */
  @Operation
  @ConstantOperand(type = SInvokable.class)
  public static final class SuperSend {
    @Specialization
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
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
    @ForceQuickening
    public static boolean doIt(final Object value) {
      return value == Nil.nilObject;
    }
  }

  @Operation
  public static final class IsNotNil {
    @Specialization
    @ForceQuickening
    public static boolean doIt(final Object value) {
      return value != Nil.nilObject;
    }
  }

  /** {@code from <= to} for the inlined {@code to:do:}. */
  @Operation
  public static final class LessOrEqual {
    @Specialization
    @ForceQuickening
    public static boolean doLong(final long a, final long b) {
      return a <= b;
    }

    @Specialization
    public static boolean doLongDouble(final long a, final double b) {
      return a <= b;
    }

    @Specialization
    @ForceQuickening
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
    @ForceQuickening
    public static boolean doLong(final long a, final long b) {
      return a >= b;
    }

    @Specialization
    public static boolean doLongDouble(final long a, final double b) {
      return a >= b;
    }

    @Specialization
    @ForceQuickening
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
    @ForceQuickening
    public static long doLong(final long value, final long step) {
      return value + step;
    }

    @Specialization
    @ForceQuickening
    public static double doDouble(final double value, final long step) {
      return value + step;
    }
  }

  /** The eagerly specialised {@code +}, as the AST parser builds it. */
  @Operation
  public static final class PrimAdd {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("+");

    @Specialization(rewriteOn = ArithmeticException.class)
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return AdditionPrim.doLong(a, b);
    }

    @Specialization
    public static Object doLLBig(final long a, final long b) {
      return AdditionPrim.doLongWithOverflow(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doLD(final long a, final double b) {
      return AdditionPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDD(final double a, final double b) {
      return AdditionPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDL(final double a, final long b) {
      return AdditionPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code -}, as the AST parser builds it. */
  @Operation
  public static final class PrimSub {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("-");

    @Specialization(rewriteOn = ArithmeticException.class)
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return SubtractionPrim.doLong(a, b);
    }

    @Specialization
    public static Object doLLBig(final long a, final long b) {
      return SubtractionPrim.doLongWithOverflow(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doLD(final long a, final double b) {
      return SubtractionPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDD(final double a, final double b) {
      return SubtractionPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDL(final double a, final long b) {
      return SubtractionPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code *}, as the AST parser builds it. */
  @Operation
  public static final class PrimMul {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("*");

    @Specialization(rewriteOn = ArithmeticException.class)
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return MultiplicationPrim.doLong(a, b);
    }

    @Specialization
    public static Object doLLBig(final long a, final long b) {
      return MultiplicationPrim.doLongWithOverflow(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doLD(final long a, final double b) {
      return MultiplicationPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDD(final double a, final double b) {
      return MultiplicationPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDL(final double a, final long b) {
      return MultiplicationPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code /}, as the AST parser builds it. */
  @Operation
  public static final class PrimDiv {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("/");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return DividePrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static long doLD(final long a, final double b) {
      return DividePrim.doLong(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code //}, as the AST parser builds it. */
  @Operation
  public static final class PrimDoubleDiv {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("//");

    @Specialization
    @ForceQuickening
    public static double doLL(final long a, final long b) {
      return DoubleDivPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doLD(final long a, final double b) {
      return DoubleDivPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDD(final double a, final double b) {
      return DoubleDivPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDL(final double a, final long b) {
      return DoubleDivPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code %}, as the AST parser builds it. */
  @Operation
  public static final class PrimMod {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("%");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return ModuloPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doLD(final long a, final double b) {
      return ModuloPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDD(final double a, final double b) {
      return ModuloPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDL(final double a, final long b) {
      return ModuloPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code rem:}, as the AST parser builds it. */
  @Operation
  public static final class PrimRem {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("rem:");

    @Specialization(rewriteOn = ArithmeticException.class)
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return RemainderPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doLD(final long a, final double b) {
      return RemainderPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDD(final double a, final double b) {
      return RemainderPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static double doDL(final double a, final long b) {
      return RemainderPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code &}, as the AST parser builds it. */
  @Operation
  public static final class PrimLogicAnd {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("&");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return LogicAndPrim.doLong(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code bitXor:}, as the AST parser builds it. */
  @Operation
  public static final class PrimBitXor {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("bitXor:");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return BitXorPrim.doLong(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code >>>}, as the AST parser builds it. */
  @Operation
  public static final class PrimUnsignedRightShift {
    static final SSymbol SELECTOR = SymbolTable.symbolFor(">>>");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return UnsignedRightShiftPrim.doLong(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code min:}, as the AST parser builds it. */
  @Operation
  public static final class PrimMin {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("min:");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return MinIntPrim.doLong(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code max:}, as the AST parser builds it. */
  @Operation
  public static final class PrimMax {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("max:");

    @Specialization
    @ForceQuickening
    public static long doLL(final long a, final long b) {
      return MaxIntPrim.doLong(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code <}, as the AST parser builds it. */
  @Operation
  public static final class PrimLessThan {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("<");

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return LessThanPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLD(final long a, final double b) {
      return LessThanPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return LessThanPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDL(final double a, final long b) {
      return LessThanPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code <=}, as the AST parser builds it. */
  @Operation
  public static final class PrimLessThanOrEqual {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("<=");

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return LessThanOrEqualPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLD(final long a, final double b) {
      return LessThanOrEqualPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return LessThanOrEqualPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDL(final double a, final long b) {
      return LessThanOrEqualPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code >}, as the AST parser builds it. */
  @Operation
  public static final class PrimGreaterThan {
    static final SSymbol SELECTOR = SymbolTable.symbolFor(">");

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return GreaterThanPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLD(final long a, final double b) {
      return GreaterThanPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return GreaterThanPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDL(final double a, final long b) {
      return GreaterThanPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code >=}, as the AST parser builds it. */
  @Operation
  public static final class PrimGreaterThanOrEqual {
    static final SSymbol SELECTOR = SymbolTable.symbolFor(">=");

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return GreaterThanOrEqualPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLD(final long a, final double b) {
      return GreaterThanOrEqualPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return GreaterThanOrEqualPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDL(final double a, final long b) {
      return GreaterThanOrEqualPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code =}, as the AST parser builds it. */
  @Operation
  public static final class PrimEquals {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("=");

    @Specialization
    @ForceQuickening
    public static boolean doBB(final boolean a, final boolean b) {
      return EqualsPrim.doBoolean(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return EqualsPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLD(final long a, final double b) {
      return EqualsPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return EqualsPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDL(final double a, final long b) {
      return EqualsPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code <>}, as the AST parser builds it. */
  @Operation
  public static final class PrimUnequals {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("<>");

    @Specialization
    @ForceQuickening
    public static boolean doBB(final boolean a, final boolean b) {
      return UnequalsPrim.doBoolean(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return UnequalsPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doLD(final long a, final double b) {
      return UnequalsPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return UnequalsPrim.doDouble(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDL(final double a, final long b) {
      return UnequalsPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code ==}, as the AST parser builds it. */
  @Operation
  public static final class PrimIdentical {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("==");

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return EqualsEqualsPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return EqualsEqualsPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code ~=}, as the AST parser builds it. */
  @Operation
  public static final class PrimNotIdentical {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("~=");

    @Specialization
    @ForceQuickening
    public static boolean doLL(final long a, final long b) {
      return UnequalUnequalPrim.doLong(a, b);
    }

    @Specialization
    @ForceQuickening
    public static boolean doDD(final double a, final double b) {
      return UnequalUnequalPrim.doDouble(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }

  /** The eagerly specialised {@code negated}, as the AST parser builds it. */
  @Operation
  public static final class PrimNegated {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("negated");

    @Specialization
    @ForceQuickening
    public static long doL(final long a) {
      return NegatedValue.doLong(a);
    }

    @Specialization
    @ForceQuickening
    public static double doD(final double a) {
      return NegatedValue.doDouble(a);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a});
    }
  }

  /** The eagerly specialised {@code asDouble}, as the AST parser builds it. */
  @Operation
  public static final class PrimAsDouble {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("asDouble");

    @Specialization
    @ForceQuickening
    public static double doL(final long a) {
      return AsDoubleValue.doLong(a);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a});
    }
  }

  /** The eagerly specialised {@code as32BitSignedValue}, as the AST parser builds it. */
  @Operation
  public static final class PrimAs32BitSignedValue {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("as32BitSignedValue");

    @Specialization
    @ForceQuickening
    public static long doL(final long a) {
      return As32BitSignedValue.doLong(a);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a});
    }
  }

  /** The eagerly specialised {@code as32BitUnsignedValue}, as the AST parser builds it. */
  @Operation
  public static final class PrimAs32BitUnsignedValue {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("as32BitUnsignedValue");

    @Specialization
    @ForceQuickening
    public static long doL(final long a) {
      return As32BitUnsignedValue.doLong(a);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a});
    }
  }

  /** The eagerly specialised {@code not}, as the AST parser builds it. */
  @Operation
  public static final class PrimNot {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("not");

    @Specialization
    @ForceQuickening
    public static boolean doB(final boolean a) {
      return NotMessageNode.doNot(a);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a});
    }
  }

  /** The eagerly specialised {@code abs}, as the AST parser builds it. */
  @Operation
  public static final class PrimAbs {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("abs");

    @Specialization(guards = "!minLong(a)")
    @ForceQuickening
    public static long doL(final long a) {
      return AbsPrim.doLong(a);
    }

    @Specialization
    @ForceQuickening
    public static double doD(final double a) {
      return Math.abs(a);
    }

    protected static boolean minLong(final long a) {
      return AbsPrim.minLong(a);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a});
    }
  }

  /** The eagerly specialised {@code <<}, as the AST parser builds it. */
  @Operation
  public static final class PrimLeftShift {
    static final SSymbol SELECTOR = SymbolTable.symbolFor("<<");

    @Specialization(rewriteOn = ArithmeticException.class)
    @ForceQuickening
    public static long doLL(final long a, final long b,
        @Cached final InlinedBranchProfile overflow, @Bind final Node node) {
      return LeftShiftPrim.doLong(a, b, overflow, node);
    }

    @Specialization
    public static Object doLLBig(final long a, final long b) {
      return LeftShiftPrim.doLongWithOverflow(a, b);
    }


    @NeverDefault
    protected static AbstractDispatchNode dispatch() {
      return dispatchFor(SELECTOR);
    }

    @Fallback
    public static Object doSend(final VirtualFrame frame, final Object a, final Object b,
        @Cached("dispatch()") final AbstractDispatchNode dispatch) {
      return dispatch.executeDispatch(frame, new Object[] {a, b});
    }
  }


}
