package trufflesom.interpreter.nodes;

import com.oracle.truffle.api.Truffle;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.DirectCallNode;

import trufflesom.bdt.primitives.Specializer;
import trufflesom.bdt.primitives.nodes.PreevaluatedExpression;
import com.oracle.truffle.api.Assumption;
import com.oracle.truffle.api.CompilerDirectives;

import trufflesom.interpreter.nodes.dispatch.AbstractDispatchNode;
import trufflesom.interpreter.nodes.dispatch.GenericDispatchNode;
import trufflesom.interpreter.nodes.dispatch.UninitializedDispatchNode;
import trufflesom.primitives.Primitives;
import trufflesom.vm.NotYetImplementedException;
import trufflesom.vm.VmSettings;
import trufflesom.vmobjects.SClass;
import trufflesom.vmobjects.SInvokable;
import trufflesom.vmobjects.SSymbol;


public final class MessageSendNode {

  public static ExpressionNode create(final SSymbol selector,
      final ExpressionNode[] arguments, final long coord) {
    if (VmSettings.UseBdslInterp) {
      return new UninitializedMessageSendNode(selector, arguments).initialize(coord);
    }

    Specializer<ExpressionNode, SSymbol> specializer =
        Primitives.Current.getParserSpecializer(selector, arguments);
    if (specializer == null) {
      return new UninitializedMessageSendNode(selector, arguments).initialize(coord);
    }

    return specializer.create(null, arguments, coord);
  }

  private static final ExpressionNode[] NO_ARGS = new ExpressionNode[0];

  public static AbstractMessageSendNode createForPerformNodes(final SSymbol selector,
      final long coord) {
    return new UninitializedMessageSendNode(selector, NO_ARGS).initialize(coord);
  }

  public static GenericMessageSendNode createGeneric(final SSymbol selector,
      final ExpressionNode[] argumentNodes, final long coord) {
    return new GenericMessageSendNode(selector, argumentNodes,
        new UninitializedDispatchNode(selector)).initialize(coord);
  }

  public static GenericMessageSendNode createGenericDispatch(final SSymbol selector,
      final ExpressionNode[] argumentNodes, final long coord) {
    return new GenericMessageSendNode(selector, argumentNodes,
        new GenericDispatchNode(selector)).initialize(coord);
  }

  public static GenericMessageSendNode createBoundaryDispatch(final SSymbol selector,
      final ExpressionNode[] argumentNodes, final long coord) {
    return new GenericMessageSendNode(selector, argumentNodes,
        new UninitializedDispatchNode(selector, true)).initialize(coord);
  }

  public static AbstractMessageSendNode createBoundSelfSend(final SSymbol selector,
      final ExpressionNode[] arguments, final SInvokable method, final Assumption assumption,
      final long coord) {
    DirectCallNode call = Truffle.getRuntime().createDirectCallNode(method.getCallTarget());
    return new BoundSelfSendNode(selector, arguments, call, assumption).initialize(coord);
  }

  public static AbstractMessageSendNode createInlinedSelfSend(final SSymbol selector,
      final ExpressionNode[] arguments, final PreevaluatedExpression expr,
      final Assumption assumption, final long coord) {
    return new InlinedSelfSendNode(selector, arguments, expr, assumption).initialize(coord);
  }

  public static final class InlinedSelfSendNode extends AbstractMessageSendNode {
    private final SSymbol    selector;
    private final Assumption stillValid;

    @Child private ExpressionNode expr;

    private InlinedSelfSendNode(final SSymbol selector, final ExpressionNode[] arguments,
        final PreevaluatedExpression expr, final Assumption stillValid) {
      super(selector.getNumberOfSignatureArguments(), arguments);
      this.selector = selector;
      this.expr = (ExpressionNode) expr;
      this.stillValid = stillValid;
    }

    @Override
    public Object doPreEvaluated(final VirtualFrame frame, final Object[] arguments) {
      if (!stillValid.isValid()) {
        CompilerDirectives.transferToInterpreterAndInvalidate();
        AbstractDispatchNode dispatch = new UninitializedDispatchNode(selector);
        GenericMessageSendNode send =
            new GenericMessageSendNode(selector, argumentNodes, dispatch).initialize(sourceCoord);
        replace(send);
        dispatch.notifyAsInserted();
        return send.doPreEvaluated(frame, arguments);
      }
      return expr.doPreEvaluated(frame, arguments);
    }

    @Override
    public String getInvocationIdentifier() {
      return selector.getString();
    }

    @Override
    public String toString() {
      return "InlinedSelfSend(" + selector.getString() + ")";
    }
  }

  public static final class BoundSelfSendNode extends AbstractMessageSendNode {
    private final SSymbol    selector;
    private final Assumption stillValid;

    @Child private DirectCallNode target;

    private BoundSelfSendNode(final SSymbol selector, final ExpressionNode[] arguments,
        final DirectCallNode target, final Assumption stillValid) {
      super(selector.getNumberOfSignatureArguments(), arguments);
      this.selector = selector;
      this.target = target;
      this.stillValid = stillValid;
    }

    @Override
    public Object doPreEvaluated(final VirtualFrame frame, final Object[] arguments) {
      if (!stillValid.isValid()) {
        CompilerDirectives.transferToInterpreterAndInvalidate();
        AbstractDispatchNode dispatch = new UninitializedDispatchNode(selector);
        GenericMessageSendNode send =
            new GenericMessageSendNode(selector, argumentNodes, dispatch).initialize(sourceCoord);
        replace(send);
        dispatch.notifyAsInserted();
        return send.doPreEvaluated(frame, arguments);
      }
      return target.call(arguments);
    }

    @Override
    public String getInvocationIdentifier() {
      return selector.getString();
    }

    @Override
    public String toString() {
      return "BoundSelfSend(" + selector.getString() + ")";
    }
  }

  public static AbstractMessageSendNode createSuperSend(final SClass superClass,
      final SSymbol selector, final ExpressionNode[] arguments, final long coord) {
    SInvokable method = superClass.lookupInvokable(selector);

    if (method == null) {
      throw new NotYetImplementedException(
          "Currently #dnu with super sent is not yet implemented. ");
    }

    if (VmSettings.UseBdslInterp) {
      return new BdslSuperSendNode(selector, arguments, method).initialize(coord);
    }

    PreevaluatedExpression node = method.copyTrivialNode();
    if (node != null) {
      return new SuperExprNode(selector, arguments, node).initialize(coord);
    }

    DirectCallNode superMethodNode = Truffle.getRuntime().createDirectCallNode(
        method.getCallTarget());

    return new SuperSendNode(selector, arguments, superMethodNode).initialize(coord);
  }

  /**
   * A parse-time placeholder for a super send, used only by the Bytecode DSL translator, which
   * reads the resolved method off it. It is never executed.
   */
  public static final class BdslSuperSendNode extends AbstractMessageSendNode {
    private final SSymbol    selector;
    private final SInvokable method;

    private BdslSuperSendNode(final SSymbol selector, final ExpressionNode[] arguments,
        final SInvokable method) {
      super(selector.getNumberOfSignatureArguments(), arguments);
      this.selector = selector;
      this.method = method;
    }

    public SInvokable getMethod() {
      return method;
    }

    @Override
    public Object doPreEvaluated(final VirtualFrame frame, final Object[] arguments) {
      throw new NotYetImplementedException();
    }

    @Override
    public String getInvocationIdentifier() {
      return selector.getString();
    }
  }

  public static final class SuperSendNode extends AbstractMessageSendNode {
    private final SSymbol selector;

    @Child private DirectCallNode cachedSuperMethod;

    private SuperSendNode(final SSymbol selector, final ExpressionNode[] arguments,
        final DirectCallNode superMethod) {
      super(selector.getNumberOfSignatureArguments(), arguments);
      this.selector = selector;
      this.cachedSuperMethod = superMethod;
    }

    @Override
    public Object doPreEvaluated(final VirtualFrame frame,
        final Object[] arguments) {
      return cachedSuperMethod.call(arguments);
    }

    @Override
    public String getInvocationIdentifier() {
      return selector.getString();
    }

    @Override
    public String toString() {
      return "SuperSend(" + selector.getString() + ")";
    }
  }

  private static final class SuperExprNode extends AbstractMessageSendNode {
    private final SSymbol selector;

    @Child private ExpressionNode expr;

    private SuperExprNode(final SSymbol selector, final ExpressionNode[] arguments,
        final PreevaluatedExpression expr) {
      super(selector.getNumberOfSignatureArguments(), arguments);
      this.selector = selector;
      this.expr = (ExpressionNode) expr;
    }

    @Override
    public Object doPreEvaluated(final VirtualFrame frame,
        final Object[] arguments) {
      return expr.doPreEvaluated(frame, arguments);
    }

    @Override
    public String getInvocationIdentifier() {
      return selector.getString();
    }

    @Override
    public String toString() {
      return "SendExpr(" + selector.getString() + ")";
    }
  }
}
