package som.interpreter.nodes.messages;

import som.interpreter.Arguments;
import som.interpreter.Invokable;
import som.interpreter.nodes.BinaryMessageNode;
import som.interpreter.nodes.ExpressionNode;
import som.vm.Universe;
import som.vmobjects.SAbstractObject;
import som.vmobjects.SClass;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.CallTarget;
import com.oracle.truffle.api.CompilerAsserts;
import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.impl.DefaultCallTarget;
import com.oracle.truffle.api.nodes.FrameFactory;
import com.oracle.truffle.api.nodes.InlinableCallSite;
import com.oracle.truffle.api.nodes.Node;


public abstract class BinarySendNode extends BinaryMessageNode {

  @Child    protected ExpressionNode   receiverExpr;
  @Children protected ExpressionNode[] argumentsNodes;

  private BinarySendNode(final SSymbol selector,
      final Universe universe, final ExpressionNode receiver,
      final ExpressionNode[] arguments) {
    super(selector, universe);
    this.receiverExpr   = adoptChild(receiver);
    this.argumentsNodes = adoptChildren(arguments);
  }

  private BinarySendNode(final BinarySendNode node) {
    this(node.selector, node.universe, node.receiverExpr, node.argumentsNodes);
  }

  @Override
  public ExpressionNode getReceiver() {
    return receiverExpr;
  }

  @Override
  public ExpressionNode[] getArguments() {
    return argumentsNodes;
  }

  @Override
  public final Object executeGeneric(final VirtualFrame frame) {
    Object receiverValue = receiverExpr.executeGeneric(frame);
    Object argument = argumentsNodes[0].executeGeneric(frame);
    return executeEvaluated(frame, receiverValue, argument);
  }

  @Override
  public ExpressionNode cloneForInlining() {
    return create(selector, universe, receiverExpr, argumentsNodes);
  }

  public static BinarySendNode create(final SSymbol selector,
      final Universe universe, final ExpressionNode receiver,
      final ExpressionNode[] arguments) {
    return new UninitializedSendNode(selector, universe, receiver, arguments, 0);
  }

  private static final class CachedSendNode extends BinarySendNode {

    @Child protected BinarySendNode    nextNode;
    @Child protected BinaryMessageNode currentNode;
           private final SClass        cachedRcvrClass;

    CachedSendNode(final BinarySendNode node,
        final BinarySendNode next, final BinaryMessageNode current,
        final SClass rcvrClass) {
      super(node);
      this.nextNode        = adoptChild(next);
      this.currentNode     = adoptChild(current);
      this.cachedRcvrClass = rcvrClass;
    }

    @Override
    public Object executeEvaluated(final VirtualFrame frame,
        final Object receiver, final Object argument) {
      if (cachedRcvrClass == classOfReceiver(receiver)) {
        return currentNode.executeEvaluated(frame, receiver, argument);
      } else {
        return nextNode.executeEvaluated(frame, receiver, argument);
      }
    }

    @Override
    public ExpressionNode cloneForInlining() {
      throw new RuntimeException("This node should not be asked for inlining infos, I think. Because it is in a chain, and only the most general of these nodes is probably to be inlined so that it can specialize separately.");
    }
  }

  private static final class UninitializedSendNode extends BinarySendNode {

    protected final int depth;

    UninitializedSendNode(final SSymbol selector, final Universe universe,
        final ExpressionNode receiver, final ExpressionNode[] arguments,
        final int depth) {
      super(selector, universe, receiver, arguments);
      this.depth = depth;
    }

    UninitializedSendNode(final BinarySendNode node, final int depth) {
      super(node);
      this.depth = depth;
    }

    UninitializedSendNode(final UninitializedSendNode node) {
      this(node, node.depth);
    }

    @Override
    public Object executeEvaluated(final VirtualFrame frame, final Object receiver,
        final Object argument) {
      CompilerDirectives.transferToInterpreter();
      return specialize(receiver).executeEvaluated(frame, receiver, argument);
    }

    // DUPLICATED but types
    private BinarySendNode specialize(final Object receiver) {
      CompilerAsserts.neverPartOfCompilation();

      if (depth < INLINE_CACHE_SIZE) {
        CallTarget  callTarget = lookupCallTarget(receiver);
        BinaryMessageNode current = (BinaryMessageNode) createCachedNode(callTarget);
        BinarySendNode       next = new UninitializedSendNode(this);
        return replace(new CachedSendNode(this, next, current, classOfReceiver(receiver)));
      } else {
        BinarySendNode topMost = (BinarySendNode) getTopNode();
        return topMost.replace(new GenericSendNode(this));
      }
    }

    // DUPLICATED
    protected Node getTopNode() {
      Node parentNode = this;
      for (int i = 0; i < depth; i++) {
        parentNode = parentNode.getParent();
      }
      return parentNode;
    }

    // DUPLICATED but types
    protected ExpressionNode createCachedNode(final CallTarget callTarget) {
      if (!(callTarget instanceof DefaultCallTarget)) {
        throw new RuntimeException("This should not happen in TruffleSOM");
      }

      DefaultCallTarget ct = (DefaultCallTarget) callTarget;
      Invokable invokable = (Invokable) ct.getRootNode();
      if (invokable.isAlwaysToBeInlined()) {
        return invokable.methodCloneForInlining();
      } else {
        return new InlinableSendNode(this, ct);
      }
    }
  }

  private static final class InlinableSendNode extends BinarySendNode
    implements InlinableCallSite {

    private final DefaultCallTarget inlinableCallTarget;

    @CompilationFinal private int callCount;

    InlinableSendNode(final BinarySendNode node, final DefaultCallTarget callTarget) {
      super(node);
      this.inlinableCallTarget = callTarget;
      callCount = 0;
    }

    @Override
    public int getCallCount() {
      return callCount;
    }

    @Override
    public void resetCallCount() {
      callCount = 0;
    }

    @Override
    public Node getInlineTree() {
      Invokable root = (Invokable) inlinableCallTarget.getRootNode();
      return root.methodCloneForInlining();
    }

    @Override
    public boolean inline(final FrameFactory factory) {
      CompilerAsserts.neverPartOfCompilation();

      ExpressionNode method = null;
      Invokable invokable = (Invokable) inlinableCallTarget.getRootNode();
      method = invokable.methodCloneForInlining();
      if (method != null) {
        replace(method);
        return true;
      } else {
        return false;
      }
    }

    @Override
    public CallTarget getCallTarget() {
      return inlinableCallTarget;
    }

    @Override
    public Object executeEvaluated(final VirtualFrame frame,
        final Object receiver, final Object argument) {
      if (CompilerDirectives.inInterpreter()) {
        callCount++;
      }

      Arguments args = new Arguments((SAbstractObject) receiver,
          new SAbstractObject[] {(SAbstractObject) argument});
      return inlinableCallTarget.call(frame.pack(), args);
    }

    @Override
    public ExpressionNode cloneForInlining() {
      throw new RuntimeException("This node should not be asked for inlining infos, I think. Because it is in a chain, and only the most general of these nodes is probably to be inlined so that it can specialize separately.");
    }
  }

  private static final class GenericSendNode extends BinarySendNode {
    GenericSendNode(final BinarySendNode node) {
      super(node);
    }

    @Override
    public Object executeEvaluated(final VirtualFrame frame, final Object receiver, final Object argument) {
      CallTarget callTarget = lookupCallTarget(receiver);
      Arguments args = new Arguments((SAbstractObject) receiver,
          new SAbstractObject[] {(SAbstractObject) argument});
      return callTarget.call(args);
    }
  }
}
