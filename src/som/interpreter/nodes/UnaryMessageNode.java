package som.interpreter.nodes;

import som.interpreter.nodes.messages.UnaryMonomorphicNode;
import som.vm.Universe;
import som.vmobjects.SAbstractObject;
import som.vmobjects.SClass;
import som.vmobjects.SMethod;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.dsl.NodeChild;
import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;

@NodeChild(value = "receiver", type = ExpressionNode.class)
public abstract class UnaryMessageNode extends AbstractMessageNode {

  public UnaryMessageNode(final SSymbol selector, final Universe universe) {
    super(selector, universe);
  }

  public UnaryMessageNode(final UnaryMessageNode node) {
    this(node.selector, node.universe);
  }

  public abstract ExpressionNode getReceiver();
  public abstract Object executeEvaluated(final VirtualFrame frame, final Object receiver);

  // TODO: want to use @Generic here!
  @Specialization
  public Object doGeneric(final VirtualFrame frame, final Object rcvr) {
    CompilerDirectives.transferToInterpreter();

    SAbstractObject receiver = (SAbstractObject) rcvr;

    SClass rcvrClass = classOfReceiver(receiver, getReceiver());
    SMethod invokable = rcvrClass.lookupInvokable(selector);

    if (invokable != null) {
      UnaryMonomorphicNode node = NodeFactory.createUnaryMonomorphicNode(selector, universe, rcvrClass, invokable, getReceiver());
      return replace(node, "Be optimisitic and do a monomorphic lookup cache, or a primitive inline.").executeEvaluated(frame, receiver);
    } else {
      return doFullSend(frame, receiver, noArgs, rcvrClass);
    }
  }

  @Override
  public ExpressionNode cloneForInlining() {
    // TODO: test whether this is problematic
    return (ExpressionNode) this.copy();
    // return NodeFactory.createUnaryMessageNode(selector, universe, getReceiver());
  }
}
