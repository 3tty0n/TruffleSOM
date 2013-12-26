package som.interpreter.nodes.specialized;

import som.interpreter.nodes.BinaryMessageNode;
import som.vmobjects.SBlock;
import som.vmobjects.SObject;

import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;

public abstract class WhileFalseMessageNode extends AbstractWhileMessageNode {
  public WhileFalseMessageNode(final BinaryMessageNode node, final Object rcvr,
      final Object arg) { super(node, rcvr, arg); }
  public WhileFalseMessageNode(final WhileFalseMessageNode node) { super(node); }

  @Specialization(guards = "isSameArgument")
  public SObject doWhileTrue(final VirtualFrame frame,
      final SBlock loopCondition, final SBlock loopBody) {
    return doWhile(frame, loopCondition, loopBody, universe.falseObject);
  }

  @Specialization(guards = {"receiverIsFalseObject", "isSameArgument"})
  public SObject doWhileFalse(final VirtualFrame frame,
      final Object loopCondition, final SBlock loopBody) {
    return doWhile(frame, loopCondition, loopBody);
  }
}
