package som.interpreter.nodes.specialized;

import som.interpreter.nodes.messages.BinarySendNode;
import som.vmobjects.SAbstractObject;
import som.vmobjects.SBlock;
import som.vmobjects.SMethod;
import som.vmobjects.SObject;

import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;


public abstract class IfFalseMessageNode extends BinarySendNode  {
  public IfFalseMessageNode(final BinarySendNode node) { super(node); }
  public IfFalseMessageNode(final IfFalseMessageNode node) { super(node); }

  /**
   * This is the case were we got a block as the argument. Need to actually
   * evaluate it.
   */
  @Specialization(order = 1)
  public SAbstractObject doIfFalse(final VirtualFrame frame,
      final boolean receiver, final SBlock argument) {
    if (!receiver) {
      SMethod blockMethod = argument.getMethod();
      SBlock b = universe.newBlock(blockMethod, frame.materialize(), 1);
      return blockMethod.invoke(frame.pack(), b, noArgs);
    } else {
      return universe.nilObject;
    }
  }

  @Specialization(guards = "isBooleanReceiver", order = 2)
  public SAbstractObject doIfFalse(final VirtualFrame frame,
      final SObject receiver, final SBlock argument) {
    // additional `not`/! because doIfFalse is implemented to take a boolean and check for false
    return doIfFalse(frame, !(receiver == universe.falseObject), argument);
  }

  /**
   * The argument in this case is an expression and can be returned directly.
   */
  @Specialization(order = 10)
  public SAbstractObject doIfFalse(final VirtualFrame frame,
      final boolean receiver, final SAbstractObject argument) {
    if (!receiver) {
      return argument;
    } else {
      return universe.nilObject;
    }
  }


  @Specialization(guards = "isBooleanReceiver", order = 11)
  public SAbstractObject doIfFalse(final VirtualFrame frame,
      final SObject receiver, final SAbstractObject argument) {
    return doIfFalse(frame, receiver == universe.falseObject, argument);
  }
}
