package som.primitives;

import som.interpreter.nodes.nary.UnaryExpressionNode.UnarySideEffectFreeExpressionNode;

import com.oracle.truffle.api.dsl.Specialization;

public abstract class LengthPrim extends UnarySideEffectFreeExpressionNode {
  @Specialization
  public final int doSArray(final Object[] receiver) {
    return receiver.length;
  }

  @Specialization
  public final int doSString(final String receiver) {
    return receiver.length();
  }
}
