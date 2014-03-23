package som.primitives;

import som.interpreter.nodes.nary.UnaryExpressionNode.UnarySideEffectFreeExpressionNode;
import som.vmobjects.SArray;
import som.vmobjects.SObject;

import com.oracle.truffle.api.dsl.Specialization;

public abstract class ObjectSizePrim extends UnarySideEffectFreeExpressionNode {
  @Specialization
  public final int doSArray(final SArray receiver) {
    int size = 0;
    size += receiver.getNumberOfIndexableFields();
    return size;
  }

  @Specialization
  public final int doSObject(final SObject receiver) {
    int size = 0;
    size += receiver.getNumberOfFields();
    return size;
  }

  @Specialization
  public final int doSAbstractObject(final Object receiver) {
    return 0; // TODO: allow polymorphism?
  }
}
