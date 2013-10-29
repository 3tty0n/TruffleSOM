package som.primitives;

import som.interpreter.nodes.PrimitiveNode;
import som.vm.Universe;
import som.vmobjects.SAbstractObject;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;


public abstract class AsStringPrim extends PrimitiveNode {
  public AsStringPrim(final SSymbol selector, final Universe universe) {
    super(selector, universe);
  }

  @Specialization
  public SAbstractObject doGeneric(final VirtualFrame frame,
      final SAbstractObject receiver, final Object arguments) {
    SSymbol self = (SSymbol) receiver;
    return universe.newString(self.getString());
  }
}
