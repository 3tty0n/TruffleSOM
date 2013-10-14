package som.primitives;

import som.interpreter.nodes.PrimitiveNode;
import som.vm.Universe;
import som.vmobjects.SDouble;
import som.vmobjects.SInteger;
import som.vmobjects.SObject;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;


public abstract class DoublePrims extends PrimitiveNode {

  protected DoublePrims(final SSymbol selector, final Universe universe) {
    super(selector, universe);
  }

  protected SDouble coerceToDouble(final SObject o) {
    if (o instanceof SDouble) { return (SDouble) o; }
    if (o instanceof SInteger) {
      return universe.newDouble(((SInteger) o).getEmbeddedInteger());
    }
    throw new ClassCastException("Cannot coerce to Double!");
  }


  public abstract static class AsStringPrim extends PrimitiveNode {
    public AsStringPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SDouble self = (SDouble) receiver;
      return universe.newString(java.lang.Double.toString(
          self.getEmbeddedDouble()));
    }
  }

  public abstract static class DoubleDivPrim extends DoublePrims {
    public DoubleDivPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SDouble op1 = coerceToDouble(((SObject[]) arguments)[0]);
      SDouble op2 = (SDouble) receiver;
      return universe.newDouble(op2.getEmbeddedDouble()
          / op1.getEmbeddedDouble());
    }
  }

  public abstract static class ModPrim extends DoublePrims {
    public ModPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SDouble op1 = coerceToDouble(((SObject[]) arguments)[0]);
      SDouble op2 = (SDouble) receiver;
      return universe.newDouble(op2.getEmbeddedDouble()
          % op1.getEmbeddedDouble());
    }
  }

  public abstract static class EqualsPrim extends DoublePrims {
    public EqualsPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SDouble op1 = coerceToDouble(((SObject[]) arguments)[0]);
      SDouble op2 = (SDouble) receiver;
      if (op1.getEmbeddedDouble() == op2.getEmbeddedDouble()) {
        return universe.trueObject;
      } else {
        return universe.falseObject;
      }
    }
  }

  public abstract static class RoundPrim extends PrimitiveNode {
    public RoundPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SDouble rcvr = (SDouble) receiver;
      long result = Math.round(rcvr.getEmbeddedDouble());
      if (result > java.lang.Integer.MAX_VALUE
          || result < java.lang.Integer.MIN_VALUE) {
        return universe.newBigInteger(result);
      } else {
        return universe.newInteger((int) result);
      }
    }
  }
}
