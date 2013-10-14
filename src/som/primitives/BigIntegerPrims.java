package som.primitives;

import som.interpreter.nodes.PrimitiveNode;
import som.vm.Universe;
import som.vmobjects.SBigInteger;
import som.vmobjects.SInteger;
import som.vmobjects.SObject;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.dsl.Specialization;
import com.oracle.truffle.api.frame.VirtualFrame;


public class BigIntegerPrims {

  public abstract static class AsStringPrim extends PrimitiveNode {
    public AsStringPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SBigInteger self = (SBigInteger) receiver;
      return universe.newString(self.getEmbeddedBiginteger().toString());
    }
  }

  public abstract static class SqrtPrim extends PrimitiveNode {
    public SqrtPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SBigInteger self = (SBigInteger) receiver;
      return universe.newDouble(Math.sqrt(
          self.getEmbeddedBiginteger().doubleValue()));
    }
  }

  public abstract static class DividePrim extends PrimitiveNode {
    public DividePrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SObject rightObj = ((SObject[]) arguments)[0];
      SBigInteger right = null;
      SBigInteger left = (SBigInteger) receiver;

      // Check second parameter type:
      if (rightObj instanceof SInteger) {
        // Second operand was Integer
        right = universe.newBigInteger(
            ((SInteger) rightObj).getEmbeddedInteger());
      } else {
        right = (SBigInteger) rightObj;
      }

      // Do operation and perform conversion to Integer if required
      java.math.BigInteger result = left.getEmbeddedBiginteger().divide(
          right.getEmbeddedBiginteger());
      if (result.bitLength() > 31) {
        return universe.newBigInteger(result);
      } else {
        return universe.newInteger(result.intValue());
      }
    }
  }


  public abstract static class ModPrim extends PrimitiveNode {
    public ModPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SObject rightObj = ((SObject[]) arguments)[0];
      SBigInteger right = null;
      SBigInteger left = (SBigInteger) receiver;

      // Check second parameter type:
      if (rightObj instanceof SInteger) {
        // Second operand was Integer
        right = universe.newBigInteger(
            ((SInteger) rightObj).getEmbeddedInteger());
      } else {
        right = (SBigInteger) rightObj;
      }

      // Do operation:
      return universe.newBigInteger(left.getEmbeddedBiginteger().mod(
          right.getEmbeddedBiginteger()));
    }
  }


  public abstract static class AndPrim extends PrimitiveNode {
    public AndPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SObject rightObj = ((SObject[]) arguments)[0];
      SBigInteger right = null;
      SBigInteger left = (SBigInteger) receiver;

      // Check second parameter type:
      if (rightObj instanceof SInteger) {
        // Second operand was Integer
        right = universe.newBigInteger(
            ((SInteger) rightObj).getEmbeddedInteger());
      } else {
        right = (SBigInteger) rightObj;
      }

      // Do operation:
      return universe.newBigInteger(left.getEmbeddedBiginteger().and(
          right.getEmbeddedBiginteger()));
    }
  }


  public abstract static class EqualsPrim extends PrimitiveNode {
    public EqualsPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SObject rightObj = ((SObject[]) arguments)[0];
      SBigInteger right = null;
      SBigInteger left = (SBigInteger) receiver;

      // Check second parameter type:
      if (rightObj instanceof SInteger) {
        // Second operand was Integer
        right = universe.newBigInteger(
            ((SInteger) rightObj).getEmbeddedInteger());
      } else {
        right = (SBigInteger) rightObj;
      }

      // Do operation:
      if (left.getEmbeddedBiginteger().compareTo(
          right.getEmbeddedBiginteger()) == 0) {
        return universe.trueObject;
      } else {
        return universe.falseObject;
      }
    }
  }


  public abstract static class LessThanPrim extends PrimitiveNode {
    public LessThanPrim(final SSymbol selector, final Universe universe) {
      super(selector, universe);
    }

    @Specialization
    public SObject doGeneric(final VirtualFrame frame,
        final SObject receiver, final Object arguments) {
      SObject rightObj = ((SObject[]) arguments)[0];
      SBigInteger right = null;
      SBigInteger left = (SBigInteger) receiver;

      // Check second parameter type:
      if (rightObj instanceof SInteger) {
        // Second operand was Integer
        right = universe.newBigInteger(
            ((SInteger) rightObj).getEmbeddedInteger());
      } else {
        right = (SBigInteger) rightObj;
      }

      // Do operation:
      if (left.getEmbeddedBiginteger().compareTo(
          right.getEmbeddedBiginteger()) < 0) {
        return universe.trueObject;
      } else {
        return universe.falseObject;
      }
    }
  }
}
