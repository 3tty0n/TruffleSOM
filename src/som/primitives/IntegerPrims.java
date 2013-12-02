package som.primitives;

import som.interpreter.nodes.UnaryMessageNode;
import som.primitives.arithmetic.ArithmeticPrim;
import som.vm.Universe;
import som.vmobjects.SAbstractObject;
import som.vmobjects.SClass;
import som.vmobjects.SInteger;
import som.vmobjects.SString;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.dsl.Specialization;

public abstract class IntegerPrims {


  public abstract static class RandomPrim extends UnaryMessageNode {
    public RandomPrim(final SSymbol selector, final Universe universe) { super(selector, universe); }
    public RandomPrim(final RandomPrim prim) { this(prim.selector, prim.universe); }

    @Specialization
    public SAbstractObject doSInteger(final SInteger receiver) {
      return universe.newInteger((int) (receiver.getEmbeddedInteger() * Math.random()));
    }
  }

  public abstract static class FromStringPrim extends ArithmeticPrim {
    public FromStringPrim(final SSymbol selector, final Universe universe) { super(selector, universe); }
    public FromStringPrim(final FromStringPrim prim) { this(prim.selector, prim.universe); }

    protected boolean receiverIsIntegerClass(final SClass receiver) {
      return receiver == universe.integerClass;
    }

    @Specialization(guards = "receiverIsIntegerClass")
    public SAbstractObject doSClass(final SClass receiver, final SString argument) {
      long result = Long.parseLong(argument.getEmbeddedString());
      return makeInt(result);
    }
  }
}
