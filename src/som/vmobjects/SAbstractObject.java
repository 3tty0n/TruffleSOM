package som.vmobjects;

import som.interpreter.SArguments;
import som.interpreter.Types;
import som.vm.Universe;

import com.oracle.truffle.api.CompilerAsserts;


public abstract class SAbstractObject {

  public abstract SClass getSOMClass();

  @Override
  public String toString() {
    CompilerAsserts.neverPartOfCompilation();
    SClass clazz = getSOMClass();
    if (clazz == null) {
      return "an Object(clazz==null)";
    }
    return "a " + clazz.getName().getString();
  }

  public static final Object send(
      final String selectorString,
      final Object[] arguments) {
    CompilerAsserts.neverPartOfCompilation("SAbstractObject.send()");
    SSymbol selector = Universe.current().symbolFor(selectorString);

    // Lookup the invokable
    SInvokable invokable = Types.getClassOf(arguments[0]).lookupInvokable(selector);

    return invokable.invoke(arguments);
  }

  public static final Object sendDoesNotUnderstand(final SSymbol selector,
      final Object[] arguments) {
    CompilerAsserts.neverPartOfCompilation("SAbstractObject.sendDNU()");
    assert arguments != null;

    // Allocate an array to hold the arguments, without receiver
    Object[] argumentsArray = SArguments.getArgumentsWithoutReceiver(arguments);
    Object[] args = new Object[] {arguments[0], selector, argumentsArray};
    return send("doesNotUnderstand:arguments:", args);
  }

  public static final Object sendUnknownGlobal(final Object receiver,
      final SSymbol globalName) {
    Object[] arguments = {receiver, globalName};
    return send("unknownGlobal:", arguments);
  }

  public static final Object sendEscapedBlock(final Object receiver,
      final SBlock block) {
    Object[] arguments = {receiver, block};
    return send("escapedBlock:", arguments);
  }

}
