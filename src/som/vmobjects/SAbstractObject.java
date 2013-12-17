package som.vmobjects;

import som.vm.Universe;

import com.oracle.truffle.api.frame.PackedFrame;


public abstract class SAbstractObject {

  public abstract SClass getSOMClass(final Universe universe);

  @Override
  public String toString() {
    return "a " + getSOMClass(Universe.current()).getName().getString();
  }

  public Object send(final String selectorString,
      final SAbstractObject[] arguments,
      final Universe universe, final PackedFrame frame) {
    // Turn the selector string into a selector
    SSymbol selector = universe.symbolFor(selectorString);

    // Lookup the invokable
    SMethod invokable = getSOMClass(universe).lookupInvokable(selector);

    // Invoke the invokable
    return invokable.invoke(frame, this, arguments);
  }

  public Object sendDoesNotUnderstand(final SSymbol selector,
      final SAbstractObject[] arguments,
      final Universe universe,
      final PackedFrame frame) {
    // Allocate an array with enough room to hold all arguments
    int numArgs = (arguments == null) ? 0 : arguments.length;

    SArray argumentsArray = universe.newArray(numArgs);
    for (int i = 0; i < numArgs; i++) {
      argumentsArray.setIndexableField(i, arguments[i]);
    }

    SAbstractObject[] args = new SAbstractObject[] {selector, argumentsArray};

    return send("doesNotUnderstand:arguments:", args, universe, frame);
  }

  public Object sendUnknownGlobal(final SSymbol globalName,
      final Universe universe,
      final PackedFrame frame) {
    SAbstractObject[] arguments = {globalName};
    return send("unknownGlobal:", arguments, universe, frame);
  }

  public Object sendEscapedBlock(final SBlock block,
      final Universe universe,
      final PackedFrame frame) {
    SAbstractObject[] arguments = {block};
    return send("escapedBlock:", arguments, universe, frame);
  }

}
