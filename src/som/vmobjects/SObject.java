/**
 * Copyright (c) 2009 Michael Haupt, michael.haupt@hpi.uni-potsdam.de
 * Software Architecture Group, Hasso Plattner Institute, Potsdam, Germany
 * http://www.hpi.uni-potsdam.de/swa/
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package som.vmobjects;

import som.vm.Universe;

import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.nodes.ExplodeLoop;

public class SObject extends SAbstractObject {

  public SObject() {
    fields = noFields;
  }

  protected SObject(final int numberOfFields, final SObject nilObject) {
    fields = setClearFields(numberOfFields, nilObject);
  }

  public SObject(final SClass instanceClass, final SObject nilObject) {
    clazz  = instanceClass;
    fields = setClearFields(instanceClass.getNumberOfInstanceFields(), nilObject);
  }

  @Override
  public SClass getSOMClass(final Universe universe) {
    // Get the class of this object by reading the field with class index
    return clazz;
  }

  public void setClass(final SClass value) {
    CompilerDirectives.transferToInterpreterAndInvalidate();
    // Set the class of this object by writing to the field with class index
    clazz = value;
  }

  public int getNumberOfFields() {
    // Get the number of fields in this object
    return fields.length;
  }

  @ExplodeLoop
  private SAbstractObject[] setClearFields(final int numberOfFields, final SObject nilObject) {
    if (numberOfFields == 0) { return noFields; }

    // Clear each and every field by putting nil into them
    SAbstractObject[] fieldArr = new SAbstractObject[numberOfFields];
    for (int i = 0; i < fieldArr.length; i++) {
      fieldArr[i] = nilObject;
    }
    return fieldArr;
  }

  public SAbstractObject getField(final int index) {
    // Get the field with the given index
    return fields[index];
  }

  public void setField(final int index, final SAbstractObject value) {
    // Set the field with the given index to the given value
    fields[index] = value;
  }


  // Private array of fields
  private final SAbstractObject[]  fields;
  @CompilationFinal private SClass clazz;

  private static final SAbstractObject[] noFields = new SAbstractObject[0];

  // Static field indices and number of object fields
  static final int numberOfObjectFields = 0;
}
