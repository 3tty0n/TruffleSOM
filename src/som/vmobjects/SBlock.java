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

import com.oracle.truffle.api.frame.MaterializedFrame;
import com.oracle.truffle.api.frame.PackedFrame;

public class SBlock extends SObject {

  private MaterializedFrame declarationFrame;

  public SBlock(final SObject nilObject, final SMethod blockMethod,
      final MaterializedFrame context) {
    super(nilObject);
    setMethod(blockMethod);
    setContext(context);
  }

  public SMethod getMethod() {
    // Get the method of this block by reading the field with method index
    return (SMethod) getField(methodIndex);
  }

  private void setMethod(final SMethod value) {
    // Set the method of this block by writing to the field with method
    // index
    setField(methodIndex, value);
  }

  public MaterializedFrame getContext() {
    // Get the context of this block by reading the field with context index
    return declarationFrame;
  }

  private void setContext(final MaterializedFrame value) {
    if (declarationFrame != null) {
      throw new IllegalStateException("This is most likely a bug, "
          + "the block's context should not change.");
    }
    declarationFrame = value;
  }

  @Override
  public int getDefaultNumberOfFields() {
    // Return the default number of fields for a block
    return numberOfBlockFields;
  }

  public static SPrimitive getEvaluationPrimitive(final int numberOfArguments,
      final Universe universe) {
    return new Evaluation(numberOfArguments, universe);
  }

  public static class Evaluation extends SPrimitive {

    public Evaluation(final int numberOfArguments, final Universe universe) {
      super(computeSignatureString(numberOfArguments), universe);
    }

    @Override
    public SObject invoke(final PackedFrame frame, final SObject selfO, final SObject[] args) {
      // Get the block (the receiver)
      SBlock self = (SBlock) selfO;
      return self.getMethod().invoke(frame, selfO, args);
    }

    private static java.lang.String computeSignatureString(final int numberOfArguments) {
      // Compute the signature string
      java.lang.String signatureString = "value";
      if (numberOfArguments > 1) { signatureString += ":"; }

      // Add extra value: selector elements if necessary
      for (int i = 2; i < numberOfArguments; i++) {
        signatureString += "with:";
      }

      // Return the signature string
      return signatureString;
    }
  }

  // Static field indices and number of block fields
  static final int methodIndex         = numberOfObjectFields;
  static final int contextIndex        = 1 + methodIndex;
  static final int numberOfBlockFields = 1 + contextIndex;
}
