/**
 * Copyright (c) 2013 Stefan Marr, stefan.marr@vub.ac.be
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
package som.interpreter;

import som.vmobjects.SAbstractObject;

import com.oracle.truffle.api.CompilerDirectives.CompilationFinal;
import com.oracle.truffle.api.frame.VirtualFrame;

public abstract class Arguments extends com.oracle.truffle.api.Arguments {

  private final SAbstractObject self;

  private Arguments(final SAbstractObject self) {
    this.self = self;
  }

  public SAbstractObject getSelf() {
    return self;
  }

  public abstract SAbstractObject getArgument(final int i);

  public static Arguments get(final VirtualFrame frame) {
    return frame.getArguments(Arguments.class);
  }

//  public static Arguments getUnary(final VirtualFrame frame) {
//    return frame.getArguments(UnaryArguments.class);
//  }
//
//  public static Arguments getBinary(final VirtualFrame frame) {
//    return frame.getArguments(BinaryArguments.class);
//  }
//
//  public static Arguments getTernary(final VirtualFrame frame) {
//    return frame.getArguments(TernaryArguments.class);
//  }
//
//  public static Arguments getKeyword(final VirtualFrame frame) {
//    return frame.getArguments(KeywordArguments.class);
//  }

  public static final class UnaryArguments extends Arguments {
    public UnaryArguments(final SAbstractObject self) {
      super(self);
    }

    @Override
    public SAbstractObject getArgument(final int i) {
      return null;
    }
  }

  public static final class BinaryArguments extends Arguments {
    private final SAbstractObject arg;
    public BinaryArguments(final SAbstractObject self, final SAbstractObject arg) {
      super(self);
      this.arg = arg;
    }

    @Override
    public SAbstractObject getArgument(final int i) {
      assert i == 0;
      return arg;
    }
  }

  public static final class TernaryArguments extends Arguments {
    private final SAbstractObject arg1;
    private final SAbstractObject arg2;

    public TernaryArguments(final SAbstractObject self,
        final SAbstractObject arg1,
        final SAbstractObject arg2) {
      super(self);
      this.arg1 = arg1;
      this.arg2 = arg2;
    }

    @Override
    public SAbstractObject getArgument(final int i) {
      if (i == 0) {
        return arg1;
      } else {
        assert i == 1;
        return arg2;
      }
    }
  }

  public static final class KeywordArguments extends Arguments {
    @CompilationFinal
    private final SAbstractObject[] arguments;

    public KeywordArguments(final SAbstractObject self, final SAbstractObject[] arguments) {
      super(self);
      this.arguments = arguments;
    }

    @Override
    public SAbstractObject getArgument(final int i) {
      return arguments[i];
    }
  }
}
