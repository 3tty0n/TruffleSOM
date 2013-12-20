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

package som.compiler;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;

import som.vm.Universe;
import som.vmobjects.SClass;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.CompilerDirectives.SlowPath;

public class SourcecodeCompiler {

  private Parser parser;

  public static class Source implements com.oracle.truffle.api.Source {

    private final String filename;
    private final String code;

    public Source(final String filename) throws IOException {
      this.filename = filename;
      this.code = read(filename);
    }

    @Override
    public String getName() {
      return filename;
    }

    @Override
    public String getCode() {
      return code;
    }

    private String read(final String filename) throws IOException {
      byte[] encoded = Files.readAllBytes(Paths.get(filename));
      return Charset.forName("US-ASCII").decode(ByteBuffer.wrap(encoded)).toString();
    }
  }

  @SlowPath
  public static SClass compileClass(final String path, final String file,
      final SClass systemClass, final Universe universe)
      throws IOException {
    return new SourcecodeCompiler().compile(path, file, systemClass, universe);
  }

  @SlowPath
  public static SClass compileClass(final String stmt,
      final SClass systemClass, final Universe universe) {
    return new SourcecodeCompiler().compileClassString(stmt, systemClass,
        universe);
  }

  @SlowPath
  private SClass compile(final String path, final String file,
      final SClass systemClass, final Universe universe)
      throws IOException {
    SClass result = systemClass;

    String fname = path + File.separator + file + ".som";

    parser = new Parser(new FileReader(fname), new Source(fname), universe);

    result = compile(systemClass, universe);

    SSymbol cname = result.getName();
    String cnameC = cname.getString();

    if (file != cnameC) {
      throw new IllegalStateException("File name " + file
          + " does not match class name " + cnameC);
    }

    return result;
  }

  private SClass compileClassString(final String stream,
      final SClass systemClass, final Universe universe) {
    parser = new Parser(new StringReader(stream), null, universe);

    SClass result = compile(systemClass, universe);
    return result;
  }

  private SClass compile(final SClass systemClass,
      final Universe universe) {
    ClassGenerationContext cgc = new ClassGenerationContext(universe);

    SClass result = systemClass;
    parser.classdef(cgc);

    if (systemClass == null) {
      result = cgc.assemble();
    } else {
      cgc.assembleSystemClass(result);
    }

    return result;
  }

}
