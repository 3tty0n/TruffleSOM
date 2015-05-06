package som.interpreter;

import som.compiler.MethodGenerationContext;
import som.compiler.Variable.Local;
import som.interpreter.nodes.ExpressionNode;
import som.interpreter.nodes.SOMNode;
import som.interpreter.nodes.UninitializedVariableNode.UninitializedVariableReadNode;
import som.interpreter.nodes.UninitializedVariableNode.UninitializedVariableWriteNode;

import com.oracle.truffle.api.frame.FrameSlot;
import com.oracle.truffle.api.nodes.Node;
import com.oracle.truffle.api.nodes.NodeUtil;
import com.oracle.truffle.api.nodes.NodeVisitor;
import com.oracle.truffle.api.source.SourceSection;


public class InlinerForLexicallyEmbeddedMethods implements NodeVisitor {

  public static ExpressionNode doInline(
      final ExpressionNode body, final MethodGenerationContext mgenc,
      final int blockStartIdx) {
    ExpressionNode inlinedBody = NodeUtil.cloneNode(body);

    return NodeVisitorUtil.applyVisitor(inlinedBody,
        new InlinerForLexicallyEmbeddedMethods(mgenc, blockStartIdx));
  }

  private final MethodGenerationContext mgenc;
  private final int blockStartIdx;

  public InlinerForLexicallyEmbeddedMethods(final MethodGenerationContext mgenc,
      final int blockStartIdx) {
    this.mgenc = mgenc;
    this.blockStartIdx = blockStartIdx;
  }

  @Override
  public boolean visit(final Node node) {
    if (node instanceof SOMNode) {
      ((SOMNode) node).replaceWithLexicallyEmbeddedNode(this);
    }
    return true;
  }

  public UninitializedVariableReadNode getLocalRead(final Object slotIdentifier, final SourceSection source) {
    String inlinedId = getEmbeddedSlotId(slotIdentifier);
    mgenc.addLocalIfAbsent(inlinedId);
    return (UninitializedVariableReadNode) mgenc.getLocalReadNode(inlinedId, source);
  }

  private String getEmbeddedSlotId(final Object slotIdentifier) {
    String id = (String) slotIdentifier;
    String inlinedId = id + ":" + blockStartIdx;
    return inlinedId;
  }

  public FrameSlot getLocalSlot(final Object orgSlotId) {
    String id = getEmbeddedSlotId(orgSlotId);
    Local var = mgenc.getEmbeddedLocal(id);
    return var.getSlot();
  }

  public UninitializedVariableWriteNode getLocalWrite(final Object slotIdentifier,
      final ExpressionNode valExp,
      final SourceSection source) {
    String inlinedId = getEmbeddedSlotId(slotIdentifier);
    mgenc.addLocalIfAbsent(inlinedId);
    return (UninitializedVariableWriteNode) mgenc.getLocalWriteNode(inlinedId,
        valExp, source);
  }

  public LexicalContext getOuterContext() {
    return mgenc.getLexicalContext();
  }
}
