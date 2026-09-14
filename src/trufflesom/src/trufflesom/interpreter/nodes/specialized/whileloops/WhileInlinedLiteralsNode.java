package trufflesom.interpreter.nodes.specialized.whileloops;

import com.oracle.truffle.api.CompilerAsserts;
import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.Truffle;
import com.oracle.truffle.api.dsl.UnsupportedSpecializationException;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.LoopNode;
import com.oracle.truffle.api.nodes.Node;
import com.oracle.truffle.api.nodes.RepeatingNode;
import com.oracle.truffle.api.nodes.RootNode;
import com.oracle.truffle.api.nodes.UnexpectedResultException;

import trufflesom.bdt.inlining.Inline;
import trufflesom.bdt.inlining.Inline.False;
import trufflesom.bdt.inlining.Inline.True;
import trufflesom.interpreter.Invokable;
import trufflesom.interpreter.nodes.ExpressionNode;
import trufflesom.interpreter.nodes.NoPreEvalExprNode;
import trufflesom.vm.constants.Nil;


@Inline(selector = "whileTrue:", inlineableArgIdx = {0, 1}, additionalArgs = True.class)
@Inline(selector = "whileFalse:", inlineableArgIdx = {0, 1}, additionalArgs = False.class)
public final class WhileInlinedLiteralsNode extends NoPreEvalExprNode {

  @Child private LoopNode loopNode;

  private final boolean expectedBool;

  @SuppressWarnings("unused") private final ExpressionNode conditionActualNode;
  @SuppressWarnings("unused") private final ExpressionNode bodyActualNode;

  public WhileInlinedLiteralsNode(final ExpressionNode originalConditionNode,
      final ExpressionNode originalBodyNode, final ExpressionNode inlinedConditionNode,
      final ExpressionNode inlinedBodyNode, final boolean expectedBool) {
    this.expectedBool = expectedBool;
    this.loopNode = Truffle.getRuntime().createLoopNode(
        new WhileRepeatingNode(inlinedConditionNode, inlinedBodyNode, expectedBool));
    this.conditionActualNode = originalConditionNode;
    this.bodyActualNode = originalBodyNode;
  }

  @Override
  public Object executeGeneric(final VirtualFrame frame) {
    loopNode.execute(frame);
    return Nil.nilObject;
  }

  private static final class WhileRepeatingNode extends Node implements RepeatingNode {

    @Child private ExpressionNode conditionNode;
    @Child private ExpressionNode bodyNode;

    private final boolean expectedBool;

    private long iterationCount;

    WhileRepeatingNode(final ExpressionNode conditionNode, final ExpressionNode bodyNode,
        final boolean expectedBool) {
      this.conditionNode = conditionNode;
      this.bodyNode = bodyNode;
      this.expectedBool = expectedBool;
    }

    private boolean evaluateCondition(final VirtualFrame frame) {
      try {
        return conditionNode.executeBoolean(frame);
      } catch (UnexpectedResultException e) {
        CompilerDirectives.transferToInterpreterAndInvalidate();
        throw new UnsupportedSpecializationException(this,
            new Node[] {conditionNode}, e.getResult());
      }
    }

    @Override
    public boolean executeRepeating(final VirtualFrame frame) {
      if (evaluateCondition(frame) != expectedBool) {
        if (CompilerDirectives.inInterpreter()) {
          long count = iterationCount;
          iterationCount = 0;
          reportLoopCount(count);
        }
        return false;
      }
      bodyNode.executeGeneric(frame);
      if (CompilerDirectives.inInterpreter()) {
        iterationCount += 1;
      }
      return true;
    }

    private void reportLoopCount(final long count) {
      if (count < 1) {
        return;
      }
      CompilerAsserts.neverPartOfCompilation("reportLoopCount");
      Node current = getParent();
      while (current != null && !(current instanceof RootNode)) {
        current = current.getParent();
      }
      if (current != null) {
        ((Invokable) current).propagateLoopCountThroughoutLexicalScope(count);
      }
    }
  }
}
