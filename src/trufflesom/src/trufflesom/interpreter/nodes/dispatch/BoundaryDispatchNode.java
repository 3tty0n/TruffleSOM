package trufflesom.interpreter.nodes.dispatch;

import com.oracle.truffle.api.CallTarget;
import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.IndirectCallNode;
import com.oracle.truffle.api.nodes.InvalidAssumptionException;

import trufflesom.interpreter.nodes.SOMNode;

/**
 * Like {@link CachedDispatchNode}, but calls the cached target through a
 * {@link TruffleBoundary} using an {@link IndirectCallNode} instead of a {@link
 * com.oracle.truffle.api.nodes.DirectCallNode} child. This keeps the polymorphic inline
 * cache (the guard chain), but prevents partial evaluation from inlining the callee's
 * bytecode into the caller's compilation unit: the callee compiles as its own call target.
 */
public final class BoundaryDispatchNode extends AbstractDispatchNode {

  private final DispatchGuard guard;
  private final CallTarget    callTarget;

  @Child private AbstractDispatchNode nextInCache;

  public BoundaryDispatchNode(final DispatchGuard guard, final CallTarget callTarget,
      final AbstractDispatchNode nextInCache) {
    this.guard = guard;
    this.callTarget = callTarget;
    this.nextInCache = nextInCache;
  }

  @TruffleBoundary
  private static Object callBoundary(final CallTarget target, final Object[] arguments) {
    return IndirectCallNode.getUncached().call(target, arguments);
  }

  @Override
  public Object executeDispatch(final VirtualFrame frame, final Object[] arguments) {
    Object rcvr = arguments[0];
    try {
      if (guard.entryMatches(rcvr)) {
        return callBoundary(callTarget, arguments);
      } else {
        return nextInCache.executeDispatch(frame, arguments);
      }
    } catch (InvalidAssumptionException e) {
      CompilerDirectives.transferToInterpreterAndInvalidate();
      return replace(SOMNode.unwrapIfNeeded(
          nextInCache)).executeDispatch(frame, arguments);
    }
  }

  @Override
  public int lengthOfDispatchChain() {
    return 1 + nextInCache.lengthOfDispatchChain();
  }
}
