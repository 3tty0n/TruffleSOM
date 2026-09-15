package trufflesom.interpreter.nodes.dispatch;

import static com.oracle.truffle.api.CompilerDirectives.transferToInterpreterAndInvalidate;

import com.oracle.truffle.api.CallTarget;
import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.CompilerDirectives.TruffleBoundary;
import com.oracle.truffle.api.frame.VirtualFrame;
import com.oracle.truffle.api.nodes.IndirectCallNode;
import com.oracle.truffle.api.nodes.Node;

import trufflesom.bdt.primitives.nodes.PreevaluatedExpression;
import trufflesom.interpreter.SArguments;
import trufflesom.interpreter.Types;
import trufflesom.vm.DeferredRespec;
import trufflesom.vmobjects.SArray;
import trufflesom.vmobjects.SClass;
import trufflesom.vmobjects.SInvokable;
import trufflesom.vmobjects.SObject;
import trufflesom.vmobjects.SSymbol;


public final class UninitializedDispatchNode extends AbstractDispatchNode {
  private final SSymbol selector;
  private final boolean boundary;

  private Object[] deferredRcvrs;
  private int      deferredCount;
  private boolean  deferredOverflow;
  private long     deferredHits;
  private boolean  deferredDone;

  public UninitializedDispatchNode(final SSymbol selector) {
    this(selector, false);
  }

  public UninitializedDispatchNode(final SSymbol selector, final boolean boundary) {
    this.selector = selector;
    this.boundary = boundary;
  }

  private AbstractDispatchNode specialize(final Object[] arguments) {
    // Determine position in dispatch node chain, i.e., size of inline cache
    Node i = this;
    int chainDepth = 0;
    while (i.getParent() instanceof AbstractDispatchNode) {
      i = i.getParent();
      chainDepth++;
    }
    AbstractDispatchNode first = (AbstractDispatchNode) i;

    Object rcvr = arguments[0];
    assert rcvr != null;

    if (rcvr instanceof SObject) {
      SObject r = (SObject) rcvr;
      if (r.updateLayoutToMatchClass() && first != this) { // if first is this, short cut and
                                                           // directly continue...
        return first;
      }
    }

    if (chainDepth < SEND_CACHE_SIZE) {
      UninitializedDispatchNode newChainEnd = new UninitializedDispatchNode(selector, boundary);
      AbstractDispatchNode node = createDispatch(rcvr, selector, newChainEnd, boundary);

      replace(node);
      newChainEnd.notifyAsInserted();
      return node;
    }

    // the chain is longer than the maximum defined by SEND_CACHE_SIZE and
    // thus, this callsite is considered to be megaprophic, and we generalize it.
    GenericDispatchNode genericReplacement = new GenericDispatchNode(selector);
    first.replace(genericReplacement);
    return genericReplacement;
  }

  public static AbstractDispatchNode createDispatch(final Object rcvr, final SSymbol selector,
      final AbstractDispatchNode newChainEnd, final boolean boundary) {
    SClass rcvrClass = Types.getClassOf(rcvr);
    SInvokable method = rcvrClass.lookupInvokable(selector);

    if (method == null) {
      DispatchGuard guard = DispatchGuard.create(rcvr);
      return new CachedDnuNode(rcvrClass, guard, selector, newChainEnd);
    }

    AbstractDispatchNode node = method.asDispatchNode(rcvr, newChainEnd);
    if (node != null) {
      return node;
    }

    PreevaluatedExpression expr = method.copyTrivialNode();

    DispatchGuard guard = DispatchGuard.create(rcvr);
    if (expr != null) {
      return new CachedExprNode(guard, expr, method.getSource(), newChainEnd);
    }

    CallTarget callTarget = method.getCallTarget();
    if (boundary) {
      return new BoundaryDispatchNode(guard, callTarget, newChainEnd);
    }
    return new CachedDispatchNode(guard, callTarget, newChainEnd);
  }

  /**
   * Deferred re-specialisation: the miss happened in compiled code, so instead of
   * invalidating the enclosing unit, look the method up behind a boundary and call it
   * indirectly, keeping the receiver for a later batched chain extension.
   */
  @TruffleBoundary
  private Object deferredDispatch(final Object[] arguments) {
    Object rcvr = arguments[0];
    DeferredRespec.sendSlow(deferredHits == 0);
    deferredHits++;
    record(rcvr);

    SClass rcvrClass = Types.getClassOf(rcvr);
    SInvokable method = rcvrClass.lookupInvokable(selector);

    CallTarget target;
    Object[] args;
    if (method != null) {
      target = method.getCallTarget();
      args = arguments;
    } else {
      SArray argumentsArray = SArguments.getArgumentsWithoutReceiver(arguments);
      args = new Object[] {rcvr, selector, argumentsArray};
      target = CachedDnuNode.getDnuCallTarget(rcvrClass);
    }

    Object result = IndirectCallNode.getUncached().call(target, args);

    if (DeferredRespec.THRESHOLD > 0 && !deferredDone
        && deferredHits >= DeferredRespec.THRESHOLD) {
      deferredDone = true;
      DeferredRespec.sendExtension();
      extendChain();
    }
    return result;
  }

  private void record(final Object rcvr) {
    if (deferredOverflow) {
      return;
    }
    if (deferredRcvrs == null) {
      deferredRcvrs = new Object[SEND_CACHE_SIZE];
    }
    SClass rcvrClass = Types.getClassOf(rcvr);
    for (int k = 0; k < deferredCount; k++) {
      if (Types.getClassOf(deferredRcvrs[k]) == rcvrClass) {
        return;
      }
    }
    if (deferredCount == deferredRcvrs.length) {
      deferredOverflow = true;
      return;
    }
    deferredRcvrs[deferredCount++] = rcvr;
  }

  /** Splices all recorded receivers into the chain at once; one invalidation, not one per class. */
  private void extendChain() {
    Node i = this;
    int chainDepth = 0;
    while (i.getParent() instanceof AbstractDispatchNode) {
      i = i.getParent();
      chainDepth++;
    }
    AbstractDispatchNode first = (AbstractDispatchNode) i;

    if (deferredOverflow || chainDepth + deferredCount > SEND_CACHE_SIZE) {
      first.replace(new GenericDispatchNode(selector));
      return;
    }

    UninitializedDispatchNode newChainEnd = new UninitializedDispatchNode(selector, boundary);
    AbstractDispatchNode head = newChainEnd;
    for (int k = deferredCount - 1; k >= 0; k--) {
      Object rcvr = deferredRcvrs[k];
      if (rcvr instanceof SObject) {
        ((SObject) rcvr).updateLayoutToMatchClass();
      }
      head = createDispatch(rcvr, selector, head, boundary);
    }

    replace(head);
    newChainEnd.notifyAsInserted();
    deferredRcvrs = null;
    deferredCount = 0;
  }

  @Override
  public Object executeDispatch(final VirtualFrame frame, final Object[] arguments) {
    if (DeferredRespec.ON && CompilerDirectives.inCompiledCode()) {
      return deferredDispatch(arguments);
    }
    transferToInterpreterAndInvalidate();
    return specialize(arguments).executeDispatch(frame, arguments);
  }

  @Override
  public int lengthOfDispatchChain() {
    return 0;
  }
}
