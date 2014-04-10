package som.interpreter.nodes.dispatch;

import static som.interpreter.TruffleCompiler.transferToInterpreterAndInvalidate;
import som.interpreter.Types;
import som.interpreter.nodes.MessageSendNode.GenericMessageSendNode;
import som.vm.Universe;
import som.vmobjects.SClass;
import som.vmobjects.SInvokable;
import som.vmobjects.SObject;
import som.vmobjects.SSymbol;

import com.oracle.truffle.api.nodes.Node;


public final class UninitializedDispatchNode extends AbstractDispatchWithLookupNode {

  public UninitializedDispatchNode(final SSymbol selector, final Universe universe) {
    super(selector, universe);
  }

  @Override
  public Object executeDispatch(final Object[] arguments) {
    transferToInterpreterAndInvalidate("Initialize a dispatch node.");
    Object rcvr = arguments[0];

    // Determine position in dispatch node chain, i.e., size of inline cache
    Node i = this;
    int chainDepth = 0;
    while (i.getParent() instanceof AbstractDispatchNode) {
      i = i.getParent();
      chainDepth++;
    }
    GenericMessageSendNode sendNode = (GenericMessageSendNode) i.getParent();


    if (chainDepth < INLINE_CACHE_SIZE) {
      SClass rcvrClass = Types.getClassOf(rcvr, universe);
      SInvokable method = rcvrClass.lookupInvokable(selector);

      if (method != null) {
        UninitializedDispatchNode newChainEnd = new UninitializedDispatchNode(selector, universe);

//        if (method.getInvokable().isAlwaysToBeInlined()) {
//          InlinedDispatchNode inlined = InlinedDispatchNode.create(
//              rcvrClass, method, newChainEnd, universe);
//          return replace(inlined).executeDispatch(frame, arguments);
//        } else {
          if (rcvr instanceof SObject) {
            SObject receiver = (SObject) rcvr;
            CachedDispatchSObjectCheckNode node =
                new CachedDispatchSObjectCheckNode(receiver.getSOMClass(universe),
                    method, newChainEnd);
            if ((getParent() instanceof CachedDispatchSObjectCheckNode)) {

              return replace(node).executeDispatch(arguments);
            } else {
              SObjectCheckDispatchNode checkNode = new SObjectCheckDispatchNode(node,
                  new UninitializedDispatchNode(selector, universe));
              return replace(checkNode).executeDispatch(arguments);
            }
          } else {
            // the simple checks are prepended
            CachedDispatchSimpleCheckNode node =
                new CachedDispatchSimpleCheckNode(
                    rcvr.getClass(), method,
                    sendNode.getDispatchListHead());
            sendNode.adoptNewDispatchListHead(node);
            return node.executeDispatch(arguments);
          }
      }
      // if method == null: fall through and use generic node
    }

    // the chain is longer than the maximum defined by INLINE_CACHE_SIZE and
    // thus, this callsite is considered to be megaprophic, and we generalize
    // it.
    // Or, the lookup failed, and we have a callsite that leads to a
    // does not understand, which means, we also treat this callsite as
    // megamorphic.
    // TODO: see whether we could get #DNUs fast.
    GenericDispatchNode genericReplacement = new GenericDispatchNode(selector, universe);
    sendNode.replaceDispatchListHead(genericReplacement);
    return genericReplacement.executeDispatch(arguments);
  }
}
