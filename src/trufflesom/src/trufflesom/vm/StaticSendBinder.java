package trufflesom.vm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.oracle.truffle.api.Assumption;
import com.oracle.truffle.api.Truffle;
import com.oracle.truffle.api.nodes.NodeUtil;

import trufflesom.interpreter.nodes.ArgumentReadNode.LocalArgumentReadNode;
import trufflesom.interpreter.nodes.ArgumentReadNode.NonLocalArgumentReadNode;
import trufflesom.interpreter.nodes.ExpressionNode;
import trufflesom.interpreter.nodes.MessageSendNode;
import trufflesom.interpreter.nodes.UninitializedMessageSendNode;
import trufflesom.vmobjects.SClass;
import trufflesom.vmobjects.SInvokable;
import trufflesom.vmobjects.SInvokable.SMethod;
import trufflesom.vmobjects.SSymbol;

public final class StaticSendBinder {
  private static final class Site {
    final SClass     holder;
    final Assumption assumption;

    Site(final SClass holder, final Assumption assumption) {
      this.holder = holder;
      this.assumption = assumption;
    }
  }

  private static final List<SClass>              classes = new ArrayList<>();
  private static final Map<SSymbol, List<Site>>  sites   = new HashMap<>();

  private static int candidates;
  private static int bound;
  private static int unbound;
  private static int noParent;
  private static int noTarget;
  private static int overridden;
  private static boolean statsHooked;

  private StaticSendBinder() {}

  public static void classLoaded(final SClass clazz) {
    if (!SendPlacement.AOT || clazz == null) {
      return;
    }
    hookStats();
    SClass metaclass = clazz.getSOMClass();
    invalidateOverridden(clazz);
    invalidateOverridden(metaclass);
    classes.add(clazz);
    classes.add(metaclass);
    bindClass(clazz);
    bindClass(metaclass);
  }

  private static void hookStats() {
    if (!SendPlacement.STATS || statsHooked) {
      return;
    }
    statsHooked = true;
    Runtime.getRuntime().addShutdownHook(new Thread(() -> System.err.println(
        "static-send: candidates=" + candidates + " bound=" + bound + " unbound=" + unbound
            + " noParent=" + noParent + " noTarget=" + noTarget + " overridden=" + overridden)));
  }

  private static boolean isSubclass(final SClass clazz, final SClass ancestor) {
    SClass c = clazz;
    while (true) {
      if (c == ancestor) {
        return true;
      }
      if (!c.hasSuperClass()) {
        return false;
      }
      c = (SClass) c.getSuperClass();
    }
  }

  private static void invalidateOverridden(final SClass clazz) {
    if (clazz.getInstanceInvokablesForDisassembler() == null) {
      return;
    }
    for (SInvokable inv : clazz.getInstanceInvokablesForDisassembler()) {
      if (inv.getHolder() != clazz) {
        continue;
      }
      List<Site> list = sites.get(inv.getSignature());
      if (list == null) {
        continue;
      }
      for (Site site : list) {
        if (site.holder != clazz && site.assumption.isValid()
            && isSubclass(clazz, site.holder)) {
          site.assumption.invalidate("overridden by " + clazz.getName().getString());
          unbound++;
        }
      }
    }
  }

  private static boolean overriddenBelow(final SClass holder, final SSymbol selector) {
    for (SClass d : classes) {
      if (d != holder && isSubclass(d, holder) && d.lookupOwnInvokable(selector) != null) {
        return true;
      }
    }
    return false;
  }

  private static boolean isSelfRead(final ExpressionNode node) {
    if (node instanceof LocalArgumentReadNode) {
      return ((LocalArgumentReadNode) node).isSelfRead();
    }
    if (node instanceof NonLocalArgumentReadNode) {
      return ((NonLocalArgumentReadNode) node).isSelfRead();
    }
    return false;
  }

  private static void collectSelfSends(final SInvokable inv,
      final List<UninitializedMessageSendNode> out) {
    inv.getCallTarget();
    for (UninitializedMessageSendNode node : NodeUtil.findAllNodeInstances(
        inv.getInvokable(), UninitializedMessageSendNode.class)) {
      ExpressionNode[] args = node.getArgumentNodes();
      if (args.length > 0 && isSelfRead(args[0])) {
        out.add(node);
      }
    }
    if (inv instanceof SMethod) {
      for (SMethod block : ((SMethod) inv).getEmbeddedBlocks()) {
        collectSelfSends(block, out);
      }
    }
  }

  private static void bindClass(final SClass clazz) {
    if (clazz.getInstanceInvokablesForDisassembler() == null) {
      return;
    }
    List<UninitializedMessageSendNode> nodes = new ArrayList<>();
    for (SInvokable inv : clazz.getInstanceInvokablesForDisassembler()) {
      if (inv.getHolder() == clazz) {
        collectSelfSends(inv, nodes);
      }
    }
    for (UninitializedMessageSendNode node : nodes) {
      candidates++;
      if (node.getParent() == null) {
        noParent++;
        continue;
      }
      SSymbol selector = node.getSelector();
      SInvokable target = clazz.lookupInvokable(selector);
      if (target == null) {
        noTarget++;
        continue;
      }
      if (overriddenBelow(clazz, selector)) {
        overridden++;
        continue;
      }
      Assumption assumption =
          Truffle.getRuntime().createAssumption("self-send " + selector.getString());
      node.replace(MessageSendNode.createBoundSelfSend(selector, node.getArgumentNodes(),
          target, assumption, node.getSourceCoordinate()));
      List<Site> list = sites.get(selector);
      if (list == null) {
        list = new ArrayList<>();
        sites.put(selector, list);
      }
      list.add(new Site(clazz, assumption));
      bound++;
    }
  }
}
