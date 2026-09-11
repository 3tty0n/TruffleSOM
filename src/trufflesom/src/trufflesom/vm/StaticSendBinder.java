package trufflesom.vm;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.oracle.truffle.api.Assumption;
import com.oracle.truffle.api.Truffle;
import com.oracle.truffle.api.nodes.NodeUtil;

import trufflesom.bdt.primitives.nodes.PreevaluatedExpression;
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
  private static int inlined;
  private static boolean statsHooked;

  // profile-guided placement (pgo)
  private static boolean             profileLoaded;
  private static final Map<String, Boolean> exactGeneric    = new HashMap<>();
  private static final Map<String, Boolean> fallbackGeneric = new HashMap<>();
  private static int                 genericSites;
  private static int                 matchedSites;

  private static boolean         boundaryLoaded;
  private static final Set<String> boundarySet = new HashSet<>();
  private static int             boundarySites;

  private StaticSendBinder() {}

  public static void classLoaded(final SClass clazz) {
    boolean boundaryEnabled = SendPlacement.SEND_BOUNDARY != null;
    if (!(SendPlacement.AOT || SendPlacement.PGO || boundaryEnabled) || clazz == null) {
      return;
    }
    hookStats();
    SClass metaclass = clazz.getSOMClass();
    if (SendPlacement.AOT || SendPlacement.PGO) {
      invalidateOverridden(clazz);
      invalidateOverridden(metaclass);
      classes.add(clazz);
      classes.add(metaclass);
    }
    if (SendPlacement.PGO) {
      if (!profileLoaded) {
        loadProfile();
      }
      markGenericSites(clazz);
      markGenericSites(metaclass);
    }
    if (boundaryEnabled) {
      if (!boundaryLoaded) {
        loadBoundary();
      }
      markBoundarySites(clazz);
      markBoundarySites(metaclass);
    }
    if (SendPlacement.AOT || SendPlacement.PGO) {
      bindClass(clazz);
      bindClass(metaclass);
    }
  }

  private static void hookStats() {
    if (!SendPlacement.STATS || statsHooked) {
      return;
    }
    statsHooked = true;
    Runtime.getRuntime().addShutdownHook(new Thread(() -> {
      System.err.println(
          "static-send: candidates=" + candidates + " bound=" + bound + " unbound=" + unbound
              + " noParent=" + noParent + " noTarget=" + noTarget + " overridden=" + overridden
              + " inlined_sites=" + inlined);
      if (SendPlacement.PGO) {
        System.err.println("pgo: generic_sites=" + genericSites + " matched=" + matchedSites);
      }
      if (SendPlacement.SEND_BOUNDARY != null) {
        System.err.println("boundary: sites=" + boundarySites);
      }
    }));
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
      PreevaluatedExpression trivial =
          SendPlacement.SEND_INLINE ? target.copyTrivialNode() : null;
      if (trivial != null) {
        node.replace(MessageSendNode.createInlinedSelfSend(selector, node.getArgumentNodes(),
            trivial, assumption, node.getSourceCoordinate()));
        inlined++;
      } else {
        node.replace(MessageSendNode.createBoundSelfSend(selector, node.getArgumentNodes(),
            target, assumption, node.getSourceCoordinate()));
      }
      List<Site> list = sites.get(selector);
      if (list == null) {
        list = new ArrayList<>();
        sites.put(selector, list);
      }
      list.add(new Site(clazz, assumption));
      bound++;
    }
  }

  // ---- profile-guided placement (pgo) ----

  private static boolean isGeneric(final int distinctClasses, final long lastNewClassIndex,
      final long sendsTotal) {
    if (distinctClasses >= 5) {
      return true;
    }
    return distinctClasses > 1 && sendsTotal > 0 && lastNewClassIndex > 0.5 * sendsTotal;
  }

  private static void loadProfile() {
    profileLoaded = true;
    String path = SendPlacement.SEND_PROFILE;
    if (path == null) {
      return;
    }
    List<String> lines;
    try {
      lines = Files.readAllLines(Paths.get(path));
    } catch (IOException e) {
      return;
    }

    boolean inSites = false;
    long sendsTotal = 0;
    Map<String, boolean[]> agg = new HashMap<>();

    for (String line : lines) {
      if (line.isEmpty()) {
        continue;
      }
      if (line.equals("# sites")) {
        inSites = true;
        continue;
      }
      if (line.equals("# summary")) {
        inSites = false;
        continue;
      }
      if (!inSites) {
        if (line.startsWith("sends_total\t")) {
          sendsTotal = Long.parseLong(line.substring("sends_total\t".length()));
        }
        continue;
      }

      String[] parts = line.split("\t", -1);
      if (parts.length != 9 || parts[0].equals("holder")) {
        continue;
      }
      String holder = parts[0];
      String signature = parts[1];
      String selector = parts[3];
      int ordinal = Integer.parseInt(parts[4]);
      int distinctClasses = Integer.parseInt(parts[6]);
      long lastNewClassIndex = Long.parseLong(parts[8]);
      boolean generic = isGeneric(distinctClasses, lastNewClassIndex, sendsTotal);

      exactGeneric.put(key(holder, signature, selector, ordinal), generic);

      String selKey = holder + " " + selector;
      boolean[] a = agg.computeIfAbsent(selKey, k -> new boolean[2]);
      if (generic) {
        a[0] = true;
      } else {
        a[1] = true;
      }
    }

    for (Map.Entry<String, boolean[]> e : agg.entrySet()) {
      boolean[] a = e.getValue();
      if (a[0] ^ a[1]) {
        fallbackGeneric.put(e.getKey(), a[0]);
      }
    }
  }

  private static String key(final String holder, final String signature, final String selector,
      final int ordinal) {
    return holder + " " + signature + " " + selector + " " + ordinal;
  }

  private static Boolean lookupGeneric(final String holder, final String signature,
      final String selector, final int ordinal) {
    Boolean exact = exactGeneric.get(key(holder, signature, selector, ordinal));
    if (exact != null) {
      return exact;
    }
    return fallbackGeneric.get(holder + " " + selector);
  }

  private static void markGenericSites(final SClass clazz) {
    if (clazz.getInstanceInvokablesForDisassembler() == null) {
      return;
    }
    for (SInvokable inv : clazz.getInstanceInvokablesForDisassembler()) {
      if (inv.getHolder() == clazz) {
        markGenericInvokable(inv, clazz);
      }
    }
  }

  private static void markGenericInvokable(final SInvokable inv, final SClass clazz) {
    inv.getCallTarget();
    List<UninitializedMessageSendNode> nodes = new ArrayList<>(
        NodeUtil.findAllNodeInstances(inv.getInvokable(), UninitializedMessageSendNode.class));
    nodes.sort(Comparator.comparingLong(UninitializedMessageSendNode::getSourceCoordinate));

    String holderName = clazz.getName().getString();
    String sigName = inv.getSignature().getString();
    Map<SSymbol, Integer> ordinalCounter = new HashMap<>();

    for (UninitializedMessageSendNode node : nodes) {
      SSymbol selector = node.getSelector();
      int ordinal = ordinalCounter.merge(selector, 1, Integer::sum) - 1;

      Boolean generic = lookupGeneric(holderName, sigName, selector.getString(), ordinal);
      if (generic == null) {
        continue;
      }
      matchedSites++;
      if (generic && node.getParent() != null) {
        node.replace(MessageSendNode.createGenericDispatch(selector, node.getArgumentNodes(),
            node.getSourceCoordinate()));
        genericSites++;
      }
    }

    if (inv instanceof SMethod) {
      for (SMethod block : ((SMethod) inv).getEmbeddedBlocks()) {
        markGenericInvokable(block, clazz);
      }
    }
  }


  private static void loadBoundary() {
    boundaryLoaded = true;
    String path = SendPlacement.SEND_BOUNDARY;
    if (path == null) {
      return;
    }
    List<String> lines;
    try {
      lines = Files.readAllLines(Paths.get(path));
    } catch (IOException e) {
      return;
    }

    for (String line : lines) {
      if (line.isEmpty()) {
        continue;
      }
      String[] parts = line.split("\t", -1);
      if (parts.length != 4 || parts[0].equals("holder")) {
        continue;
      }
      String holder = parts[0];
      String signature = parts[1];
      String selector = parts[2];
      int ordinal = Integer.parseInt(parts[3]);
      boundarySet.add(key(holder, signature, selector, ordinal));
    }
  }

  private static void markBoundarySites(final SClass clazz) {
    if (clazz.getInstanceInvokablesForDisassembler() == null) {
      return;
    }
    for (SInvokable inv : clazz.getInstanceInvokablesForDisassembler()) {
      if (inv.getHolder() == clazz) {
        markBoundaryInvokable(inv, clazz);
      }
    }
  }

  private static void markBoundaryInvokable(final SInvokable inv, final SClass clazz) {
    inv.getCallTarget();
    List<UninitializedMessageSendNode> nodes = new ArrayList<>(
        NodeUtil.findAllNodeInstances(inv.getInvokable(), UninitializedMessageSendNode.class));
    nodes.sort(Comparator.comparingLong(UninitializedMessageSendNode::getSourceCoordinate));

    String holderName = clazz.getName().getString();
    String sigName = inv.getSignature().getString();
    Map<SSymbol, Integer> ordinalCounter = new HashMap<>();

    for (UninitializedMessageSendNode node : nodes) {
      SSymbol selector = node.getSelector();
      int ordinal = ordinalCounter.merge(selector, 1, Integer::sum) - 1;

      if (node.getParent() != null
          && boundarySet.contains(key(holderName, sigName, selector.getString(), ordinal))) {
        node.replace(MessageSendNode.createBoundaryDispatch(selector, node.getArgumentNodes(),
            node.getSourceCoordinate()));
        boundarySites++;
      }
    }

    if (inv instanceof SMethod) {
      for (SMethod block : ((SMethod) inv).getEmbeddedBlocks()) {
        markBoundaryInvokable(block, clazz);
      }
    }
  }
}
