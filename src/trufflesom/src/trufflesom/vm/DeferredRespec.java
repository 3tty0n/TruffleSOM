package trufflesom.vm;

import java.util.concurrent.atomic.AtomicLong;


/**
 * Deferred re-specialisation, {@code -Dsom.deferredRespec=off|slow|deferred|deferred(N)}.
 *
 * <p>When the tail of a send or field-access chain is reached from compiled code, the stock
 * behaviour is {@code transferToInterpreterAndInvalidate} plus {@code replace}, which throws
 * away the whole compiled unit for one changed site. {@code slow} instead keeps the unit and
 * serves the new case behind a {@link com.oracle.truffle.api.CompilerDirectives.TruffleBoundary}
 * forever; {@code deferred(N)} does the same but splices every case recorded in the first N
 * slow hits into the chain at once, so a site costs at most one invalidation per phase.
 *
 * <p>Counters are printed at exit under {@code -Dsom.sendStats=true}.
 */
public final class DeferredRespec {
  public static final String  MODE      = System.getProperty("som.deferredRespec", "off");
  public static final boolean ON        = !"off".equals(MODE);
  public static final int     THRESHOLD = threshold(MODE);

  private static final AtomicLong SEND_CALLS  = new AtomicLong();
  private static final AtomicLong SEND_SITES  = new AtomicLong();
  private static final AtomicLong SEND_EXT    = new AtomicLong();
  private static final AtomicLong FIELD_CALLS = new AtomicLong();
  private static final AtomicLong FIELD_SITES = new AtomicLong();
  private static final AtomicLong FIELD_EXT   = new AtomicLong();

  static {
    if (Boolean.getBoolean("som.sendStats")) {
      Runtime.getRuntime().addShutdownHook(new Thread(() -> System.err.println(
          "sendStats: mode=" + MODE
              + " slowCalls=" + SEND_CALLS.get()
              + " slowSites=" + SEND_SITES.get()
              + " extensions=" + SEND_EXT.get()
              + " fieldSlowCalls=" + FIELD_CALLS.get()
              + " fieldSlowSites=" + FIELD_SITES.get()
              + " fieldExtensions=" + FIELD_EXT.get())));
    }
  }

  private DeferredRespec() {}

  private static int threshold(final String mode) {
    if (!mode.startsWith("deferred")) {
      return 0;
    }
    int open = mode.indexOf('(');
    if (open < 0) {
      return 1000;
    }
    return Integer.parseInt(mode.substring(open + 1, mode.indexOf(')')));
  }

  public static void sendSlow(final boolean firstAtSite) {
    SEND_CALLS.incrementAndGet();
    if (firstAtSite) {
      SEND_SITES.incrementAndGet();
    }
  }

  public static void sendExtension() {
    SEND_EXT.incrementAndGet();
  }

  public static void fieldSlow(final boolean firstAtSite) {
    FIELD_CALLS.incrementAndGet();
    if (firstAtSite) {
      FIELD_SITES.incrementAndGet();
    }
  }

  public static void fieldExtension() {
    FIELD_EXT.incrementAndGet();
  }
}
