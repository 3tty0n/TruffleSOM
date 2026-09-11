package trufflesom.vm;

public final class SendPlacement {
  public static final String PLACE = System.getProperty("som.sendPlace", "interp");
  public static final boolean AOT = PLACE.equals("aot");
  public static final boolean PGO = PLACE.equals("pgo");
  public static final boolean JIT = PLACE.equals("jit");
  public static final boolean STATS = Boolean.getBoolean("som.sendStats");
  public static final String  SEND_PROFILE = System.getProperty("som.sendProfile");
  public static final boolean SEND_INLINE = Boolean.getBoolean("som.sendInline");
  public static final String  SEND_BOUNDARY = System.getProperty("som.sendBoundary");

  private SendPlacement() {}
}
