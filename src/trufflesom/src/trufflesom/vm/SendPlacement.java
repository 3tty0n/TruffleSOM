package trufflesom.vm;

public final class SendPlacement {
  public static final String PLACE = System.getProperty("som.sendPlace", "interp");
  public static final boolean AOT = PLACE.equals("aot");
  public static final boolean JIT = PLACE.equals("jit");
  public static final boolean STATS = Boolean.getBoolean("som.sendStats");

  private SendPlacement() {}
}
