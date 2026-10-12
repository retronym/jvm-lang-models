import java.util.ArrayList;
import java.util.List;

/**
 * Rendered methods call `ran` with their owner on entry, so the probe sees the sequence of methods
 * entered (Track J4). A get site logs its field's value (the owner's name); a put site logs a `Put`
 * for `Run` to find which class's field changed. Instantiating a receiver is muted: the model's
 * `new` enters no method.
 */
public final class ProbeLog {
  public record Put(Object obj, String field) {}

  public static final List<Object> entered = new ArrayList<>();
  public static int muted;

  public static void ran(String owner) { if (muted == 0) entered.add(owner); }
  public static void put(Object obj, String field) { if (muted == 0) entered.add(new Put(obj, field)); }
  public static void mute() { muted++; }
  public static void unmute() { muted--; }

  public static void reset() { entered.clear(); muted = 0; }
}
