import java.lang.classfile.*;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.constant.*;
import java.nio.file.*;
import java.util.*;

/**
 * Adds `ProbeLog` calls to compiled classfiles in place, so `Run` sees the methods a compiler's
 * code enters as it sees `Render`'s (Track J4): each method logs its class on entry, and each
 * `getstatic` of a class whose internal name starts with `prefix` logs that class, as the model's
 * `getstatic` does. Class initialisation is not modelled, so a static initialiser is muted.
 *
 * Usage: java Instrument prefix dir...
 */
public class Instrument {
  static final ClassDesc LOG = ClassDesc.of("ProbeLog");
  static final MethodTypeDesc RAN = MethodTypeDesc.of(ConstantDescs.CD_void, ConstantDescs.CD_String);
  static final MethodTypeDesc VOID = MethodTypeDesc.of(ConstantDescs.CD_void);

  public static void main(String[] args) throws Exception {
    String prefix = args[0];
    for (int i = 1; i < args.length; i++) {
      List<Path> classes;
      try (var files = Files.walk(Path.of(args[i]))) {
        classes = files.filter(f -> f.toString().endsWith(".class")).toList();
      }
      for (Path p : classes) {
        ClassFile cf = ClassFile.of();
        ClassModel cm = cf.parse(p);
        String owner = cm.thisClass().asInternalName().replace('/', '.');
        byte[] logged = cf.transformClass(cm, ClassTransform.transformingMethodBodies(
            m -> !m.methodName().equalsString("<clinit>"), new CodeTransform() {
          @Override public void atStart(CodeBuilder b) { b.ldc(owner).invokestatic(LOG, "ran", RAN); }
          @Override public void accept(CodeBuilder b, CodeElement e) {
            b.with(e);
            if (e instanceof FieldInstruction fi && fi.opcode() == Opcode.GETSTATIC
                && fi.owner().asInternalName().startsWith(prefix)) {
              b.ldc(fi.owner().asInternalName().replace('/', '.')).invokestatic(LOG, "ran", RAN);
            }
          }
        }));
        Files.write(p, cf.transformClass(cf.parse(logged), ClassTransform.transformingMethodBodies(
            m -> m.methodName().equalsString("<clinit>"), new CodeTransform() {
          @Override public void atStart(CodeBuilder b) { b.invokestatic(LOG, "mute", VOID); }
          @Override public void accept(CodeBuilder b, CodeElement e) {
            if (e instanceof ReturnInstruction) b.invokestatic(LOG, "unmute", VOID);
            b.with(e);
          }
        })));
      }
    }
  }
}
