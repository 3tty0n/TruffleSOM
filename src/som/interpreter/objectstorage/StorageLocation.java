package som.interpreter.objectstorage;

import som.interpreter.nodes.ExpressionNode;
import som.interpreter.objectstorage.FieldNode.AbstractReadFieldNode;
import som.interpreter.objectstorage.FieldNode.AbstractWriteFieldNode;
import som.interpreter.objectstorage.FieldNode.ReadDoubleFieldNode;
import som.interpreter.objectstorage.FieldNode.ReadLongFieldNode;
import som.interpreter.objectstorage.FieldNode.ReadObjectFieldNode;
import som.interpreter.objectstorage.FieldNode.ReadUnwrittenFieldNode;
import som.interpreter.objectstorage.FieldNode.WriteDoubleFieldNode;
import som.interpreter.objectstorage.FieldNode.WriteLongFieldNode;
import som.interpreter.objectstorage.FieldNode.WriteObjectFieldNode;
import som.vm.Universe;
import som.vmobjects.SObject;

import com.oracle.truffle.api.CompilerDirectives;
import com.oracle.truffle.api.nodes.UnexpectedResultException;


public abstract class StorageLocation {

  public interface LongStorageLocation {
    long readLong(final SObject obj, boolean assumptionValid) throws UnexpectedResultException;
    void writeLong(final SObject obj, final long value);
  }

  public interface DoubleStorageLocation {
    double readDouble(final SObject obj, boolean assumptionValid) throws UnexpectedResultException;
    void   writeDouble(final SObject obj, final double value);
  }

  public static StorageLocation createForLong(final ObjectLayout layout,
      final int primFieldIndex) {
    if (primFieldIndex < SObject.NUM_PRIMITIVE_FIELDS) {
      return new LongDirectStoreLocation(layout, primFieldIndex);
    } else {
      return new LongArrayStoreLocation(layout, primFieldIndex);
    }
  }

  public static StorageLocation createForDouble(final ObjectLayout layout,
      final int primFieldIndex) {
    if (primFieldIndex < SObject.NUM_PRIMITIVE_FIELDS) {
      return new DoubleDirectStoreLocation(layout, primFieldIndex);
    } else {
      throw new RuntimeException("Not yet implemented");
    }
  }

  public static StorageLocation createForObject(final ObjectLayout layout,
      final int objFieldIndex) {
    if (objFieldIndex < SObject.NUM_PRIMITIVE_FIELDS) {
      return new ObjectDirectStorageLocation(layout, objFieldIndex);
    } else {
      return new ObjectArrayStorageLocation(layout, objFieldIndex);
    }
  }

  private ObjectLayout layout;

  protected StorageLocation(final ObjectLayout layout) {
    this.layout = layout;
  }

  public abstract boolean isSet(SObject obj, boolean assumptionValid);
  public abstract Object  read(SObject obj,  boolean assumptionValid);
  public abstract void    write(SObject obj, Object value) throws GeneralizeStorageLocationException, UninitalizedStorageLocationException;
  public abstract Class<?> getStoredClass();

  public abstract AbstractReadFieldNode  getReadNode(ExpressionNode self, int fieldIndex, ObjectLayout layout, AbstractReadFieldNode next);
  public abstract AbstractWriteFieldNode getWriteNode(ExpressionNode self, ExpressionNode value, int fieldIndex, ObjectLayout layout, AbstractWriteFieldNode next);


  public final ObjectLayout getObjectLayout() {
    return layout;
  }

  public final class GeneralizeStorageLocationException extends Exception {
    private static final long serialVersionUID = 4610497040788136337L;
  }

  public final class UninitalizedStorageLocationException extends Exception {
    private static final long serialVersionUID = -3046154908139289066L;
  }

  public static final class UnwrittenStorageLocation extends StorageLocation {
    public UnwrittenStorageLocation(final ObjectLayout layout) {
      super(layout);
    }

    @Override
    public boolean isSet(final SObject obj, final boolean assumptionValid) {
      return false;
    }

    @Override
    public Object read(final SObject obj, final boolean assumptionValid) {
      return Universe.current().nilObject;
    }

    @Override
    public void write(final SObject obj, final Object value) throws UninitalizedStorageLocationException {
      throw new UninitalizedStorageLocationException();
    }

    @Override
    public Class<?> getStoredClass() {
      return null;
    }

    @Override
    public AbstractReadFieldNode getReadNode(final ExpressionNode self, final int fieldIndex,
        final ObjectLayout layout, final AbstractReadFieldNode next) {
      return new ReadUnwrittenFieldNode(self, fieldIndex, layout, next);
    }

    @Override
    public AbstractWriteFieldNode getWriteNode(final ExpressionNode self, final ExpressionNode value, final int fieldIndex,
        final ObjectLayout layout, final AbstractWriteFieldNode next) {
      throw new RuntimeException("we should not get here, should we?");
      // return new UninitializedWriteFieldNode(fieldIndex);
    }
  }

  public abstract static class AbstractObjectStorageLocation extends StorageLocation {
    protected final int fieldIndex;

    public AbstractObjectStorageLocation(final ObjectLayout layout, final int fieldIndex) {
      super(layout);
      this.fieldIndex = fieldIndex;
    }

    @Override
    public abstract void write(final SObject obj, final Object value);

    @Override
    public final Class<?> getStoredClass() {
      return Object.class;
    }

    @Override
    public final AbstractReadFieldNode getReadNode(final ExpressionNode self,
        final int fieldIndex,
        final ObjectLayout layout, final AbstractReadFieldNode next) {
      return new ReadObjectFieldNode(self, fieldIndex, layout, next);
    }

    @Override
    public final AbstractWriteFieldNode getWriteNode(
        final ExpressionNode self, final ExpressionNode value,
        final int fieldIndex,
        final ObjectLayout layout, final AbstractWriteFieldNode next) {
      return new WriteObjectFieldNode(self, value, fieldIndex, layout, next);
    }
  }

  public static final class ObjectDirectStorageLocation extends AbstractObjectStorageLocation {
    private final long fieldOffset;
    public ObjectDirectStorageLocation(final ObjectLayout layout, final int fieldIndex) {
      super(layout, fieldIndex);
      fieldOffset = SObject.getObjectFieldOffset(fieldIndex);
    }

    @Override
    public boolean isSet(final SObject obj, final boolean assumptionValid) {
      return read(obj, assumptionValid) != null;
    }

    @Override
    public Object read(final SObject obj, final boolean assumptionValid) {
      // TODO: for the moment Graal doesn't seem to get the optimizations
      // right, still need to pass in the correct location identifier, which can probably be `this`.
      return CompilerDirectives.unsafeGetObject(obj, fieldOffset, assumptionValid, null);
    }

    @Override
    public void write(final SObject obj, final Object value) {
      // TODO: for the moment Graal doesn't seem to get the optimizations
      // right, still need to pass in the correct location identifier, which can probably be `this`.
      CompilerDirectives.unsafePutObject(obj, fieldOffset, value, null);
    }
  }

  public static final class ObjectArrayStorageLocation extends AbstractObjectStorageLocation {
    private final int extensionIndex;
    public ObjectArrayStorageLocation(final ObjectLayout layout, final int fieldIndex) {
      super(layout, fieldIndex);
      extensionIndex = fieldIndex - SObject.NUM_OBJECT_FIELDS;
    }

    @Override
    public boolean isSet(final SObject obj, final boolean assumptionValid) {
      return read(obj, assumptionValid) != null;
    }

    @Override
    public Object read(final SObject obj, final boolean assumptionValid) {
      // TODO: should we use unsafe operations to avoid overhead of array bounce check etc.?
      return obj.getExtensionObjFields()[extensionIndex];
    }

    @Override
    public void write(final SObject obj, final Object value) {
      // TODO: should we use unsafe operations to avoid overhead of array bounce check etc.?
      obj.getExtensionObjFields()[extensionIndex] = value;
    }
  }

  public abstract static class PrimitiveStorageLocation extends StorageLocation {
    protected final int mask;

    protected PrimitiveStorageLocation(final ObjectLayout layout, final int primField) {
      super(layout);
      mask = SObject.getPrimitiveFieldMask(primField);
    }

    @Override
    public final boolean isSet(final SObject obj, final boolean assumptionValid) {
      return obj.isPrimitiveSet(mask);
    }

    protected final void markAsSet(final SObject obj) {
      obj.markPrimAsSet(mask);
    }
  }

  // TODO: implement PrimitiveArrayStoreLocation
//  public abstract static class PrimitiveArrayStoreLocation extends PrimitiveStorageLocation {
//
//  }

  public abstract static class PrimitiveDirectStoreLocation extends PrimitiveStorageLocation {
    protected final long offset;
    public PrimitiveDirectStoreLocation(final ObjectLayout layout, final int primField) {
      super(layout, primField);
      offset = SObject.getPrimitiveFieldOffset(primField);
    }
  }

  public static final class DoubleDirectStoreLocation extends PrimitiveDirectStoreLocation
      implements DoubleStorageLocation {
    public DoubleDirectStoreLocation(final ObjectLayout layout, final int primField) {
      super(layout, primField);
    }

    @Override
    public Object read(final SObject obj, final boolean assumptionValid) {
      try {
        return readDouble(obj, assumptionValid);
      } catch (UnexpectedResultException e) {
        return e.getResult();
      }
    }

    @Override
    public double readDouble(final SObject obj, final boolean assumptionValid) throws UnexpectedResultException {
      if (isSet(obj, assumptionValid)) {
        // TODO: for the moment Graal doesn't seem to get the optimizations
        // right, still need to pass in the correct location identifier, which can probably be `this`.
        return CompilerDirectives.unsafeGetDouble(obj, offset, assumptionValid, null);
      } else {
        throw new UnexpectedResultException(Universe.current().nilObject);
      }
    }

    @Override
    public void write(final SObject obj, final Object value) throws GeneralizeStorageLocationException {
      assert value != null;
      if (value instanceof Double) {
        writeDouble(obj, (double) value);
      } else {
        throw new GeneralizeStorageLocationException();
      }
    }

    @Override
    public void writeDouble(final SObject obj, final double value) {
      CompilerDirectives.unsafePutDouble(obj, offset, value, null);
      markAsSet(obj);
    }

    @Override
    public Class<?> getStoredClass() {
      return Double.class;
    }

    @Override
    public AbstractReadFieldNode getReadNode(final ExpressionNode self,
        final int fieldIndex,
        final ObjectLayout layout, final AbstractReadFieldNode next) {
      return new ReadDoubleFieldNode(self, fieldIndex, layout, next);
    }

    @Override
    public AbstractWriteFieldNode getWriteNode(final ExpressionNode self, final ExpressionNode value, final int fieldIndex,
        final ObjectLayout layout, final AbstractWriteFieldNode next) {
      return new WriteDoubleFieldNode(self, value, fieldIndex, layout, next);
    }
  }

  public static final class LongDirectStoreLocation extends PrimitiveDirectStoreLocation
      implements LongStorageLocation {
    public LongDirectStoreLocation(final ObjectLayout layout, final int primField) {
      super(layout, primField);
    }

    @Override
    public Object read(final SObject obj, final boolean assumptionValid) {
      try {
        return readLong(obj, assumptionValid);
      } catch (UnexpectedResultException e) {
        return e.getResult();
      }
    }

    @Override
    public long readLong(final SObject obj, final boolean assumptionValid) throws UnexpectedResultException {
      if (isSet(obj, assumptionValid)) {
        // TODO: for the moment Graal doesn't seem to get the optimizations
        // right, still need to pass in the correct location identifier
        return CompilerDirectives.unsafeGetLong(obj, offset, assumptionValid, null);
      } else {
        throw new UnexpectedResultException(Universe.current().nilObject);
      }
    }

    @Override
    public void write(final SObject obj, final Object value) throws GeneralizeStorageLocationException {
      assert value != null;
      if (value instanceof Long) {
        writeLong(obj, (long) value);
      } else {
        throw new GeneralizeStorageLocationException();
      }
    }

    @Override
    public void writeLong(final SObject obj, final long value) {
      CompilerDirectives.unsafePutLong(obj, offset, value, null);
      markAsSet(obj);
    }

    @Override
    public Class<?> getStoredClass() {
      return Long.class;
    }

    @Override
    public AbstractReadFieldNode getReadNode(final ExpressionNode self, final int fieldIndex,
        final ObjectLayout layout, final AbstractReadFieldNode next) {
      return new ReadLongFieldNode(self, fieldIndex, layout, next);
    }

    @Override
    public AbstractWriteFieldNode getWriteNode(final ExpressionNode self, final ExpressionNode value, final int fieldIndex,
        final ObjectLayout layout, final AbstractWriteFieldNode next) {
      return new WriteLongFieldNode(self, value, fieldIndex, layout, next);
    }
  }

  public abstract static class PrimitiveArrayStoreLocation extends PrimitiveStorageLocation {
    protected final int extensionIndex;
    public PrimitiveArrayStoreLocation(final ObjectLayout layout, final int primField) {
      super(layout, primField);
      extensionIndex = primField - SObject.NUM_PRIMITIVE_FIELDS;
      assert extensionIndex >= 0;
    }
  }

  public static final class LongArrayStoreLocation extends PrimitiveArrayStoreLocation
      implements LongStorageLocation {
    public LongArrayStoreLocation(final ObjectLayout layout, final int primField) {
      super(layout, primField);
    }

    @Override
    public Object read(final SObject obj, final boolean assumptionValid) {
      try {
        return readLong(obj, assumptionValid);
      } catch (UnexpectedResultException e) {
        return e.getResult();
      }
    }

    @Override
    public long readLong(final SObject obj, final boolean assumptionValid) throws UnexpectedResultException {
      if (isSet(obj, assumptionValid)) {
        // perhaps we should use the unsafe operations as for doubles
        return obj.getExtendedPrimFields()[extensionIndex];
      } else {
        throw new UnexpectedResultException(Universe.current().nilObject);
      }
    }

    @Override
    public void write(final SObject obj, final Object value) throws GeneralizeStorageLocationException {
      assert value != null;
      if (value instanceof Long) {
        writeLong(obj, (long) value);
      } else {
        throw new GeneralizeStorageLocationException();
      }
    }

    @Override
    public void writeLong(final SObject obj, final long value) {
      obj.getExtendedPrimFields()[extensionIndex] = value;
      markAsSet(obj);
    }

    @Override
    public Class<?> getStoredClass() {
      return Long.class;
    }

    @Override
    public AbstractReadFieldNode getReadNode(final ExpressionNode self, final int fieldIndex,
        final ObjectLayout layout, final AbstractReadFieldNode next) {
      return new ReadLongFieldNode(self, fieldIndex, layout, next);
    }

    @Override
    public AbstractWriteFieldNode getWriteNode(
        final ExpressionNode self, final ExpressionNode value,
        final int fieldIndex,
        final ObjectLayout layout, final AbstractWriteFieldNode next) {
      return new WriteLongFieldNode(self, value, fieldIndex, layout, next);
    }
  }
}
