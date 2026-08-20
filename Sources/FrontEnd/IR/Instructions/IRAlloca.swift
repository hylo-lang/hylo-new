import Archivist

/// Allocates memory on the stack.
///
/// The instruction defines a place capable of storing an instance of `storage`, allocated on the
/// stack. The place is uninitialized after its creation and it must be deinitialized before its
/// deallocation, which occurs automatically when the function returns. Allocated memory is valid
/// only in blocks dominated by the instruction.
///
/// Unlike LLVM's alloca, this instruction cannot be used to allocate dynamically sized buffers. It
/// is nonetheless possible to allocate storage for a fixed number of contiguous instances using a
/// tuple (e.g., `Int[8]` in surface syntax).
@Archivable
public struct IRAlloca: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the allocated storage.
  public let storage: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// Creates an instance denoting a stack allocation aligned at `alignment` for storing instances
  /// of `storage`, whose size is known at compile-time.
  public init(staticallySized storage: AnyTypeIdentity, alignment: IRAlignment, anchor: Anchor) {
    self.operands = []
    self.anchor = anchor
    self.storage = storage
    self.alignment = alignment
  }

  /// Creates an instance denoting a stack allocation aligned at `alignment` for storing instances
  /// of `storage`, show size can only be known at run-time using `storageTypeWitness`.
  public init(
    dynamicallySized storage: AnyTypeIdentity, witnessedBy storageTypeWitness: IRValue,
    alignment: IRAlignment, anchor: Anchor
  ) {
    self.operands = [storageTypeWitness]
    self.anchor = anchor
    self.storage = storage
    self.alignment = alignment
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.storage = other.storage
    self.alignment = other.alignment
  }

  /// A witness of the run-time type of the allocated storage iff the size of the allocation is not
  /// available at compile-time.
  public var storageTypeWitness: IRValue? {
    operands.first
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(storage)
  }

}

extension IRAlloca: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let w = storageTypeWitness {
      return "alloca \(printer.show(w)) as \(printer.show(storage)), \(printer.show(alignment))"
    } else {
      return "alloca \(printer.show(storage)), \(printer.show(alignment))"
    }
  }

}
