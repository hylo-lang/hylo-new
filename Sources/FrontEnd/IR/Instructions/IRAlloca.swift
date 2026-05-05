/// Allocates memory on the stack for storing instances of a type known at compile-time.
///
/// The result of the instruction is the address of stack-allocated storage capable of holding one
/// instance of `storageType`. The storage is uninitialized and deallocated automatically when the
/// function returns, at which point it must be deinitialized.
///
/// Unlike LLVM's alloca, this instruction cannot be used to allocate dynamically sized buffers. It
/// is nonetheless possible to allocate storage for a fixed number of contiguous instances using a
/// tuple (e.g., `Int[8]` in surface syntax).
///
/// Repeated allocas may happen in loops, in which case only the first allocation will be emitted.
/// Upon repeated allocations, the existing value in the storage must have been deinitialized.
/// Moving all allocas in the entry block of the function will be done right before LLVM lowering,
/// after subscript elaboration.
public struct IRAlloca: Instruction {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the allocated storage.
  public let storage: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// Creates an instance with the given properties.
  public init(storage: AnyTypeIdentity, alignment: IRAlignment, anchor: Anchor) {
    self.anchor = anchor
    self.storage = storage
    self.alignment = alignment
  }

  /// Creates a copy of `other`, substituting its properties with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self = other
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(storage)
  }

}

extension IRAlloca: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "alloca \(printer.show(storage)), \(printer.show(alignment))"
  }

}
