/// Allocates memory on the stack.
///
/// The result of the instruction is the address of stack-allocated storage capable of holding
/// an instance of `storageType` contiguously. The storage is uninitialized and deallocated when
/// then function returns, at which point it must be deinitialized.
///
/// Stack allocations should generally be emitted in the entry block of the function. `alloca`s
/// occurring in loops are illegal.
public struct IRAlloca: Instruction {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the allocated storage.
  public let storageType: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// Creates an instance with the given properties.
  public init(
    storageType: AnyTypeIdentity, alignment: IRAlignment, anchor: Anchor
  ) {
    self.anchor = anchor
    self.storageType = storageType
    self.alignment = alignment
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .addressOf(storageType)
  }

}

extension IRAlloca: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "alloca \(printer.show(storageType)), \(printer.show(alignment))"
  }

}
