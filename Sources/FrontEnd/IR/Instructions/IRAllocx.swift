/// Allocates memory on the stack for storing instances of a type known at run-time.
///
/// This instruction is similar to `alloca` except that it uses a type witness to determine the
/// size and alignment of the allocated storage.
public struct IRAllocx: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// An existential type representing the type of the allocated storage.
  public let storage: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// Creates an instance with the given properties.
  public init(storage: AnyTypeIdentity, witness: IRValue, alignment: IRAlignment, anchor: Anchor) {
    self.operands = [witness]
    self.anchor = anchor
    self.storage = storage
    self.alignment = alignment
  }

  /// Creates a copy of `other`, substituting its properities with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = [ss[other.witness]]
    self.anchor = other.anchor
    self.storage = other.storage
    self.alignment = other.alignment
  }

  /// An existential type representing the type of the allocated storage.
  public var witness: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .addressOf(storage)
  }

}

extension IRAllocx: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "allocx \(printer.show(witness)) as \(printer.show(storage)), \(printer.show(alignment))"
  }

}
