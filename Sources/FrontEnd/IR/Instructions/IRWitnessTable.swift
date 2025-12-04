/// Allocates and initializes a witness table. 
///
/// The witness table is allocated on the stack.
public struct IRWitnessTable: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the witness produced by this instruction.
  public let witnessType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(witnessType: AnyTypeIdentity, anchor: Anchor) {
    self.operands = []
    self.anchor = anchor
    self.witnessType = witnessType
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .addressOf(witnessType)
  }

}

extension IRWitnessTable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "witnesstable \(printer.show(witnessType))"
  }

}
