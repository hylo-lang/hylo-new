/// Creates a witness table.
public struct IRWitnessTable: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the witness produced by this instruction.
  public let witnessType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(witnessType: AnyTypeIdentity, members: [IRValue], anchor: Anchor) {
    self.operands = members
    self.anchor = anchor
    self.witnessType = witnessType
  }

  /// Creates a copy of `other`, substituting its properities with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in ss[o] })
    self.anchor = other.anchor
    self.witnessType = other.witnessType
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .value(witnessType)
  }

}

extension IRWitnessTable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "witnesstable {\(printer.show(operands))} as \(printer.show(witnessType))"
  }

}
