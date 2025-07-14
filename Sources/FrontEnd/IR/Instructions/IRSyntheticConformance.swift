/// Returns the synthesized the conformance of a type to a core trait.
public struct IRSyntheticConformance: Instruction {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the witness synthesized by this instruction.
  public let witness: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(witness: AnyTypeIdentity, anchor: Anchor) {
    self.anchor = anchor
    self.witness = witness
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .hylo(witness, isAddress: true)
  }

}

extension IRSyntheticConformance: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "synthetic_conformance \(printer.show(witness))"
  }

}

