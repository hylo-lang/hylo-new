/// Converts a built-in pointer to a place.
public struct IRPointerCast: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the resulting place.
  public let target: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(source: IRValue, target: AnyTypeIdentity, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
    self.target = target
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.target = other.target
  }

  /// The pointer being converted.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(target)
  }

}

extension IRPointerCast: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "pointer_cast \(printer.show(source)) as \(printer.show(target))"
  }

}
