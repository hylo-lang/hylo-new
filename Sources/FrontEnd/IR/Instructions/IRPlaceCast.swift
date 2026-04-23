/// Converts a place of type `A` to a place of type `B`.
///
/// The conversion is not checked. Accessing the resulting place has undefined behavior unless `B`
/// is layout-compatible with `A`.
public struct IRPlaceCast: Instruction {

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

  /// Creates a copy of `other`, substituting its properties with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = [ss[other.source]]
    self.anchor = other.anchor
    self.target = other.target
  }


  /// The place being converted.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(target)
  }

}

extension IRPlaceCast: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "place_cast \(printer.show(source)) to \(printer.show(target))"
  }

}
