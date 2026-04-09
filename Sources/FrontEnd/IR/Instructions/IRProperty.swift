/// Returns the address of a property stored in an opaque record.
public struct IRProperty: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The property being accessed.
  public let property: DeclarationIdentity

  /// The type of the property being accessed.
  public let propertyType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    receiver: IRValue, property: DeclarationIdentity, propertyType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [receiver]
    self.anchor = anchor
    self.property = property
    self.propertyType = propertyType
  }

  /// Creates a copy of `other`, substituting its properities with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = [ss[other.receiver]]
    self.anchor = other.anchor
    self.property = other.property
    self.propertyType = other.propertyType
  }

  /// The address of the record containing the property whose getter is returned.
  public var receiver: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(propertyType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

}

extension IRProperty: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "property \"\(printer.program.nameOrTag(of: property))\" of \(printer.show(receiver))"
  }

}
