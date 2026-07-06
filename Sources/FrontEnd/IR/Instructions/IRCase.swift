import Archivist

/// Accesses to the payload of an enum.
@Archivable
public struct IRCase: IRRegionEntry {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The declaration of the case describing the payload being accessed.
  public let payload: EnumCaseDeclaration.ID

  /// The type of the payload being accessed.
  public let payloadType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    source: IRValue, payload: EnumCaseDeclaration.ID, payloadType: AnyTypeIdentity, anchor: Anchor
  ) {
    self.operands = [source]
    self.anchor = anchor
    self.payload = payload
    self.payloadType = payloadType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.payload = other.payload
    self.payloadType = other.payloadType
  }

  /// The place of the enum whose payload is accessed.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the payload being accessed.
  public var type: IRType {
    .place(payloadType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

}

extension IRCase: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "case \"\(printer.program[payload].identifier.value)\" of \(printer.show(source))"
  }

}
