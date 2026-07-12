import Archivist
import Utilities

/// Accesses to the payload of an enum.
///
///     case <payload : declaration> of <source : value>
///
/// `case` identifies the place representing the associated value (i.e., the payload) of the enum
/// in place `source` for the case declared by `payload`.
///
/// If `source` is initialized or partially initialized, `payload` must be the declaration of the
/// case currently active. In this case, the discriminator of the enum held in `source` corresponds
/// to `payload` and it is not modified. If `source` is uninitialized, then the discriminator of
/// the enum is set to the value corresponding to `payload`.
@Archivable
public struct IRCase: IRRegionEntry {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The declaration of the case describing the payload being accessed.
  public let payload: EnumCaseDeclaration.ID

  /// The opaque union type with which the result of this instruction is presented.
  public let opaquePayloadType: OpaqueType.ID

  /// Creates an instance with the given properties.
  public init(
    source: IRValue, payload: EnumCaseDeclaration.ID, opaquePayloadType: OpaqueType.ID,
    anchor: Anchor
  ) {
    self.operands = [source]
    self.anchor = anchor
    self.payload = payload
    self.opaquePayloadType = opaquePayloadType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.payload = other.payload
    self.opaquePayloadType = other.opaquePayloadType
  }

  /// The place of the enum whose payload is accessed.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the payload being accessed.
  public var type: IRType {
    .place(opaquePayloadType.erased)
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
