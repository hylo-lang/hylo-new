import Archivist
import Utilities

/// Computes the address of storage for a field or sub-field of a record.
@Archivable
public struct IRSubfield: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// A list of indices identifying the subfield whose address is computed.
  public let path: IndexPath

  /// The type of the subfield being accessed.
  public let subfieldType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    whole: IRValue, path: IndexPath, subfieldType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [whole]
    self.anchor = anchor
    self.path = path
    self.subfieldType = subfieldType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.whole]]
    self.anchor = properties.anchor(other)
    self.path = other.path
    self.subfieldType = other.subfieldType
  }

  /// The place of the whole containing the subfield being accessed.
  public var whole: IRValue {
    operands[0]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(subfieldType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }
}

extension IRSubfield: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "subfield \(printer.show(whole)) at \(list: path) as \(printer.show(subfieldType))"
  }

}
