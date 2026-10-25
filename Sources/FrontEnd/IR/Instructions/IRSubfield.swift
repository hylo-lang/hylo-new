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
  public let part: IndexPath

  /// The type of the subfield being accessed.
  public let partType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    whole: IRValue, part: IndexPath, partType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [whole]
    self.anchor = anchor
    self.part = part
    self.partType = partType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.whole]]
    self.anchor = properties.anchor(other)
    self.part = other.part
    self.partType = other.partType
  }

  /// The place of the whole containing the subfield being accessed.
  public var whole: IRValue {
    operands[0]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(partType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }
}

extension IRSubfield: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "subfield \(printer.show(whole)) at \(list: part) as \(printer.show(partType))"
  }

}
