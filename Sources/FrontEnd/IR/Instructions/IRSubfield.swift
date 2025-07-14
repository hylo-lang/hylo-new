import Utilities

/// Computes the address of storage for a field or sub-field of a record.
public struct IRSubfield: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// A list of indices identifying the subfield whose address is computed.
  public let path: IndexPath

  /// The type of the subfield being accessed.
  public let typeOfSubfield: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    base: IRValue, path: IndexPath, typeOfSubfield: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [base]
    self.anchor = anchor
    self.path = path
    self.typeOfSubfield = typeOfSubfield
  }

  /// The address of the record containing the subfield whose address is computed.
  public var base: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .hylo(typeOfSubfield, isAddress: true)
  }

}

extension IRSubfield: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "subfield \(printer.show(base)) at \(list: path)"
  }

}
