import Archivist

/// Creates a type witness using a runtime type constructor.
@Archivable
public struct IRTypeWitness: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The constructor of the witness being formed.
  public var constructor: AnyTypeIdentity

  /// The type of the type witness being being formed.
  public let witnessType: TypeWitness.ID

  /// Creates an instance with the given properties.
  public init(
    constructor: AnyTypeIdentity, arguments: [IRValue], witnessType: TypeWitness.ID,
    anchor: Anchor
  ) {
    self.operands = arguments
    self.anchor = anchor
    self.constructor = constructor
    self.witnessType = witnessType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.constructor = other.constructor
    self.witnessType = other.witnessType
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(witnessType.erased)
  }

}

extension IRTypeWitness: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let xs = operands.map({ (o) in printer.show(o) }).joined(separator: ", ")
    return "type_witness \(printer.show(constructor))(\(xs))"
  }

}
