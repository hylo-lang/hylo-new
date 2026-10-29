import Archivist
import Utilities

/// Creates a type witness using a runtime type constructor.
@Archivable
public struct IRTypeWitness: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Either a universal type or a constant describing the witness being constructed.
  ///
  /// If `operands` is empty, then the instruction projects a witness of `constructor`, which may
  /// be any arbitrary type. Otherwise, `constructor` is a universal type denoting an abstraction
  /// taking as many parameters as the number of `operands`.
  public var constructor: AnyTypeIdentity

  /// The type of the type witness being constructed.
  public let typeOfApplication: TypeWitness.ID

  /// Creates an instance with the given properties.
  public init(
    constructor: AnyTypeIdentity, arguments: [IRValue], typeOfApplication: TypeWitness.ID,
    anchor: Anchor
  ) {
    self.operands = arguments
    self.anchor = anchor
    self.constructor = constructor
    self.typeOfApplication = typeOfApplication
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.constructor = other.constructor
    self.typeOfApplication = other.typeOfApplication
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(typeOfApplication.erased)
  }

}

extension IRTypeWitness: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let u = printer.program.types.cast(constructor, to: UniversalType.self) {
      let f = printer.show(printer.program.types[u].head)
      let a = operands.map({ (o) in printer.show(o) })
      return "type_witness \(f)(\(list: a))"
    } else {
      return "type_witness \(printer.show(constructor))"
    }
  }

}
