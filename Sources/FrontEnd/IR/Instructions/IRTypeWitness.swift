/// Creates a type witness using a runtime type constructor.
public struct IRTypeWitness: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// An existential type describing the type witness being constructed.
  public var constructor: UniversalType.ID

  /// The type of the type witness being constructed.
  public let typeOfApplication: TypeWitness.ID

  /// Creates an instance with the given properties.
  public init(
    constructor: UniversalType.ID, arguments: [IRValue], typeOfApplication: TypeWitness.ID,
    anchor: Anchor
  ) {
    self.operands = arguments
    self.anchor = anchor
    self.constructor = constructor
    self.typeOfApplication = typeOfApplication
  }

  /// Creates a copy of `other`, substituting its properties with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in ss[o] })
    self.anchor = other.anchor
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
    let xs = operands.map({ (o) in printer.show(o) }).joined(separator: ", ")
    return "type_witness \(printer.show(constructor))(\(xs))"
  }

}
