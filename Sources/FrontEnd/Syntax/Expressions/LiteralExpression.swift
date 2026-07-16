/// A literal expression.
public protocol LiteralExpression: Expression {
  
  /// The literal type associated with `Self`.
  static var literalType: LiteralType { get }

  /// The inferred type of a literal expression in the absence of external constraints.
  static var defaultType: Program.StandardLibraryEntity { get }

  /// The trait whose conformers can be expressed by `Self`.
  static var literalTrait: Program.StandardLibraryEntity { get }

  /// The label of the constructor accepting a literal expression.
  static var constructorLabel: String { get }

}
