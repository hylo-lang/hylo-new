/// A literal expression.
public protocol LiteralExpression: Expression {
  
  /// The literal type associated with `Self`.
  static var literalType: LiteralType { get }

}