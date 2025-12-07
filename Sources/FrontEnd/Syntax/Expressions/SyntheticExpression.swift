import Archivist

/// The expression of a value synthesized during elaboration.
@Archivable
public struct SyntheticExpression: Expression {

  /// The value of a synthetic expression.
  @Archivable
  public enum Value: Equatable, Sendable {

    /// A witness inferred by implicit resolution.
    case witness(WitnessExpression)

    /// A default argument.
    case defaultArgument(ExpressionIdentity)

  }

  /// The synthesized expression.
  public let value: Value

  /// The site at which the synthesized expression is anchored.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(value: Value, site: SourceSpan) {
    self.value = value
    self.site = site
  }

}

extension SyntheticExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch value {
    case .witness(let w):
      return printer.show(w)
    case .defaultArgument(let e):
      return printer.show(e)
    }
  }

}
