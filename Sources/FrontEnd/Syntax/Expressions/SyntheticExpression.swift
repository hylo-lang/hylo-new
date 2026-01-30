import Archivist

/// The expression of a value synthesized during elaboration.
@Archivable
public struct SyntheticExpression: Expression {

  /// The synthesized expression.
  public let value: WitnessExpression

  /// The site to which the synthesized expression is anchored.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(value: WitnessExpression, site: SourceSpan) {
    self.value = value
    self.site = site
  }

}

extension SyntheticExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(value)
  }

}
