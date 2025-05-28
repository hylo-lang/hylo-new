import Archivist

/// The expression of a lambda.
@Archivable
public struct Lambda: Expression {

  /// The underlying function.
  public let function: FunctionDeclaration.ID

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(function: FunctionDeclaration.ID, site: SourceSpan) {
    self.function = function
    self.site = site
  }

}

extension Lambda: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(function)
  }

}
