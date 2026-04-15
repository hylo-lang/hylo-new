import Archivist

/// The application of an abstraction to context arguments.
@Archivable
public struct StaticCall: Expression {

  /// The abstraction being applied.
  public let callee: ExpressionIdentity

  /// The arguments passed to the abstraction.
  public let arguments: [ExpressionIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(callee: ExpressionIdentity, arguments: [ExpressionIdentity], site: SourceSpan) {
    self.callee = callee
    self.arguments = arguments
    self.site = site
  }

  /// Returns a copy of `self` with the arguments replaced.
  public func replacing(arguments: [ExpressionIdentity]) -> StaticCall {
    .init(callee: callee, arguments: arguments, site: site)
  }

}

extension StaticCall: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(callee))<\(printer.show(arguments))>"
  }

}
