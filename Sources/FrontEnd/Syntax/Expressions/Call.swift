import Archivist

/// The application of a function, method, or subscript.
@Archivable
public struct Call: Expression {

  /// The way in which an entity is being applied.
  @Archivable
  public enum Style: UInt8, Hashable, Sendable {

    /// Entity called with parentheses.
    case parenthesized

    /// Entity called with brackets.
    case bracketed

    /// Creates the style with which an entity introduced by `i` should be applied.
    public init(_ i: FunctionDeclaration.Introducer) {
      self = (i == .subscript) ? .bracketed : .parenthesized
    }

  }

  /// The function or method being applied.
  public let callee: ExpressionIdentity

  /// The arguments passed to the callee.
  public let arguments: [LabeledExpression]

  /// The way in which the arguments are passed.
  public let style: Style

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    callee: ExpressionIdentity,
    arguments: [LabeledExpression],
    style: Style,
    site: SourceSpan
  ) {
    self.callee = callee
    self.arguments = arguments
    self.style = style
    self.site = site
  }

  /// Returns a copy of `self` with the callee replaced.
  public func replacing(callee: ExpressionIdentity) -> Call {
    .init(callee: callee, arguments: arguments, style: style, site: site)
  }

  /// Returns a copy of `self` with the arguments replaced.
  public func replacing(arguments: [LabeledExpression]) -> Call {
    .init(callee: callee, arguments: arguments, style: style, site: site)
  }

  /// The labels of the arguments.
  public var labels: [String?] {
    arguments.map(\.label?.value)
  }

}

extension Call: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let c = printer.show(callee)
    let a = arguments.map({ (a) in printer.show(a) }).joined(separator: ", ")
    switch style {
    case .parenthesized:
      return "\(c)(\(a))"
    case .bracketed:
      return "\(c)[\(a)]"
    }
  }

}
