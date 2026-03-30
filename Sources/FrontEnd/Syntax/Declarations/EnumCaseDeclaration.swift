import Archivist

/// The declaration of a case constructor in an enumeration.
///
/// An enum case can only occur as a non-static member in an enum and it defines a constructor for
/// that enum. It also defines a member of the underlying sum type of the enum unless the latter
/// has a custom raw representation.
@Archivable
public struct EnumCaseDeclaration: Declaration, Scope {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared constructor.
  public let identifier: Parsed<String>

  /// The parameters of the declared constructor.
  public let parameters: [ParameterDeclaration.ID]

  /// The definition of the constructor, if any.
  public let body: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Token,
    identifier: Parsed<String>,
    parameters: [ParameterDeclaration.ID],
    body: ExpressionIdentity?,
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.identifier = identifier
    self.parameters = parameters
    self.body = body
    self.site = site
  }

}

extension EnumCaseDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "case \(identifier.value)"
    if !parameters.isEmpty {
      result.append("(\(printer.show(parameters)))")
    }
    if let b = body {
      result.append(" = \(printer.show(b))")
    }
    return result
  }

}
