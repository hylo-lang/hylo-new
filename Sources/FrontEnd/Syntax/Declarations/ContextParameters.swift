import Archivist

/// A clause describing context parameters and contextual constraints (aka usings).
@Archivable
public struct ContextParameters: Equatable, Sendable {

  /// The type parameters of the list.
  public let types: [GenericParameterDeclaration.ID]

  /// The constraints in the clause.
  public let usings: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    types: [GenericParameterDeclaration.ID],
    usings: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.types = types
    self.usings = usings
    self.site = site
  }

  /// `true` iff `self` doesn't contain any parameter or constraint.
  public var isEmpty: Bool {
    types.isEmpty && usings.isEmpty
  }

  /// Returns an empty clause anchored at `site`.
  public static func empty(at site: SourceSpan) -> ContextParameters {
    .init(types: [], usings: [], site: site)
  }

}

extension ContextParameters: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if usings.isEmpty {
      return "<\(printer.show(types))>"
    } else {
      return "<\(printer.show(types)) where \(printer.show(usings))>"
    }
  }

}
