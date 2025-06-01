import Archivist

/// A clause describing contextual parameters and contextual constraints taken at compile-time.
@Archivable
public struct ContextParameters: Equatable, Sendable {

  /// The explicit parameters of the list.
  public let explicit: [GenericParameterDeclaration.ID]

  /// The constraints in the clause.
  public let implicit: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    explicit: [GenericParameterDeclaration.ID],
    implicit: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.explicit = explicit
    self.implicit = implicit
    self.site = site
  }

  /// `true` iff `self` doesn't contain any parameter or constraint.
  public var isEmpty: Bool {
    explicit.isEmpty && implicit.isEmpty
  }

  /// Returns an empty clause anchored at `site`.
  public static func empty(at site: SourceSpan) -> ContextParameters {
    .init(explicit: [], implicit: [], site: site)
  }

}

extension ContextParameters: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if implicit.isEmpty {
      return "<\(printer.show(explicit))>"
    } else {
      return "<\(printer.show(explicit)) where \(printer.show(implicit))>"
    }
  }

}
