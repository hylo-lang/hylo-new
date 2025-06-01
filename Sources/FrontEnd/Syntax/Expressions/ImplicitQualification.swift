import Archivist

/// The implicit qualification of a name expression prefixed by a dot (e.g., `.bar`).
@Archivable
public struct ImplicitQualification: Expression {

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(site: SourceSpan) {
    self.site = site
  }

}

extension ImplicitQualification: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    ""
  }

}
