import Archivist

/// A pattern that matches tuples.
@Archivable
public struct TuplePattern: Pattern {

  /// The elements of the pattern.
  public let elements: [PatternIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(elements: [PatternIdentity], site: SourceSpan) {
    self.elements = elements
    self.site = site
  }

}

extension TuplePattern: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if elements.count == 1 {
      return "(\(printer.show(elements)),)"
    } else {
      return "(\(printer.show(elements)))"
    }
  }

}
