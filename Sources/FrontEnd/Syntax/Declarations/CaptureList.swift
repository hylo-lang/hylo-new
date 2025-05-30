import Archivist
import Utilities

/// A capture list in a function or subscript declaration.
@Archivable
public struct CaptureList: Equatable, Sendable {

  /// The explicit contents of the capture list.
  public let explicit: [BindingDeclaration.ID]

  /// `true` iff the list allows inferred captures.
  public let allowsInferredCaptures: Bool

  /// The site at which diagnostics about this list should be reported.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(explicit: [BindingDeclaration.ID], allowsInferredCaptures: Bool, site: SourceSpan) {
    self.explicit = explicit
    self.allowsInferredCaptures = allowsInferredCaptures
    self.site = site
  }

  /// Returns `true` iff the list has no explicit declaration and doesn't allows inferred captures.
  public var isEmpty: Bool {
    explicit.isEmpty && !allowsInferredCaptures
  }

  /// Returns an empty capture list for which diagnostics should be reported at `p`.
  internal static func empty(at p: SourcePosition) -> CaptureList {
    return .init(explicit: [], allowsInferredCaptures: false, site: .empty(at: p))
  }

  /// Returns a capture list that has no explicit contents, supports inferred captures, and for
  /// which diagnostics should be reported at `p`.
  internal static func inferred(at p: SourcePosition) -> CaptureList {
    return .init(explicit: [], allowsInferredCaptures: true, site: .empty(at: p))
  }

}

extension CaptureList: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var xs = explicit.map({ (x) in printer.show(x) })
    if allowsInferredCaptures {
      xs.append("...")
    }
    return "[\(list: xs)]"
  }

}
