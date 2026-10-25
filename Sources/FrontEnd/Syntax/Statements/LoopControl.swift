import Archivist

/// A loop control statement, exiting from a loop or moving to its next iteration.
@Archivable
public struct LoopControl: Statement {

  /// The semantics of a loop control statement.
  @Archivable
  public enum Action: Hashable, Sendable {

    /// Exits from the loop.
    case `break`

    /// Moves to the next iteration.
    case `continue`

  }

  /// The semantics of this control statement.
  public let action: Action

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(action: Action, site: SourceSpan) {
    self.action = action
    self.site = site
  }

}

extension LoopControl: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    String(describing: action)
  }

}
