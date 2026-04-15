/// An alignment requirement.
public enum IRAlignment: Hashable, Sendable {

  /// The preferred alignment of the type for which this value is used.
  case preferred

}

extension IRAlignment: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .preferred:
      return "#preferred"
    }
  }

}
