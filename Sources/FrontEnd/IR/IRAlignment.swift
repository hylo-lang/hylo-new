/// An alignment requirement.
public enum IRAlignment: Hashable, Sendable {

  /// The preferred alignment of a type on the target.
  case align(of: AnyTypeIdentity)

}

extension IRAlignment: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .align(let t):
      return "#align(of: \(printer.show(t)))"
    }
  }

}
