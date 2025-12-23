/// The value of a register in an abstract interpreter.
internal enum AbstractValue<Domain: AbstractDomain>: Hashable, Sendable {

  /// An abstract location.
  case place(AbstractPlace)

  /// An abstract object.
  case object(AbstractObject<Domain>)

  /// The payload of `self` iff it is `.place`.
  internal var place: AbstractPlace? {
    if case .place(let p) = self {
      return p
    } else {
      return nil
    }
  }

  /// The payload of `self` iff it is `.place`.
  internal var object: AbstractObject<Domain>? {
    if case .object(let o) = self {
      return o
    } else {
      return nil
    }
  }

  /// Returns `l` merged with `r`.
  internal static func && (l: Self, r: Self) -> Self {
    switch (l, r) {
    case (.place(let a), .place(let b)):
      return .place(a && b)
    case (.object(let a), .object(let b)):
      return .object(a && b)
    default:
      fatalError("invalid merge")
    }
  }

}

extension AbstractValue: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .place(let p):
      return printer.show(p)
    case .object(let o):
      return printer.show(o)
    }
  }

}
