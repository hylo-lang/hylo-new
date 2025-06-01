/// The description of the value denoted by an expression.
public indirect enum Denotation: Hashable, Sendable {

  /// A reference to an entity.
  case reference(Denotation?, DeclarationReference, AnyTypeIdentity)

}

extension Denotation: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .reference(.some(let q), let r, _):
      return printer.show(q) + "." + printer.show(r)
    case .reference(.none, let r, _):
      return printer.show(r)
    }
  }

}
