/// The type of an entity in Hylo IR.
public enum IRType: Hashable, Sendable {

  /// A type expressed in source-level Hylo.
  case lowered(AnyTypeIdentity, isAddress: Bool)

  /// The type of an IR value.
  case same(as: IRValue)

  /// The type of the dereferencing of an IR value.
  case dereferenced(IRValue)

  /// The type of an instruction that doesn't produce any value.
  case nothing

  /// Returns the type of an instance of `t`, which contains no aliases.
  public static func addressOf(_ t: AnyTypeIdentity) -> Self {
    assert(!t[.hasAliases])
    return .lowered(t, isAddress: true)
  }

}

extension IRType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .lowered(let t, isAddress: true):
      let s = printer.show(t)
      return (s.contains(where: \.isWhitespace) && !s.isParenthesized) ? "(\(s))&" : "\(s)&"
    case .lowered(let t, isAddress: false):
      return printer.show(t)
    case .same(let i):
      return "$same(as: \(printer.show(i)))"
    case .dereferenced(let i):
      return "$dereferenced(\(printer.show(i)))"
    case .nothing:
      return "$nothing"
    }
  }

}
