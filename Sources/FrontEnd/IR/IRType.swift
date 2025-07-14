/// The type of an entity in Hylo IR.
public enum IRType: Hashable, Sendable {

  /// A type expressed in source-level Hylo.
  case hylo(AnyTypeIdentity, isAddress: Bool)

  /// The type of an IR value.
  case same(as: IRValue)

  /// The type of the dereferencing of an IR value.
  case dereferenced(IRValue)

  /// The type of an instruction that doesn't produce any value.
  case nothing

  /// Returns the type of an instance of `t`, which contains no aliases.
  public static func addressOf(_ t: AnyTypeIdentity) -> Self {
    assert(!t[.hasAliases])
    return .hylo(t, isAddress: true)
  }

}

extension IRType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .hylo(let t, let isAddress):
      let s = printer.show(t)
      return isAddress ? "(\(s))&" : s
    case .same(let i):
      return "$same(as: \(printer.show(i)))"
    case .dereferenced(let i):
      return "$dereferenced(\(printer.show(i)))"
    case .nothing:
      return "$nothing"
    }
  }

}
