/// The type of an entity in Hylo IR.
public enum IRType: Hashable, Sendable {

  /// The type of a place
  case place(AnyTypeIdentity)

  /// The type of a value held in register.
  case value(AnyTypeIdentity)

  /// The type of an IR value.
  case same(as: IRValue)

  /// The type of the dereferencing of an IR value.
  case dereferenced(IRValue)

  /// The type of an instruction that doesn't produce any value.
  case nothing

}

extension IRType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .place(let t):
      let s = printer.show(t)
      return (s.contains(where: \.isWhitespace) && !s.isParenthesized) ? "(\(s))&" : "\(s)&"
    case .value(let t):
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

extension TypeStore {

  /// Returns the IR type of a place holding instances of `t`.
  public mutating func ir(place t: AnyTypeIdentity) -> IRType {
    .place(dealiased(t))
  }

  /// Returns the IR type of an instance of `t` held in register.
  public mutating func ir(value t: AnyTypeIdentity) -> IRType {
    .value(dealiased(t))
  }

}
