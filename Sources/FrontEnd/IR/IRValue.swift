/// A value in Hylo IR.
public enum IRValue: Hashable, Sendable {

  /// The `i`-th parameter of a function.
  case parameter(Int)

  /// The register assigned by an instruction.
  case register(AnyInstructionIdentity)

  /// A constant integer.
  case word(Int, MachineType.ID)

  /// A pointer to a function.
  case function(IRFunction.Name, FunctionPointer.ID)

  /// The payload of `self` iff it denotes a register.
  public var register: AnyInstructionIdentity? {
    if case .register(let i) = self {
      return i
    } else {
      return nil
    }
  }


}

extension IRValue: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .parameter(let i):
      return "%p\(i)"
    case .register(let i):
      return "%r\(i.rawValue)"
    case .word(let n, let t):
      return "\(printer.show(t)) \(n)"
    case .function(let n, _):
      return printer.show(n)
    }
  }

}

