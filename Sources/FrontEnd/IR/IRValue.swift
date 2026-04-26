import BigInt

/// A value in Hylo IR.
public enum IRValue: Hashable, Sendable {

  /// The `i`-th parameter of a function.
  case parameter(Int)

  /// The register assigned by an instruction.
  case register(AnyInstructionIdentity)

  /// A constant integer.
  indirect case integer(BigInt, MachineType.ID)

  /// A constant floating point number.
  ///
  /// `literal` contains the string representation of the floating point number without underscores.
  indirect case floatingPoint(literal: String, MachineType.ID)

  /// A reference to a lowered function.
  indirect case function(IRFunction.Name, AnyTypeIdentity)

  /// A type witness.
  indirect case type(AnyTypeIdentity, TypeWitness.ID)

  /// A "poison value", representing the result of an erroneous operation.
  indirect case poison(IRType)

  /// `true` iff `self` is a constant.
  public var isConstant: Bool {
    switch self {
    case .integer, .function, .type:
      return true
    default:
      return false
    }
  }

  /// `true` iff `self` is a poison value.
  public var isPoison: Bool {
    if case .poison = self {
      return true
    } else {
      return false
    }
  }

  /// The payload of `self` iff it denotes a parameter.
  public var parameter: Int? {
    if case .parameter(let i) = self {
      return i
    } else {
      return nil
    }
  }

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
      return "%r\(i.address.rawValue)"
    case .integer(let n, let t):
      return "\(printer.show(t)) \(n)"
    case .floatingPoint(let f, let t):
      return "\(printer.show(t)) \(f)"
    case .function(let n, _):
      return printer.show(n)
    case .type(let t, _):
      return printer.show(t)
    case .poison:
      return "#!poison"
    }
  }

}

