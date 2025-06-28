import Archivist

/// A built-in machine type.
@Archivable
public enum MachineType: TypeTree {

  /// A machine integer type.
  ///
  /// This type represents the target's integer types. A machine integer may be of any bit width
  /// and does not specify signedness.
  case i(UInt8)

  /// An alias for `.i(n)` where `n` is the width of `.ptr`.
  case word

  /// A machine 16-bit floating-point type (specifically, "binary16" in IEEE 754).
  case float16

  /// A machine 32-bit floating-point type (specifically, "binary32" in IEEE 754).
  case float32

  /// A machine 64-bit floating-point type (specifically, "binary64" in IEEE 754).
  case float64

  /// A machine 128-bit floating-point type (specifically, "binary128" in IEEE 754).
  case float128

  /// A machine opaque pointer.
  case ptr

  /// `true` iff `self` is `.i` or `.word`.
  public var isInteger: Bool {
    switch self {
    case .i, .word:
      return true
    default:
      return false
    }
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension MachineType: CustomStringConvertible {

  public var description: String {
    switch self {
    case .i(let bitWidth):
      return "i\(bitWidth)"
    case .word:
      return "word"
    case .float16:
      return "float16"
    case .float32:
      return "float32"
    case .float64:
      return "float64"
    case .float128:
      return "float128"
    case .ptr:
      return "ptr"
    }
  }

}

extension MachineType: LosslessStringConvertible {

  /// Creates an instance from its description.
  public init?<S: StringProtocol>(_ description: S) {
    switch description {
    case "word":
      self = .word
    case "float16":
      self = .float16
    case "float32":
      self = .float32
    case "float64":
      self = .float64
    case "float128":
      self = .float128
    case "ptr":
      self = .ptr
    case _ where description.starts(with: "i"):
      self.init(i: description.dropFirst())
    default:
      return nil
    }
  }

  /// Creates `.i(n)` where `n` is a non-negative integer pased from `s`.
  private init?<S: StringProtocol>(i s: S) {
    if let bitWidth = UInt8(s) {
      self = .i(bitWidth)
    } else {
      return nil
    }
  }

}

extension MachineType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    self.description
  }

}
