import BigInt
import FrontEnd
import Utilities

/// The value of a `MachineType` instance.
enum BuiltinValue: Regular {

  /// 1-bit builtin integer type.
  case i1(Bool)

  /// 8-bit builtin integer type.
  case i8(UInt8)

  /// 16-bit builtin integer type.
  case i16(UInt16)

  /// 32-bit builtin integer type.
  case i32(UInt32)

  /// 64-bit builtin integer type.
  case i64(UInt64)

  /// 128-bit builtin integer type.
  case i128(UInt128)

  // TODO: support floats, word, ptr, module.

  /// The boolean value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(1)`.
  var asBool: Bool {
    switch self {
    case .i1(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(1)`.")
    }
  }

  /// The 8-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(8)`.
  var asI8: UInt8 {
    switch self {
    case .i8(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(8)`.")
    }
  }

  /// The 16-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(16)`.
  var asI16: UInt16 {
    switch self {
    case .i16(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(16)`.")
    }
  }

  /// The 32-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(32)`.
  var asI32: UInt32 {
    switch self {
    case .i32(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(32)`.")
    }
  }

  /// The 64-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(64)`.
  var asI64: UInt64 {
    switch self {
    case .i64(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(64)`.")
    }
  }

  /// The 128-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(128)`.
  var asI128: UInt128 {
    switch self {
    case .i128(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(128)`.")
    }
  }

}

extension BuiltinValue {

  /// Creates a `w`-bit integer having value `n`.
  ///
  /// - Precondition: `n >= 0`.
  public init(integer n: BigInt, bitWidth w: Int) {
    precondition(w == 8 || w == 16 || w == 32 || w == 64 || w == 128)

    self =
      switch w {
      case 8: .i8(UInt8(n))
      case 16: .i16(UInt16(n))
      case 32: .i32(UInt32(n))
      case 64: .i64(UInt64(n))
      case 128: .i128(UInt128(n))
      default: preconditionFailure("Unknown integer bit width.")
      }
  }

  /// Creates an instance of `MachineType.i(1)` having value `b`.
  public init(bool b: Bool) {
    self = .i1(b)
  }

}

extension BuiltinValue {

  /// Returns the byte representation of `self` as a value of type `t`.
  ///
  /// - Precondition: `self` is an instance of `t`.
  public func byteRepresentation(as t: MachineType) -> [UInt8] {
    // TODO: Use endianness to figure out the byte representation.
    switch t {
    case .i(let n):
      switch n {
      case 1: withUnsafeBytes(of: asBool) { Array($0) }
      case 8: withUnsafeBytes(of: asI8) { Array($0) }
      case 16: withUnsafeBytes(of: asI16) { Array($0) }
      case 32: withUnsafeBytes(of: asI32) { Array($0) }
      case 64: withUnsafeBytes(of: asI64) { Array($0) }
      case 128: withUnsafeBytes(of: asI128) { Array($0) }
      default: preconditionFailure("Unknown integer bit width.")
      }
    default: unimplemented("float, ptr, and word are not supported yet.")
    }
  }

}
