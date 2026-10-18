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
  var asUInt8: UInt8 {
    switch self {
    case .i8(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(8)`.")
    }
  }

  /// The 16-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(16)`.
  var asUInt16: UInt16 {
    switch self {
    case .i16(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(16)`.")
    }
  }

  /// The 32-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(32)`.
  var asUInt32: UInt32 {
    switch self {
    case .i32(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(32)`.")
    }
  }

  /// The 64-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(64)`.
  var asUInt64: UInt64 {
    switch self {
    case .i64(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(64)`.")
    }
  }

  /// The 128-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(128)`.
  var asUInt128: UInt128 {
    switch self {
    case .i128(let x): x
    default: preconditionFailure("Not an instance of `MachineType.i(128)`.")
    }
  }

}

extension BuiltinValue {

  /// Creates a `w`-bit integer with the two's-complement representation of `n`.
  public init(integer n: BigInt, bitWidth w: UInt8) {
    precondition(w == 1 || w == 8 || w == 16 || w == 32 || w == 64 || w == 128)
    precondition(n.isRepresentable(asIntegerHavingBitWidth: w))

    self =
      switch w {
      case 1: .i1(n != 0)
      case 8: .i8(UInt8(truncatingIfNeeded: n))
      case 16: .i16(UInt16(truncatingIfNeeded: n))
      case 32: .i32(UInt32(truncatingIfNeeded: n))
      case 64: .i64(UInt64(truncatingIfNeeded: n))
      case 128: .i128(UInt128(truncatingIfNeeded: n))
      default: preconditionFailure("Unknown integer bit width.")
      }
  }

  /// Creates an instance of `MachineType.i(1)` having value `b`.
  public init(bool b: Bool) {
    self = .i1(b)
  }

}

extension BuiltinValue {

  /// Returns the byte representation of `self` as a value of type `t`,
  /// laid out according to the layouts provided by `c`.
  ///
  /// - Precondition: `self` is an instance of `t`.
  public func byteRepresentation(
    asValueOf t: MachineType,
    laidOutUsing c: inout LayoutComputer
  ) -> [UInt8] {
    let o = c.abi.byteOrder
    let w = c.abi.bitsInAPointer

    return switch t {
    case .i(let n): byteRepresentation(asIntegerHavingBitWidth: n, orderedBy: o)
    case .word: byteRepresentation(asIntegerHavingBitWidth: UInt8(w), orderedBy: o)
    default: unimplemented("floats, and ptr are not supported yet.")
    }

  }

  /// Returns the byte representation of `self` as a `w`-bit integer, ordered by `o`.
  private func byteRepresentation(
    asIntegerHavingBitWidth w: UInt8,
    orderedBy o: Endianness
  ) -> [UInt8] {
    var r =
      switch w {
      case 1: withUnsafeBytes(of: asBool) { Array($0) }
      case 8: withUnsafeBytes(of: asUInt8) { Array($0) }
      case 16: withUnsafeBytes(of: asUInt16) { Array($0) }
      case 32: withUnsafeBytes(of: asUInt32) { Array($0) }
      case 64: withUnsafeBytes(of: asUInt64) { Array($0) }
      case 128: withUnsafeBytes(of: asUInt128) { Array($0) }
      default: preconditionFailure("Unknown integer bit width.")
      }

    if o != .host { r.reverse() }
    return r
  }

}
