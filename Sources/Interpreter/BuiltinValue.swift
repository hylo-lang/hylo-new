import Archivist
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

  // TODO: support floats and ptr.

  /// The value of the stored `i1`, or `nil` if `self` does not match `.i1(_)`
  public var i1: Bool? {
    switch self {
    case .i1(let v): v
    default: nil
    }
  }

  /// The value of the stored `i8`, or `nil` if `self` does not match `.i8(_)`
  public var i8: UInt8? {
    switch self {
    case .i8(let v): v
    default: nil
    }
  }

  /// The value of the stored `i16`, or `nil` if `self` does not match `.i16(_)`
  public var i16: UInt16? {
    switch self {
    case .i16(let v): v
    default: nil
    }
  }

  /// The value of the stored `i32`, or `nil` if `self` does not match `.i32(_)`
  public var i32: UInt32? {
    switch self {
    case .i32(let v): v
    default: nil
    }
  }

  /// The value of the stored `i64`, or `nil` if `self` does not match `.i64(_)`
  public var i64: UInt64? {
    switch self {
    case .i64(let v): v
    default: nil
    }
  }

  /// The value of the stored `i128`, or `nil` if `self` does not match `.i128(_)`
  public var i128: UInt128? {
    switch self {
    case .i128(let v): v
    default: nil
    }
  }

  /// The magnitude of stored integer value.
  public var asUInt128: UInt128 {
    switch self {
    case .i8(let v): UInt128(v)
    case .i16(let v): UInt128(v)
    case .i32(let v): UInt128(v)
    case .i64(let v): UInt128(v)
    case .i128(let v): UInt128(v)
    default: unreachable()
    }
  }

  /// The type of the stored value.
  public var type: MachineType {
    switch self {
    case .i1(_): MachineType.i(1)
    case .i8(_): MachineType.i(8)
    case .i16(_): MachineType.i(16)
    case .i32(_): MachineType.i(32)
    case .i64(_): MachineType.i(64)
    case .i128(_): MachineType.i(128)
    }
  }

}

extension BuiltinValue {

  /// Creates a `w`-bit integer storing the two's-complement representation of `n`.
  public init(_ n: BigInt, bitWidth w: UInt8) {
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
  public init(_ b: Bool) {
    self = .i1(b)
  }

  /// Creates a value of type `t` by interpreting its byte representation `storage`
  /// according to the layout provided by `layouts`.
  public init(
    _ storage: ArraySlice<UInt8>,
    type t: MachineType,
    layouts: inout LayoutComputer
  ) {
    switch t {
    case .i(let bitWidth):
      self = .init(
        BigInt(unsignedFrom: storage, storedIn: layouts.abi.byteOrder),
        bitWidth: bitWidth
      )
    case .word:
      self = .init(
        BigInt(unsignedFrom: storage, storedIn: layouts.abi.byteOrder),
        bitWidth: layouts.abi.bitsInAPointer
      )
    default: unimplemented("floats and ptr are not supported yet.")
    }
  }

}

extension BuiltinValue {

  /// Returns the memory representation of `self` as laid out by `typeLayouts`.
  public func bytes(
    laidOutUsing typeLayouts: inout LayoutComputer
  ) -> [UInt8] {
    var bytes =
      switch self {
      case .i1(let v): withUnsafeBytes(of: v) { Array($0) }
      case .i8(let v): withUnsafeBytes(of: v) { Array($0) }
      case .i16(let v): withUnsafeBytes(of: v) { Array($0) }
      case .i32(let v): withUnsafeBytes(of: v) { Array($0) }
      case .i64(let v): withUnsafeBytes(of: v) { Array($0) }
      case .i128(let v): withUnsafeBytes(of: v) { Array($0) }
      }

    if typeLayouts.abi.byteOrder != .host { bytes.reverse() }
    return bytes
  }

}
