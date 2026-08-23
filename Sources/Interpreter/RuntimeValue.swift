import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
struct RuntimeValue {

  /// The bytes of the value preceded by zero or more bytes of padding to satisfy
  /// its alignment.
  private let storage: [UInt8]

  /// The number of bytes before the value logically begins.
  private let baseOffset: Int

  /// Creates an instance having bytes `bs` and alignment `a`.
  public init(bytes bs: [UInt8], havingAlignment a: Int) {
    var (s, o) = Array.aligned(
      repeating: 0 as UInt8,
      count: bs.count,
      alignment: a
    )
    s[o...] = bs[...]
    baseOffset = o
    storage = s
  }

  /// Raw bytes of the value.
  public var bytes: ArraySlice<UInt8> { storage[baseOffset...] }
}

extension RuntimeValue {

  /// Creates a `w`-bit integer having value `n` and alignment `a`.
  public init(integer n: BigInt, bitWidth w: Int, alignment a: Int) {
    precondition(w == 8 || w == 16 || w == 32 || w == 64 || w == 128)
    precondition(a > 0)

    let r = twosComplementRepresentation(n)
    self.init(bytes: byteRepresentation(r, bitWidth: w), havingAlignment: a)
  }

  /// Creates an instance of `MachineType.i(1)` having value `b` and layout `l`.
  public init(_ b: Bool, havingLayout l: TypeLayout.Bytes) {
    let w = l.size * 8
    precondition(w == 8 || w == 16 || w == 32 || w == 64 || w == 128)

    self.init(integer: 1, bitWidth: w, alignment: l.alignment)
  }

  /// Returns the result of calling `body` on a pointer to the value's bytes
  /// interpreted as a `T` instance.
  ///
  /// - Precondition: `self` is aligned for `T`.
  internal func withUnsafePointer<T, R>(
    to _: T.Type, _ body: (UnsafePointer<T>) -> R
  ) -> R {
    precondition(MemoryLayout<T>.size <= bytes.count)
    return bytes.withUnsafeBytes { p in
      body(p.baseAddress!.assumingMemoryBound(to: T.self))
    }
  }

  /// The boolean value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(1)`.
  public var bool: Bool {
    withUnsafePointer(to: UInt8.self) { $0.pointee != 0 }
  }

  /// The 8-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(8)`.
  public var i8: UInt8 {
    withUnsafePointer(to: UInt8.self) { $0.pointee }
  }

  /// The 16-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(16)`.
  public var i16: UInt16 {
    withUnsafePointer(to: UInt16.self) { $0.pointee }
  }

  /// The 32-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(32)`.
  public var i32: UInt32 {
    withUnsafePointer(to: UInt32.self) { $0.pointee }
  }

  /// The 64-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(64)`.
  public var i64: UInt64 {
    withUnsafePointer(to: UInt64.self) { $0.pointee }
  }

  /// The 128-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(128)`.
  public var i128: UInt128 {
    withUnsafePointer(to: UInt128.self) { $0.pointee }
  }

}

/// Returns an in-memory byte representation of the low-order `w` bits of `n`.
internal func byteRepresentation(_ n: UInt128, bitWidth w: Int) -> [UInt8] {
  precondition(w == 8 || w == 16 || w == 32 || w == 64 || w == 128)
  switch w {
  case 8:
    let value = UInt8(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 16:
    let value = UInt16(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 32:
    let value = UInt32(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 64:
    let value = UInt64(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 128:
    return withUnsafeBytes(of: n, Array.init)

  default:
    unreachable()
  }
}

/// Returns 128-bit two's-complement representation of `n`.
///
/// - Precondition: `n` must be representable as a signed 128-bit integer.
internal func twosComplementRepresentation(_ n: BigInt) -> UInt128 {
  if n.sign == .plus {
    return UInt128(n.magnitude)
  }

  return UInt128.max - UInt128(n.magnitude) + 1
}
