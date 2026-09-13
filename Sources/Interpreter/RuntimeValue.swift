import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
struct RuntimeValue {

  /// Raw bytes of the value.
  public let bytes: ArraySlice<UInt8>

}

extension RuntimeValue {

  /// Creates a `w`-bit integer having value `n` and the given byte order.
  public init(integer n: BigInt, bitWidth w: Int, byteOrder: Endianness) {
    precondition(w == 8 || w == 16 || w == 32 || w == 64 || w == 128)

    let r = twosComplementRepresentation(n)
    self.init(bytes: byteRepresentation(r, bitWidth: w, inByteOrder: byteOrder)[...])
  }

  /// Creates an instance of `MachineType.i(1)` having value `b`.
  public init(bool b: Bool) {
    // Byte order doesn't matter for single-byte types.
    self.init(integer: b ? 1 : 0, bitWidth: 8, byteOrder: .little)
  }

  /// The boolean value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(1)`.
  public var asBool: Bool {
    bytes.first! != 0
  }

  /// The 8-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(8)`.
  public var asI8: UInt8 {
    bytes.first!
  }

  /// The 16-bit unsigned value, assuming byte order `o`.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(16)`.
  public func asI16(assumingByteOrder o: Endianness) -> UInt16 {
    integerValue(as: UInt16.self, assumingByteOrder: o)
  }

  /// The 32-bit unsigned value, assuming byte order `o`.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(32)`.
  public func asI32(assumingByteOrder o: Endianness) -> UInt32 {
    integerValue(as: UInt32.self, assumingByteOrder: o)
  }

  /// The 64-bit unsigned value, assuming byte order `o`.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(64)`.
  public func asI64(assumingByteOrder o: Endianness) -> UInt64 {
    integerValue(as: UInt64.self, assumingByteOrder: o)
  }

  // TODO: uncomment when 128-bit integer is supported.
  //
  // /// The 128-bit unsigned value, assuming byte order `o`.
  // ///
  // /// - Precondition: `self` is an instance of `MachineType.i(128)`.
  // public func asI128(assumingByteOrder o: Endianness) -> UInt128 {
  //   integerValue(as: UInt128.self, assumingByteOrder: o)
  // }

  /// Returns the bytes of `self` interpreted as an integer of type `t`, assuming
  /// they are arranged in byte order `o`.
  private func integerValue<T: FixedWidthInteger>(
    as t: T.Type, assumingByteOrder o: Endianness
  ) -> T {
    precondition(bytes.count == T.bitWidth / 8)

    return (0..<bytes.count).reduce(0) { result, i in
      let j = byteIndex(
        forLeastSignificantByte: i,
        byteCount: bytes.count,
        inByteOrder: o)
      return result | T(bytes[j]) << (i * 8)
    }
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

/// Returns the in-memory byte representation of the low-order `w` bits of `n`,
/// arranged in `byteOrder`.
internal func byteRepresentation(
  _ n: UInt128,
  bitWidth w: Int,
  inByteOrder byteOrder: Endianness
) -> [UInt8] {
  precondition(w == 8 || w == 16 || w == 32 || w == 64 || w == 128)

  let byteCount = w / 8
  return (0..<byteCount).map { i in
    let j = byteIndex(
      forLeastSignificantByte: i,
      byteCount: byteCount,
      inByteOrder: byteOrder)
    return UInt8(truncatingIfNeeded: n >> (j * 8))
  }
}

/// Returns the index at which the `i`th least-significant byte is arranged in
/// `byteOrder`.
private func byteIndex(
  forLeastSignificantByte i: Int,
  byteCount: Int,
  inByteOrder byteOrder: Endianness
) -> Int {
  switch byteOrder {
  case .little:
    return i
  case .big:
    return byteCount - 1 - i
  }
}
