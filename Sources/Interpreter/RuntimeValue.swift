import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
struct RuntimeValue {

  /// The bytes of value, preceded by zero or more bytes of padding to satisfy
  /// its alignment.
  private let storage: [UInt8]

  /// The number of bytes before the value logically begins.
  private let baseOffset: Int

  /// Creates an instance from its bytes representation `bytes`, with alignment `a`.
  public init(bytes: [UInt8], havingAlignment a: Int) {
    var (s, o) = Array.aligned(
      repeating: 0 as UInt8,
      count: bytes.count,
      alignment: a
    )
    s[o...] = bytes[...]
    baseOffset = o
    storage = s
  }

  /// Raw bytes of the value.
  public var bytes: ArraySlice<UInt8> { storage[baseOffset...] }
}

extension RuntimeValue {

  /// Creates an instance for an integer of size `b` bytes having value `n` and
  /// alignment `a`.
  public init(integer n: BigInt, size b: Int, alignment a: Int) {
    precondition(b == 1 || b == 2 || b == 4 || b == 8)
    precondition(a > 0)

    let unsignedRepresentation = twosComplementRepresentation(n, size: b)
    self.init(
      bytes: byteRepresentation(unsignedRepresentation, size: b),
      havingAlignment: a)
  }

}

/// Returns the in-memory representation of `n` as an unsigned integer of size `b` bytes.
internal func byteRepresentation(_ n: BigUInt, size b: Int) -> [UInt8] {
  precondition(b == 1 || b == 2 || b == 4 || b == 8)
  switch b {
  case 1:
    let value = UInt8(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 2:
    let value = UInt16(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 4:
    let value = UInt32(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  case 8:
    let value = UInt64(truncatingIfNeeded: n)
    return withUnsafeBytes(of: value, Array.init)

  default:
    unreachable()
  }
}

/// Returns the unsigned representation of `n` using `b` bytes in two's-complement form.
///
/// - Precondition: `n` must be representable as a signed integer in `b` bytes.
internal func twosComplementRepresentation(_ n: BigInt, size b: Int) -> BigUInt {
  var unsignedRepresentation = n.magnitude
  if n.sign == .minus {
    let maximumUnsignedValue = BigUInt(1) << (8 * b)
    unsignedRepresentation = maximumUnsignedValue - unsignedRepresentation
  }
  return unsignedRepresentation
}
