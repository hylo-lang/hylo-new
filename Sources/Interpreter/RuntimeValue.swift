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
