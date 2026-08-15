import BigInt
import FrontEnd

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
    precondition(b > 0)
    precondition(a > 0)

    var unsignedRepresentation = twosComplementRepresentation(n, size: b)
    var bytes = [UInt8](repeating: 0, count: b)
    for i in 0..<b {
      bytes[i] = UInt8(truncatingIfNeeded: unsignedRepresentation)
      unsignedRepresentation >>= 8
    }

    self.init(bytes: bytes, havingAlignment: a)
  }
}

/// Returns the unsigned representation of `n` using `b` bytes in two's-complement form.
///
/// - Precondition: `n` must be representable as a signed integer in `b` bytes.
func twosComplementRepresentation(_ n: BigInt, size b: Int) -> BigUInt {
  var unsignedRepresentation = n.magnitude
  if n.sign == .minus {
    let maximumUnsignedValue = BigUInt(1) << (8 * b)
    unsignedRepresentation = maximumUnsignedValue - unsignedRepresentation
  }
  return unsignedRepresentation
}
