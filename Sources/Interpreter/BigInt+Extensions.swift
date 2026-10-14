import BigInt

extension BigInt {

  /// Creates an integer from the byte representation `bs` of an unsigned
  /// integer, ordered by `o`.
  init(byteRepresentation bs: some Collection<UInt8>, inByteOrder o: Endianness) {
    if o == .lsbFirst {
      self = .init(byteRepresentation: bs.reversed(), inByteOrder: .msbFirst)
    } else {
      self = bs.reduce(BigInt(0)) { r, c in
        (r << 8 | BigInt(c))
      }
    }
  }

  /// Returns the two's-complement representation of `self` using `w` bits.
  ///
  /// - Precondition: `w` is positive.
  /// - Precondition: `self` is representable as a signed integer of `w` bits.
  func twosComplement(ofBitWidth w: UInt8) -> BigInt {
    precondition(w > 0)

    let modulus = BigInt(1) << Int(w)
    let remainder = self % modulus
    return remainder < 0 ? remainder + modulus : remainder
  }

}
