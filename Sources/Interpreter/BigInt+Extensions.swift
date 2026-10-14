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

}
