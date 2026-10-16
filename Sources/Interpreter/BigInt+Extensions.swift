import BigInt

extension BigInt {

  /// Creates an instance by interpreting `storedFrom` as an unsigned value
  /// stored in `byteOrder`.
  init(unsignedFrom storedFrom: some Collection<UInt8>, storedIn byteOrder: Endianness) {
    if byteOrder == .lsbFirst {
      self = .init(unsignedFrom: storedFrom.reversed(), storedIn: .msbFirst)
    } else {
      self = storedFrom.reduce(into: 0 as BigInt) { r, c in
        r <<= 8
        r |= BigInt(c)
      }
    }
  }

}
