import BigInt

extension BigInt {

  /// Creates an instance by interpreting `storedForm` as an unsigned value
  /// stored in `byteOrder`.
  init(unsignedFrom storedForm: some Collection<UInt8>, storedIn byteOrder: Endianness) {
    if byteOrder == .lsbFirst {
      self = .init(unsignedFrom: storedForm.reversed(), storedIn: .msbFirst)
    } else {
      self = storedForm.reduce(into: 0 as BigInt) { r, c in
        r <<= 8
        r |= BigInt(c)
      }
    }
  }

  /// Returns whether `self` is representable as a `w`-bit integer.
  func isRepresentable(asIntegerHavingBitWidth w: UInt8) -> Bool {
    if self >= 0 {
      let unsignedUpperBound = BigInt(1) << w
      return self < unsignedUpperBound
    } else {
      let signedUpperBound = BigInt(1) << (w - 1)
      return self >= -signedUpperBound && self < signedUpperBound
    }
  }

}
