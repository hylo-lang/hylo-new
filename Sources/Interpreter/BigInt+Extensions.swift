import Archivist
import BigInt

extension BigInt {

  /// Creates an instance by interpreting `storedForm` as an unsigned value
  /// stored in `byteOrder`.
  init(unsignedFrom storedForm: some Collection<UInt8>, storedIn byteOrder: Endianness) {
    if byteOrder == .little {
      self = .init(unsignedFrom: storedForm.reversed(), storedIn: .big)
    } else {
      self = storedForm.reduce(into: 0 as BigInt) { r, c in
        r <<= 8
        r |= BigInt(c)
      }
    }
  }

  /// Returns whether `self` is representable as a `w`-bit integer.
  func isRepresentable(asIntegerHavingBitWidth w: UInt8) -> Bool {
    precondition(w > 0)
    if self < 0 {
      let wMinusOneLowBits = ~((-1 as BigInt) << (w - 1))
      return (self | ~wMinusOneLowBits) == self
    } else {
      let wLowBits = ~((-1 as BigInt) << w)
      return (self & wLowBits) == self
    }
  }

}
