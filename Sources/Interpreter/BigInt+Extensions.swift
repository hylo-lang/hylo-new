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

}
