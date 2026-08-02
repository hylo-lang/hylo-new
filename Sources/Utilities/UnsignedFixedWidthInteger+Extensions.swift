extension FixedWidthInteger where Self: UnsignedInteger {

  /// The number of bits required to represent `self`.
  public var bitsInRepresentation: UInt {
    UInt(MemoryLayout.size(ofValue: self)) * 8 - UInt(self.leadingZeroBitCount)
  }

  /// Self, rounded up to the nearest power of 2.
  public var roundedUpToPowerOf2: UInt {
    self == 0 ? 1 : 1 << (self - 1).bitsInRepresentation
  }
}
