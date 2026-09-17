import FrontEnd

extension IntegerPredicate {

  /// Returns whether `lhs` satisfies `self` with respect to `rhs`.
  public func callAsFunction<T: FixedWidthInteger & UnsignedInteger>(
    _ lhs: T,
    _ rhs: T
  ) -> Bool {
    switch self {
    case .eq: lhs == rhs
    case .ne: lhs != rhs
    case .ugt: lhs > rhs
    case .uge: lhs >= rhs
    case .ult: lhs < rhs
    case .ule: lhs <= rhs
    case .sgt: rhs.isSignedLess(than: lhs)
    case .sge: !lhs.isSignedLess(than: rhs)
    case .slt: lhs.isSignedLess(than: rhs)
    case .sle: !rhs.isSignedLess(than: lhs)
    }
  }

  /// Returns whether `lhs` satisfies `self` with respect to `rhs` where `lhs`
  /// and `rhs` are `w`-bit integers in byte order `o`.
  internal func callAsFunction(
    _ lhs: RuntimeValue, _ rhs: RuntimeValue,
    bitWidth w: Int, inByteOrder o: Endianness
  ) -> Bool {
    switch w {
    case 8: self(lhs.asI8, rhs.asI8)
    case 16: self(lhs.asI16(assumingByteOrder: o), rhs.asI16(assumingByteOrder: o))
    case 32: self(lhs.asI32(assumingByteOrder: o), rhs.asI32(assumingByteOrder: o))
    case 64: self(lhs.asI64(assumingByteOrder: o), rhs.asI64(assumingByteOrder: o))
    // TODO: uncomment when 128-bit integer is supported.
    //
    // case 128: self(lhs.i128(assumingByteOrder: o), rhs.i128(assumingByteOrder: o))
    default: fatalError("Unknown builtin integer size \(w)")
    }
  }

}

extension UnsignedInteger where Self: FixedWidthInteger {

  /// Returns whether `self` is less than `other` when their bit patterns are
  /// interpreted as two's-complement signed integers.
  fileprivate func isSignedLess(than other: Self) -> Bool {
    let signBit = Self(1) << (Self.bitWidth - 1)
    return (self ^ signBit) < (other ^ signBit)
  }

}
