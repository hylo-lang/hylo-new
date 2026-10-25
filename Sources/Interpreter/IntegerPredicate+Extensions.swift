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

  /// Returns whether `lhs` satisfies `self` with respect to `rhs`.
  internal func callAsFunction(
    _ lhs: RuntimeValue, _ rhs: RuntimeValue,
  ) -> Bool {
    if let x = lhs.i1, let y = rhs.i1 {
      self(x ? UInt8(1) : 0, y ? UInt8(1) : 0)
    } else if let x = lhs.i8, let y = rhs.i8 {
      self(x, y)
    } else if let x = lhs.i16, let y = rhs.i16 {
      self(x, y)
    } else if let x = lhs.i32, let y = rhs.i32 {
      self(x, y)
    } else if let x = lhs.i64, let y = rhs.i64 {
      self(x, y)
    } else if let x = lhs.i128, let y = rhs.i128 {
      self(x, y)
    } else {
      fatalError("arguments are not same type integers.")
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
