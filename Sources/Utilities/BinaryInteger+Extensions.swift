extension BinaryInteger {

  /// Returns `self` rounded up to the nearest multiple of `n`, which is a power of two.
  public func rounded(upToNearestMultipleOf n: Self) -> Self {
    let r = self & (n - 1)
    return (r == 0) ? self : self + (n - r)
  }

  /// Returns the smallest `n` such that `n * divisor >= self`.
  ///
  /// - Requires: `self >= 0` and `divisor > 0`.
  public func dividedRoundingUp(by divisor: Self) -> Self {
    let (quotient, remainder) = self.quotientAndRemainder(dividingBy: divisor)
    return quotient + (remainder > 0 ? 1 : 0)
  }

}
