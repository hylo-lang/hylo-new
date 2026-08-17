extension BinaryInteger {

  /// Returns the smallest `n` such that `n * divisor >= self`.
  ///
  /// - Requires: `self >= 0` and `divisor > 0`.
  public func roundingUp(afterDividingBy divisor: Self) -> Self {
    precondition(self >= 0)
    precondition(divisor > 0)
    let (quotient, remainder) = self.quotientAndRemainder(dividingBy: divisor)
    return quotient + (remainder > 0 ? 1 : 0)
  }

  /// `true` iff there is an integer `n` such that `2 ** n == self`.
  public var isPowerOfTwo: Bool { (self > 0) && (self & (self - 1) == 0) }

}
