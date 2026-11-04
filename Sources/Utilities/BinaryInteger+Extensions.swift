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

  /// Returns the digits of `self` in base `radix`, after its sign and as many zeros as needed to
  /// be at least `width` characters long.
  public func digits(radix: Int = 10, width: Int) -> String {
    let s = self < 0 ? "-" : ""
    let d = String(magnitude, radix: radix)
    return s + String(repeating: "0", count: max(0, width - s.count - d.count)) + d
  }

}
