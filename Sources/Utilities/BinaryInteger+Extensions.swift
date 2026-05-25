extension BinaryInteger {

  /// Returns `self` rounded up to the nearest multiple of `n`, which is a power of two.
  public func rounded(upToNearestMultipleOf n: Self) -> Self {
    let r = self & (n - 1)
    return (r == 0) ? self : self + (n - r)
  }

}
