/// Returns the greatest common divisor of `a` and `b`.
///
/// - Complexity: `O(log(min(|a|, |b|)))`.
public func gcd<T: BinaryInteger>(_ a: T, _ b: T) -> T.Magnitude {
  var a = a.magnitude
  var b = b.magnitude

  while b != 0 {
    (a, b) = (b, a % b)
  }

  return a
}

/// Returns the least positive integer that is divisible by `a` and `b`.
///
/// - Precondition: `a` and `b` are non-zero.
/// - Complexity: `O(log(min(|a|, |b|)))`.
public func lcm<T: BinaryInteger>(_ a: T, _ b: T) -> T.Magnitude {
  precondition(a != 0 && b != 0)

  let a = a.magnitude
  let b = b.magnitude

  return (a / gcd(a, b)) * b
}
