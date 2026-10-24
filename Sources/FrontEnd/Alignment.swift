import Utilities

/// The alignment requirement of a memory location, which is a power of two number of bytes.
public struct Alignment: Regular, Comparable {

  /// The base-2 logarithm of the value of `self` in bytes.
  public let log2: UInt8

  /// Creates an instance whose value is `2^log2` bytes.
  ///
  /// - Precondition: `2^log2` is representable as an `Int`.
  public init(log2: UInt8) {
    precondition(Int(log2) < Int.bitWidth - 1, "alignment is too large")
    self.log2 = log2
  }

  /// Creates an instance whose value is `n` bytes.
  ///
  /// - Precondition: `n < Int.max` is a power of two.
  public init<T: BinaryInteger>(bytes n: T) {
    precondition(n.isPowerOfTwo, "alignment must be a power of two (was \(n))")
    precondition(n < Int.max)
    self.log2 = UInt8(n.trailingZeroBitCount)
  }

  /// The value of `self` in bytes.
  public var bytes: Int {
    1 << Int(log2)
  }

  /// Returns `true` iff `l` is less than `r`.
  public static func < (l: Self, r: Self) -> Bool {
    l.log2 < r.log2
  }

}

extension Alignment {

  /// Returns an instance whose value is `n` bytes.
  ///
  /// - Precondition: `n < Int.max` is a power of two.
  public static func bytes<T: BinaryInteger>(_ n: T) -> Self {
    .init(bytes: n)
  }

  /// Returns an instance whose value is `2^n` bytes.
  ///
  /// - Precondition: `2^n` is representable as an `Int`.
  public static func log2(_ n: UInt8) -> Self {
    .init(log2: n)
  }

}

extension Alignment: CustomStringConvertible {

  public var description: String {
    "\(bytes)"
  }

}

extension BinaryInteger {

  /// Returns `self` rounded up to the nearest multiple of `a`.
  public func roundedUp(toNearestMultipleOf a: Alignment) -> Self {
    let n = Self(a.bytes)
    let r = self & (n - 1)
    return (r == 0) ? self : self + (n - r)
  }

  /// Returns `true` iff `self` is a multiple of `a`.
  public func isMultiple(of a: Alignment) -> Bool {
    (self & (Self(a.bytes) - 1)) == 0
  }

}
