/// Fowler–Noll–Vo hash functions.
public enum FNV1 {

  /// An implementation for a particular size.
  public struct Implementation<T: FixedWidthInteger> {

    /// The prime factor.
    private let prime: T

    /// The current hashed value.
    public private(set) var state: T

    /// Creates an instance.
    fileprivate init(basis: T, prime: T) {
      self.state = basis
      self.prime = prime
    }

    /// Hashes `value` into the current state of `self`.
    public mutating func combine<I: FixedWidthInteger>(_ value: I) {
      for i in 0 ..< MemoryLayout<I>.size {
        state = state &* prime
        state = state ^ T(truncatingIfNeeded: UInt8(truncatingIfNeeded: value >> (8 * i)))
      }
    }

    /// Hashes the contents of `bytes` into the current state of `self`.
    public mutating func combine<S: Sequence<UInt8>>(bytes: S) {
      for b in bytes {
        state = state &* prime
        state = state ^ T(truncatingIfNeeded: b)
      }
    }

    /// Hashes `value` into the current state of `self`.
    public mutating func combine(_ value: String) {
      combine(bytes: value.utf8)
    }

  }

  /// Creates an instance producing hashes as instances of `Int`.
  public static func native() -> Implementation<Int> {
#if arch(x86_64) || arch(arm64)
    let basis = Int(bitPattern: 0xcbf29ce484222325)
    let prime = Int(bitPattern: 0x100000001b3)
#elseif arch(i386) || arch(arm)
    let basis = Int(bitPattern: 0x811c9dc5)
    let prime = Int(bitPattern: 0x1000193)
#endif
    return .init(basis: basis, prime: prime)
  }

  /// Creates an instance producing hashes as instances of `UInt128`.
  public static func u128() -> Implementation<UInt128> {
    let basis: UInt128 = 0x6c62272e07bb014262b821756295c58d
    let prime: UInt128 = 0x0000000001000000000000000000013b
    return .init(basis: basis, prime: prime)
  }

  /// Combines the contents of `bytes` into `hasher` and returns it.
  public static func hash<S: Sequence<UInt8>, T: FixedWidthInteger>(
    _ bytes: S, into hasher: consuming Implementation<T>
  ) -> Implementation<T> {
    hasher.combine(bytes: bytes)
    return hasher
  }

}
