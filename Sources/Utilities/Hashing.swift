/// A Fowler–Noll–Vo hash function.
public struct FNV {

  #if arch(x86_64) || arch(arm64)
    public static let basis = Int(bitPattern: 0xcbf29ce484222325)
    public static let prime = Int(bitPattern: 0x100000001b3)
  #elseif arch(i386) || arch(arm)
    public static let basis = Int(bitPattern: 0x811c9dc5)
    public static let prime = Int(bitPattern: 0x1000193)
  #endif

  /// The current hashed value.
  public private(set) var state: Int

  /// Creates an instance with a seed.
  public init(seed: Int = FNV.basis) {
    state = seed
  }

  /// Hashes `value` into the current state of `self`.
  public mutating func combine<T: FixedWidthInteger>(_ value: T) {
    for i in 0 ..< MemoryLayout<T>.size {
      state = state &* Self.prime
      state = state ^ Int(truncatingIfNeeded: UInt8(truncatingIfNeeded: value >> (8 * i)))
    }
  }

  /// Hashes `value` into the current state of `self`.
  public mutating func combine(_ value: String) {
    combine(bytes: value.utf8)
  }

  /// Hashes the contents of `bytes` into the current state of `self`.
  public mutating func combine<T: Collection<UInt8>>(bytes: T) {
    for b in bytes {
      state = state &* Self.prime
      state = state ^ Int(truncatingIfNeeded: b)
    }
  }

}
