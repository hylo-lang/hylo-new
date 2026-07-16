/// A deterministic, seedable pseudo-random number generator for reproducible tests.
///
/// Uses the [Splitmix64](https://rosettacode.org/wiki/Pseudo-random_numbers/Splitmix64) algorithm.
struct SeedableRandomNumberGenerator: RandomNumberGenerator {

  private var state: UInt64

  /// Creates an instance with the given seed.
  init(seed: UInt64) {
    self.state = seed
  }

  /// Calculates and returns the next random number.
  mutating func next() -> UInt64 {
    state &+= 0x9E37_79B9_7F4A_7C15
    var z = state
    z = (z ^ (z >> 30)) &* 0xBF58_476D_1CE4_E5B9
    z = (z ^ (z >> 27)) &* 0x94D0_49BB_1331_11EB
    return z ^ (z >> 31)
  }

}
