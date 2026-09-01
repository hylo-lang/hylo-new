import FrontEnd

/// Types that describe the ABI for which we might interpret code.
protocol TargetABI {

  /// Returns the ABI-required alignment of `t`.
  ///
  /// The alignment of `.i(1)` and `.i(8)` is required to be one byte.
  func alignment(_ t: MachineType) -> Int

  /// The number of bits in a pointer type.
  var bitsInAPointer: Int { get }

}

extension TargetABI {

  /// Returns the size, in bytes, of `t` on `self`.
  public func size(_ t: MachineType) -> Int {
    switch t {
    case .i(let w): Int(w.dividedRoundingUp(by: 8))
    case .word: bitsInAPointer
    case .float16: 2
    case .float32: 4
    case .float64: 8
    case .float128: 16
    case .ptr: bitsInAPointer / 8
    }
  }

  /// Returns the size and alignment of `t` instances.
  public func footprint(_ t: MachineType) -> TypeLayout.StorageRequirements {
    .init(alignment: alignment(t), size: size(t))
  }

}

/// An ABI we can use to interpret code when matching some real ABI doesn't matter.
struct UnrealABI: TargetABI {

  /// An instance.
  public init() {}

  /// The size of a word in `bits`
  private let bitsInAWord = 64

  /// The maximal alignment of a machine type in bytes.
  private let maxAlignment = 128 / 8

  /// Returns the ABI-required alignment of `t`.
  func alignment(_ t: MachineType) -> Int { min(size(t), maxAlignment) }

  /// The size of a pointer in bytes.
  var bitsInAPointer: Int { bitsInAWord }

}

extension TargetABI {

  /// Returns a discriminator type for the enum of `n` types in `p`.
  ///
  /// - Precondition: `n >= 0`.
  func enumDiscriminator(count n: Int, in p: inout Program) -> MonomorphicTypeIdentity {
    precondition(n >= 0)
    if n <= 1 { return MonomorphicTypeIdentity(.void) }
    let bitsNeeded = UInt(n - 1).bitsInRepresentation
    // Integer sizes are a contiguous range of powers of 2 starting with 8
    let integerSize = max(8, bitsNeeded.roundedUpToPowerOf2)
    return .init(p.types.demand(MachineType.i(UInt8(integerSize))).erased)
  }

}
