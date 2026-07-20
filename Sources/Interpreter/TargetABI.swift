import FrontEnd

/// Types that describe the ABI for which we might interpret code.
protocol TargetABI {

  /// Returns the layout of `t`.
  func layout(_ t: MachineType) -> TypeLayout.Bytes

}

/// An ABI we can use to interpret code when matching some real ABI doesn't matter.
struct UnrealABI: TargetABI {

  /// An instance.
  public init() {}

  /// The size of a word in `bits`
  private let bitsInAWord = 64

  /// The maximal alignment of a builtin type in bytes.
  private let maxAlignment = 128 / 8

  /// Returns the layout for a `bitWidth`-bit type.
  ///
  /// - Precondition: `bitWidth` is a power of 2.
  private func layout(bitWidth: Int) -> TypeLayout.Bytes {
    precondition(
      bitWidth > 0 && bitWidth.nonzeroBitCount == 1,
      "bit width \(bitWidth) is not a power of 2.")
    let sizeInBytes = (bitWidth + 7) / 8
    return .init(
      alignment: min(sizeInBytes, maxAlignment),
      size: sizeInBytes)
  }

  /// Returns the layout of `t`.
  public func layout(_ t: MachineType) -> TypeLayout.Bytes {
    let bitWidth =
      switch t {
      case .i(let w): Int(w)
      case .word: bitsInAWord
      case .float16: 16
      case .float32: 32
      case .float64: 64
      case .float128: 128
      case .ptr: bitsInAWord
      }
    return layout(bitWidth: bitWidth)
  }

}

extension TargetABI {

  /// Returns a discriminator type for the enum of `n` types in `p`.
  ///
  /// Precondition: `n` is positive
  func enumDiscriminator(count n: Int, in p: inout Program) -> MonomorphicTypeIdentity {
    if n == 1 { return MonomorphicTypeIdentity(.void) }
    let bitsNeeded = UInt(n - 1).bitsInRepresentation
    // Integer sizes are a contiguous range of powers of 2 starting with 8
    let integerSize = max(8, bitsNeeded.roundedUpToPowerOf2)
    return .init(p.types.demand(MachineType.i(UInt8(integerSize))).erased)
  }

}
