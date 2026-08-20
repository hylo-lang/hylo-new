extension Array {

  /// Creates and returns an array containing `count` or more copies of `e`
  /// together with a `baseOffset` such that the address of the element at
  /// `baseOffset` is aligned to `alignment`.
  static func aligned(
    repeating e: Element,
    count: Int,
    alignment: Int
  ) -> (array: Self, baseOffset: Int) {
    var r = Self(repeating: e, count: count)

    // If we didn't get suitably-aligned storage, allocate enough to
    // ensure we can find a suitably-aligned region of the right
    // size.
    if r.withUnsafeBytes({
      UInt(bitPattern: $0.baseAddress) % UInt(alignment) != 0
    }) {
      let s = MemoryLayout<Element>.stride
      let additionalElementsCount = (alignment - 1) / s

      r = Self(repeating: e, count: count + additionalElementsCount)
    }

    let baseOffset = r.withUnsafeBytes { $0.firstOffsetAligned(to: alignment) }

    return (r, baseOffset)
  }

}
