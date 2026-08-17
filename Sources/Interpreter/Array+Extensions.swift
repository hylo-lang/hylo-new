import FrontEnd

extension Array {

  /// Creates and returns an array containing `count` or more copies of `e`
  /// together with a `baseOffset` such that the address of the element at
  /// `baseOffset` is aligned to `alignment`.
  static func aligned(
    repeating e: Element,
    count: Int,
    alignment: Alignment
  ) -> (array: Self, baseOffset: Int) {
    var r = Self(repeating: e, count: count)

    // If we didn't get suitably-aligned storage, allocate enough to
    // ensure we can find a suitably-aligned region of the right
    // size.
    // FIXME: https://github.com/hylo-lang/hylo-new/issues/614
    if r.withUnsafeBytes({
      !UInt(bitPattern: $0.baseAddress).isMultiple(of: alignment)
    }) {
      let s = MemoryLayout<Element>.stride
      let additionalElementsCount = (alignment.bytes - 1) / s

      r = Self(repeating: e, count: count + additionalElementsCount)
    }

    let baseOffset = r.withUnsafeBytes { $0.firstOffsetAligned(to: alignment) }

    return (r, baseOffset)
  }

}
