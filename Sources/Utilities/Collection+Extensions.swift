extension Collection {

  /// The unique element of `self` if `self` contains exactly one element; otherwise, `nil`.
  public var uniqueElement: Element? {
    count == 1 ? self[startIndex] : nil
  }

  /// The first element of `self` and its suffix after its first index or `nil` if `self` is empty.
  public var headAndTail: (head: Element, tail: SubSequence)? {
    if isEmpty { return nil }
    return (head: self[startIndex], tail: self[index(after: startIndex)...])
  }

  /// Returns the result of calling `action` on a buffer containing the elements in `self`
  /// transformed by `transform`, in the same order.
  ///
  /// The buffer pointer passed to `action` is only valid for the duration of the closure's call.
  public func withUnsafeTemporaryView<T, R>(
    applying transform: (Element) throws -> T,
    _ action: (UnsafeMutableBufferPointer<T>) throws -> R
  ) rethrows -> R {
    try withUnsafeTemporaryAllocation(of: T.self, capacity: count) { (buffer) in
      if buffer.count == 0 { return try action(buffer) }

      var b = buffer.baseAddress!
      var i = 0
      defer { b.deinitialize(count: i) }

      for e in self {
        try b.initialize(to: transform(e))
        b = b.advanced(by: 1)
        i += 1
      }

      return try action(buffer)
    }
  }

}

extension RangeReplaceableCollection where Element: Hashable {

  /// Removes all except the first element from every consecutive group of equivalent elements.
  ///
  /// - Complexity: O(n) where n is the length of `self`.
  public mutating func removeDuplicates() {
    var s = Set<Element>(minimumCapacity: count)
    var i = startIndex
    while i != endIndex {
      if s.insert(self[i]).inserted {
        formIndex(after: &i)
      } else {
        remove(at: i)
      }
    }
  }

}
