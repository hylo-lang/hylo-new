import Algorithms

extension MutableCollection where Self: RangeReplaceableCollection {

  /// Modifies `self` so that each element `e` is either replaced by `transform(e)` if that result
  /// is not `nil` or removed otherwise.
  ///
  /// - Complexity: O(n log n) where n is the length of `self`.
  public mutating func compactMapInPlace(_ transform: (Element) throws -> Element?) rethrows {
    let p = try compactMapInPlace(count: count, low: startIndex, high: endIndex, transform)
    removeSubrange(p...)
  }

  /// Modifies `self` so that each element `e` in the range `low ..< high` is either replaced by
  /// `transform(e)` if that result is not `nil` or moved to the back of `self` otherwise, and
  /// returns the index immediately after the first transform element.
  ///
  /// - Requires: `n` is the number of elements in the range `low ..< high`.
  /// - Complexity: O(n log n)
  private mutating func compactMapInPlace(
    count n: Int, low: Index, high: Index, _ transform: (Element) throws -> Element?
  ) rethrows -> Index {
    if n == 0 { return low }
    if n == 1 {
      if let e = try transform(self[low]) {
        self[low] = e
        return high
      } else {
        return low
      }
    }

    let m = n >> 1
    let p = index(low, offsetBy: m)
    let q = try compactMapInPlace(count: m, low: low, high: p, transform)
    let r = try compactMapInPlace(count: n - m, low: p, high: high, transform)
    return rotate(subrange: q ..< r, toStartAt: p)
  }

}
