extension Sequence {

  /// Returns the elements of `self` sorted by their respective values at `p`.
  public func sorted<T: Comparable>(by p: KeyPath<Element, T>) -> [Element] {
    self.sorted(by: { (a, b) in a[keyPath: p] < b[keyPath: p] })
  }

  /// Returns the elements in `self` sorted according to `areInIncreasingOrder` applied to the
  /// values of the elements at `path`.
  public func sorted<T>(
    by path: KeyPath<Element, T>, using areInIncreasingOrder: (T, T) -> Bool
  ) -> [Element] {
    self.sorted(by: { (a, b) in areInIncreasingOrder(a[keyPath: path], b[keyPath: path]) })
  }

  /// Returns the elements in `self` that are ordered (by `compare`) less than all other elements,
  /// in their original order.
  public func minimalElements(by compare: ThreeWayComparison<Element>) -> [Element] {
    var it = makeIterator()
    guard var min = it.next() else { return [] }
    var r = [min]

    while let x = it.next() {
      switch compare(min, x) {
      case .ascending: break
      case .equivalent: r.append(x)
      case .descending:
        min = x
        r = [x]
      }
    }
    return r
  }

  /// Returns the least element in `self` according to `compare`, or `nil` if `compare` does not
  /// order one element less than all others.
  public func leastElement(by compare: ThreeWayComparison<Element>) -> Element? {
    var it = makeIterator()
    guard var min = it.next() else { return nil }
    var unique = true
    while let x = it.next() {
      switch compare(min, x) {
      case .ascending: break
      case .equivalent: unique = false
      case .descending:
        min = x
        unique = true
      }
    }
    return unique ? min : nil
  }

  /// Returns the result of applying `transform` to each element in `self`, joined by the given
  /// `separator`.
  public func joinedString(
    separator: String = "",
    transform: (Element) throws -> String
  ) rethrows -> String {
    try self.reduce(into: "") { accumulator, element in
      if !accumulator.isEmpty {
        accumulator.append(separator)
      }
      accumulator.append(try transform(element))
    }
  }

  /// Returns the descriptions of all elements, joined by the given `separator`.
  public func descriptions(joinedBy separator: String = ", ") -> String {
    joinedString(separator: separator) { String(describing: $0) }
  }

  /// Returns the element in `self` with the smallest value measured by `p`, if any.
  ///
  /// If there is more than one smallest element, it is unspecified which one is returned.
  ///
  /// - Complexity: O(n)
  public func min<R: Comparable>(measuredBy p: (Element) -> R) -> Element? {
    self.min(by: { (a, b) in p(a) < p(b) })
  }

}
