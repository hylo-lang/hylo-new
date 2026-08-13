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

  /// Returns the set of elements in `self` that are not greater than any other element in `self`
  /// according to `compare`.
  public func minimalElements(by compare: (Element, Element) -> StrictOrdering) -> [Element] {
    var it = makeIterator()
    var leaves: [Element] = []

    while let x = it.next() {
      if let e = leaves.uniqueElement {
        switch compare(e, x) {
        case .ascending:
          continue
        case .equal:
          leaves.append(x)
          continue
        case .descending:
          break
        }
      }

      if leaves.allSatisfy({ (y) in compare(x, y) == .ascending }) {
        leaves = [x]
      } else {
        leaves.append(x)
      }
    }

    return leaves
  }

  /// Returns the least element in `self` according to `compare`, or `nil` if `self` contains no
  /// such element.
  public func least(by compare: (Element, Element) -> StrictOrdering) -> Element? {
    minimalElements(by: compare).uniqueElement
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

  /// Returns the least positive common multiple of all elements in the sequence;
  /// Returns `nil` if the sequence is empty.
  ///
  /// - Precondition: All elements are non-zero.
  ///
  /// - Complexity: `O(n log(m))`, where `n` is the number of elements and
  ///   `m` is the smallest non-zero element.
  public func lcm() -> Element.Magnitude? where Element: BinaryInteger {
    var i = makeIterator()
    guard let f = i.next() else { return nil }

    var r = f.magnitude
    while let e = i.next() {
      r = Utilities.lcm(r, e.magnitude)
    }

    return r
  }

}
