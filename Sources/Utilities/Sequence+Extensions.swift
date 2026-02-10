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
  /// according to `areInIncreasingOrder`.
  public func minimalElements(by areInIncreasingOrder: (Element, Element) -> Bool) -> [Element] {
    var it = makeIterator()
    var leaves: [Element] = []
    var hasLeast = false

    while let x = it.next() {
      if hasLeast {
        if areInIncreasingOrder(leaves[0], x) {
          continue
        } else if !areInIncreasingOrder(x, leaves[0]) {
          leaves.append(x)
          hasLeast = false
          continue
        }
      }

      if leaves.allSatisfy({ (y) in areInIncreasingOrder(x, y) }) {
        leaves = [x]
        hasLeast = true
      }
    }

    return leaves
  }

  /// Returns the least element in `self` according to `areInIncreasingOrder`, or `nil` if `self`
  /// contains no such element.
  public func least(by areInIncreasingOrder: (Element, Element) -> Bool) -> Element? {
    minimalElements(by: areInIncreasingOrder).uniqueElement
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

}
