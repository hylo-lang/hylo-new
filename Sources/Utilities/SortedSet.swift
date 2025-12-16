import Algorithms

/// A sorted collection of unique elements.
public struct SortedSet<Element: Comparable>: Equatable {

  /// The elements in the set.
  private var elements: ContiguousArray<Element>

  /// Creates an empty instance.
  public init() {
    self.elements = []
  }

  /// Creates an instance with the elements in `members`.
  public init<S: Sequence<Element>>(_ members: S) {
    self.elements = []
    self.elements.reserveCapacity(members.underestimatedCount)
    for e in members {
      insert(e)
    }
  }

  /// Creates the union of the contents of each sequence in `sources`.
  public init<S: Sequence<Self>>(combining sources: S) {
    var xs: [(head: Element, tail: Self.Iterator)] = sources.compactMap { (s) in
      var i = s.makeIterator()
      if let x = i.next() {
        return (x, i)
      } else {
        return nil
      }
    }

    self.elements = []
    while let i = xs.indices.min(by: { (a, b) in xs[a].head < xs[b].head }) {
      // Insert the element unless it's already in the set.
      if xs[i].head != elements.last {
        elements.append(xs[i].head)
      }

      // Advance to the next element.
      if let x = xs[i].tail.next() {
        xs[i].head = x
      } else {
        xs.remove(at: i)
      }
    }
  }

  /// Creates an empty instance with enough space to store `minimumCapacity` elements without
  /// allocating new storage.
  public init(minimumCapacity: Int) {
    self.elements = []
    self.elements.reserveCapacity(minimumCapacity)
  }

  /// Creates an instance with the given elements, which are sorted.
  private init(sorted elements: ContiguousArray<Element>) {
    assert(elements.indices.dropLast().allSatisfy({ (i) in elements[i] < elements[i + 1] }))
    self.elements = elements
  }

  /// The number of elements that can be stored in `self` without allocating new storage.
  public var capacity: Int {
    elements.capacity
  }

  /// Reserves enough space to store `minimumCapacity` elements without allocating new storage.
  public mutating func reserveCapacity(_ minimumCapacity: Int) {
    elements.reserveCapacity(minimumCapacity)
  }

  /// Returns the index of `e` iff it is contained in `self`.
  ///
  /// - Complexity: O(log n) where n is the length of `self`.
  public func firstIndex(of e: Element) -> Int? {
    let k = elements.partitioningIndex(where: { (x) in e <= x })
    return (k < elements.count) && (elements[k] == e) ? k : nil
  }

}

extension SortedSet: MutableCollection, RandomAccessCollection {

  public typealias Index = Int

  public var isEmpty: Bool {
    elements.isEmpty
  }

  public var count: Int {
    elements.count
  }

  public var startIndex: Int {
    0
  }

  public var endIndex: Int {
    elements.count
  }

  public func index(after i: Int) -> Int {
    i + 1
  }

  public subscript(i: Int) -> Element {
    get { elements[i] }
    set { elements[i] = newValue }
    _modify { yield &elements[i] }
  }

}

extension SortedSet: SetAlgebra {

  public func contains(_ e: Element) -> Bool {
    firstIndex(of: e) != nil
  }

  @discardableResult
  public mutating func insert(_ e: Element) -> (inserted: Bool, memberAfterInsert: Element) {
    let k = elements.partitioningIndex(where: { (x) in e <= x })
    if (k >= elements.count) || (elements[k] != e) {
      elements.insert(e, at: k)
      return (true, e)
    } else {
      return (false, elements[k])
    }
  }

  @discardableResult
  public mutating func update(with e: consuming Element) -> Element? {
    let k = elements.partitioningIndex(where: { (x) in e <= x })
    if (k >= elements.count) || (elements[k] != e) {
      elements.insert(e, at: k)
      return nil
    } else {
      swap(&e, &elements[k])
      return e
    }
  }

  @discardableResult
  public mutating func remove(_ e: Element) -> Element? {
    firstIndex(of: e).map({ (k) in elements.remove(at: k) })
  }

  public mutating func formUnion(_ other: Self) {
    self = union(other)
  }

  public func union(_ other: SortedSet) -> SortedSet {
    var lhs = self.elements
    var rhs = other.elements

    // Insert into the largest container to minimize the number of lookups.
    if lhs.count < rhs.count { swap(&lhs, &rhs) }

    var i = 0
    for j in rhs.indices {
      let e = rhs[j]
      let k = lhs[i...].partitioningIndex(where: { (x) in e <= x })

      if k >= lhs.count {
        lhs.append(contentsOf: other.elements[j...])
        break
      } else if self.elements[k] != e {
        lhs.insert(e, at: k)
      }

      i = k + 1
    }

    return .init(sorted: lhs)
  }

  public mutating func formIntersection(_ other: Self) {
    self = intersection(other)
  }

  public func intersection(_ other: SortedSet) -> SortedSet {
    var result: ContiguousArray<Element> = []
    var i = 0
    var j = 0

    while (i < self.elements.count) && (j < other.elements.count) {
      let a = self.elements[i]
      let b = other.elements[j]
      if a == b {
        result.append(a)
        i += 1
        j += 1
      } else if a < b {
        i += 1
      } else {
        j += 1
      }
    }

    return .init(sorted: result)
  }

  public mutating func formSymmetricDifference(_ other: Self) {
    self = symmetricDifference(other)
  }

  public func symmetricDifference(_ other: SortedSet) -> SortedSet {
    if self.isEmpty {
      return other
    } else if other.isEmpty {
      return self
    }

    var result: ContiguousArray<Element> = []
    var i = 0
    var j = 0

    while (i < self.elements.count) && (j < other.elements.count) {
      let a = self.elements[i]
      let b = other.elements[j]
      if a == b {
        i += 1
        j += 1
      } else if a < b {
        result.append(a)
        i += 1
      } else {
        result.append(b)
        j += 1
      }
    }

    return .init(sorted: result)
  }

}

extension SortedSet: Sendable where Element: Sendable {}

extension SortedSet: Hashable where Element: Hashable {}

extension SortedSet: CustomStringConvertible {

  public var description: String {
    elements.description
  }

}
