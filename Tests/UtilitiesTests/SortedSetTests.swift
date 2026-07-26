import Utilities
import XCTest

final class SortedSetTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = SortedSet<String>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testInitWithSequence() {
    let members = ["a", "b"]
    let s = SortedSet<String>(members)
    XCTAssert(s.elementsEqual(members))
  }

  func testInitCombining() {
    let s = SortedSet(combining: [["b", "c"], ["a", "c"], ["b", "d"]])
    XCTAssert(s.elementsEqual(["a", "b", "c", "d"]))
  }

  func testInitWithArrayLiteral() {
    let s: SortedSet = ["a", "b"]
    XCTAssert(s.elementsEqual(["a", "b"]))
  }

  func testIsEmpty() {
    var s = SortedSet<String>()
    XCTAssert(s.isEmpty)
    s.insert("a")
    XCTAssertFalse(s.isEmpty)
  }

  func testCount() {
    var s = SortedSet<String>()
    XCTAssertEqual(s.count, 0)
    s.insert("a")
    XCTAssertEqual(s.count, 1)
    s.insert("b")
    XCTAssertEqual(s.count, 2)
    s.remove("b")
    XCTAssertEqual(s.count, 1)
    s.remove("a")
    XCTAssertEqual(s.count, 0)
  }

  func testFirstIndexOf() {
    var s = SortedSet<String>()
    XCTAssertNil(s.firstIndex(of: "a"))

    s.insert("a")
    XCTAssertEqual(s.firstIndex(of: "a"), 0)

    s.insert("b")
    s.insert("c")
    XCTAssertEqual(s.firstIndex(of: "a"), 0)
    XCTAssertEqual(s.firstIndex(of: "b"), 1)
    XCTAssertEqual(s.firstIndex(of: "c"), 2)

    s.remove("b")
    XCTAssertEqual(s.firstIndex(of: "a"), 0)
    XCTAssertNil(s.firstIndex(of: "b"))
    XCTAssertEqual(s.firstIndex(of: "c"), 1)
  }

  func testContains() {
    var s = SortedSet<String>()
    XCTAssertFalse(s.contains("a"))
    s.insert("a")  // insert
    XCTAssert(s.contains("a"))
    s.remove("a")  // delete
    XCTAssertFalse(s.contains("a"))
    s.remove("a")  // no-op
    XCTAssertFalse(s.contains("a"))
  }

  func testInsert() {
    var s = SortedSet<String>()

    let p0 = s.insert("a")
    XCTAssert(p0.inserted)
    let p1 = s.insert("a")
    XCTAssertFalse(p1.inserted)
    let p2 = s.insert("b")
    XCTAssert(p2.inserted)
  }

  func testRemoveAt() {
    var s: SortedSet = ["a", "b", "c"]
    XCTAssertEqual(s.remove(at: s.startIndex), "a")
    XCTAssert(s.elementsEqual(["b", "c"]))
  }

  func testRemove() {
    var s: SortedSet = ["a", "b", "c"]
    XCTAssertNotNil(s.remove("a"))
    XCTAssertNil(s.remove("a"))
    XCTAssertNil(s.remove("z"))
  }

  func testSubtracting() {
    let s: SortedSet = ["a", "b", "c"]
    let t = s.subtracting(["d", "c", "a"])
    XCTAssertEqual(t, ["b"])
  }

  func testReserveCapacity() {
    var s: SortedSet = ["a", "b", "c"]
    let t = s
    s.reserveCapacity(100)
    XCTAssertEqual(s, t)
    XCTAssertNotEqual(s.capacity, t.capacity)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testIsCollection() {
    let s: SortedSet = ["a", "b"]
    var i = s.startIndex
    XCTAssertEqual(s[i], "a")
    i = s.index(after: i)
    XCTAssertEqual(s[i], "b")
    i = s.index(after: i)
    XCTAssertEqual(i, s.endIndex)
  }

  func testIsEquatable() {
    let s: SortedSet = ["a", "b", "c"]
    let t: SortedSet = ["c", "b", "a"]
    XCTAssertEqual(s, s)
    XCTAssertEqual(s, t)
    let u: SortedSet = ["a", "b", "d"]
    XCTAssertNotEqual(s, u)
  }

  func testIsHashable() {
    let s: SortedSet = ["a", "b", "c"]
    let t: SortedSet = ["c", "b", "a"]
    XCTAssertEqual(s.hashValue, t.hashValue)
  }

  func testIsCustomStringConvertible() {
    let s: SortedSet = [1, 2, 3]
    XCTAssertEqual(s.description, "[1, 2, 3]")
  }

  func testUnion() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      let observed = a.union(b)
      let expected = Set(a).union(Set(b)).sorted()
      XCTAssert(
        observed.elementsEqual(expected),
        "\(Array(a)) U \(Array(b)) == \(Array(observed)); expected \(expected)")

      // The union is commutative.
      XCTAssertEqual(observed, b.union(a), "\(Array(a)) U \(Array(b))")

      // `formUnion` agrees with `union`.
      var c = a
      c.formUnion(b)
      XCTAssertEqual(c, observed, "\(Array(a)) U \(Array(b))")
    }
  }

  func testIntersection() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      let observed = a.intersection(b)
      let expected = Set(a).intersection(Set(b)).sorted()
      XCTAssert(
        observed.elementsEqual(expected),
        "\(Array(a)) n \(Array(b)) == \(Array(observed)); expected \(expected)")

      // The intersection is commutative.
      XCTAssertEqual(observed, b.intersection(a), "\(Array(a)) n \(Array(b))")

      // `formIntersection` agrees with `intersection`.
      var c = a
      c.formIntersection(b)
      XCTAssertEqual(c, observed, "\(Array(a)) n \(Array(b))")
    }
  }

  func testSymmetricDifferenceOracle() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      // The result matches the oracle implementation.
      let observed = a.symmetricDifference(b)
      let expected = Set(a).symmetricDifference(Set(b)).sorted()
      XCTAssert(
        observed.elementsEqual(expected),
        "\(Array(a)) ∆ \(Array(b)) == \(Array(observed)); expected \(expected)")
    }
  }

  func testSymmetricDifferenceCommutative() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      // Symmetric difference is commutative.
      let observed = a.symmetricDifference(b)
      XCTAssertEqual(observed, b.symmetricDifference(a), "\(Array(a)) ∆ \(Array(b))")
    }
  }

  func testSymmetricDifferenceUnion() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      let observed = a.symmetricDifference(b)
      // A ∆ B == (A \ B) U (B \ A)
      XCTAssertEqual(
        observed, a.subtracting(b).union(b.subtracting(a)), "\(Array(a)) ∆ \(Array(b))")
    }
  }

  func testFormSymmetricDifference() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      // `formSymmetricDifference` agrees with `symmetricDifference`.
      var c = a
      c.formSymmetricDifference(b)
      XCTAssertEqual(c, a.symmetricDifference(b), "\(Array(a)) ∆ \(Array(b))")
    }
  }

  func testSubtractingOracle() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      let observed = a.subtracting(b)
      let expected = Set(a).subtracting(Set(b)).sorted()
      XCTAssert(
        observed.elementsEqual(expected),
        "\(Array(a)) \\ \(Array(b)) == \(Array(observed)); expected \(expected)")

      // `subtract` agrees with `subtracting`.
      var c = a
      c.subtract(b)
      XCTAssertEqual(c, observed, "\(Array(a)) \\ \(Array(b))")
    }
  }

  func testInitCombiningOracle() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for sources in g.randomSetLists() {
      let observed = SortedSet(combining: sources)
      let expected = sources.reduce(into: Set<Int>(), { (s, x) in s.formUnion(x) }).sorted()
      XCTAssert(
        observed.elementsEqual(expected),
        "combining \(sources.map(Array.init)) == \(Array(observed)); expected \(expected)")
    }
  }

  func testInclusionPredicates() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      let x = Set(a)
      let y = Set(b)
      let m = "\(Array(a)) vs \(Array(b))"
      XCTAssertEqual(a.isSubset(of: b), x.isSubset(of: y), m)
      XCTAssertEqual(a.isSuperset(of: b), x.isSuperset(of: y), m)
      XCTAssertEqual(a.isStrictSubset(of: b), x.isStrictSubset(of: y), m)
      XCTAssertEqual(a.isStrictSuperset(of: b), x.isStrictSuperset(of: y), m)
      XCTAssertEqual(a.isDisjoint(with: b), x.isDisjoint(with: y), m)

      // A set is a subset of its union with any other set and a superset of its intersection.
      XCTAssert(a.isSubset(of: a.union(b)), m)
      XCTAssert(a.isSuperset(of: a.intersection(b)), m)
    }
  }

  func testIndexInsertingIfAbsent() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for (a, b) in g.randomSetPairs() {
      for e in b {
        var s = a
        let m = "inserting \(e) in \(Array(a))"
        let (inserted, k) = s.index(insertingIfAbsent: e)
        XCTAssertEqual(inserted, !a.contains(e), m)
        XCTAssertEqual(s[k], e, m)
        XCTAssertEqual(s.firstIndex(of: e), k, m)
        XCTAssertEqual(s, a.union([e]), m)
      }
    }
  }

  func testInsertReturnsMemberAlreadyPresent() {
    var s: SortedSet<Keyed> = [.init(key: 1, payload: "a")]

    let p0 = s.insert(.init(key: 2, payload: "b"))
    XCTAssert(p0.inserted)
    XCTAssertEqual(p0.memberAfterInsert.payload, "b")

    // The member already in the set is returned, not the one passed as an argument.
    let p1 = s.insert(.init(key: 1, payload: "z"))
    XCTAssertFalse(p1.inserted)
    XCTAssertEqual(p1.memberAfterInsert.payload, "a")
    XCTAssertEqual(s[0].payload, "a")
  }

  func testUpdateWith() {
    var s: SortedSet<Keyed> = [.init(key: 1, payload: "a"), .init(key: 3, payload: "c")]

    // Updating with an absent member inserts it and returns `nil`.
    XCTAssertNil(s.update(with: .init(key: 2, payload: "b")))
    XCTAssertEqual(s.map(\.payload), ["a", "b", "c"])

    // Updating with a present member replaces it and returns the member it replaced.
    XCTAssertEqual(s.update(with: .init(key: 1, payload: "z"))?.payload, "a")
    XCTAssertEqual(s.map(\.payload), ["z", "b", "c"])
  }

  /// An element whose equality and ordering are defined by `key` alone, ignoring `payload`.
  ///
  /// Used for distinguishing between which instance is returned upon updates.
  private struct Keyed: Comparable, Hashable {

    /// The value defining the identity of `self`.
    let key: Int

    /// A value that takes no part in equality or ordering.
    let payload: String

    static func < (l: Self, r: Self) -> Bool {
      l.key < r.key
    }

    static func == (l: Self, r: Self) -> Bool {
      l.key == r.key
    }

    func hash(into hasher: inout Hasher) {
      hasher.combine(key)
    }

  }

}

extension RandomNumberGenerator {

  /// Returns lists of pseudo-random sets to combine, covering a range of lengths, sizes, and
  /// overlaps, drawn from `g`.
  fileprivate mutating func randomSetLists() -> [[SortedSet<Int>]] {
    (0..<300).map { (_) in
      let bound = Int.random(in: 1...24, using: &self)
      return (0..<Int.random(in: 0...5, using: &self)).map { (_) in
        randomSet(maxCount: Int.random(in: 0...8, using: &self), bound: bound)
      }
    }
  }

  /// Returns pairs of pseudo-random sets covering a range of sizes and overlaps, drawn from `g`.
  fileprivate mutating func randomSetPairs() -> [(SortedSet<Int>, SortedSet<Int>)] {
    (0..<100).map { (_) in
      let bound = Int.random(in: 1...24, using: &self)
      let a = randomSet(maxCount: Int.random(in: 0...16, using: &self), bound: bound)
      let b = randomSet(maxCount: Int.random(in: 0...16, using: &self), bound: bound)
      return (a, b)
    }
  }

  /// Returns a set of at most `maxCount` elements drawn from `0 ..< bound` using `g`.
  fileprivate mutating func randomSet(maxCount: Int, bound: Int) -> SortedSet<Int> {
    SortedSet((0..<maxCount).map({ (_) in Int.random(in: 0..<bound, using: &self) }))
  }

}
