import StableCollections
import XCTest

final class ListTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = List<String>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testInitWithSequence() {
    let members = ["a", "b"]
    let s = List<String>(members)
    XCTAssert(s.elementsEqual(members))
  }

  func testInitWithArrayLiteral() {
    let s: List = ["a", "b"]
    XCTAssert(s.elementsEqual(["a", "b"]))
  }

  func testIsEmpty() {
    var s = List<String>()
    XCTAssert(s.isEmpty)
    s.append("a")
    XCTAssertFalse(s.isEmpty)
  }

  func testCount() {
    var s = List<String>()
    XCTAssertEqual(s.count, 0)
    let a = s.append("a")
    XCTAssertEqual(s.count, 1)
    let b = s.append("b")
    XCTAssertEqual(s.count, 2)
    s.remove(at: a)
    XCTAssertEqual(s.count, 1)
    s.remove(at: b)
    XCTAssertEqual(s.count, 0)
  }

  func testAddressFromRawValue() throws {
    var s: List = ["a", "b", "c"]

    let a = s.firstAddress!
    let b = try XCTUnwrap(s.address(rawValue: a.rawValue))
    XCTAssertEqual(a, b)

    s.remove(at: a)
    XCTAssertNil(s.address(rawValue: a.rawValue))
  }

  func testAppend() {
    var s = List<String>()

    _ = s.append("a")
    XCTAssertEqual(Array(s), ["a"])
    let b = s.append("b")
    XCTAssertEqual(Array(s), ["a", "b"])
    _ = s.append("c")
    XCTAssertEqual(Array(s), ["a", "b", "c"])

    s.remove(at: b)
    s.append("d")
    XCTAssertEqual(Array(s), ["a", "c", "d"])
  }

  func testPrepend() {
    var s = List<String>()

    _ = s.prepend("a")
    XCTAssertEqual(Array(s), ["a"])
    let b = s.prepend("b")
    XCTAssertEqual(Array(s), ["b", "a"])
    _ = s.prepend("c")
    XCTAssertEqual(Array(s), ["c", "b", "a"])

    s.remove(at: b)
    s.prepend("d")
    XCTAssertEqual(Array(s), ["d", "c", "a"])
  }

  func testInsertAfter() {
    var s = List<String>()

    let a = s.prepend("a")
    s.insert("b", after: a)
    s.insert("c", after: a)
    XCTAssertEqual(Array(s), ["a", "c", "b"])
  }

  func testInsertBefore() {
    var s = List<String>()

    let a = s.prepend("a")
    s.insert("b", before: a)
    s.insert("c", before: a)
    XCTAssertEqual(Array(s), ["b", "c", "a"])
  }

  func testInsertAt() {
    var s = List<String>()

    s.insert("a", at: s.startIndex)
    s.insert("b", at: s.startIndex)
    s.insert("c", at: s.index(after: s.startIndex))
    XCTAssertEqual(Array(s), ["b", "c", "a"])
  }

  func testReserveCapacity() {
    var s: List = ["a", "b", "c"]
    let t = s
    s.reserveCapacity(100)
    XCTAssertEqual(s, t)
    XCTAssertNotEqual(s.capacity, t.capacity)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  /// Exhaustively checks `relink(_:before:)` and `relink(_:after:)` against a reference
  /// implementation on lists of 2 to 5 elements, for every pair of distinct positions.
  func testRelinkMatchesReferenceImplementation() {
    for n in 2 ... 5 {
      let elements = (0 ..< n).map(String.init)

      for i in 0 ..< n {
        for j in 0 ..< n where i != j {
          assertRelinkBefore(elements, moving: i, target: j)
          assertRelinkAfter(elements, moving: i, target: j)
        }
      }
    }
  }

  /// Asserts that relinking the element at position `i` before the one at position `j` produces
  /// the same order as the equivalent move on a plain `Array`.
  private func assertRelinkBefore(
    _ elements: [String], moving i: Int, target j: Int,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    var s = List(elements)
    let addresses = Array(s.addresses)

    // Reference: remove the moved element, then re-insert it before the target's value.
    var expected = elements
    let moved = expected.remove(at: i)
    let target = expected.firstIndex(of: elements[j])!
    expected.insert(moved, at: target)

    s.relink(addresses[i], before: addresses[j])

    assertConsistent(s, equals: expected, "moving \(i) before \(j)", file: file, line: line)
  }

  /// Asserts that relinking the element at position `i` after the one at position `j` produces
  /// the same order as the equivalent move on a plain `Array`.
  private func assertRelinkAfter(
    _ elements: [String], moving i: Int, target j: Int,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    var s = List(elements)
    let addresses = Array(s.addresses)

    // Reference: remove the moved element, then re-insert it after the target's value.
    var expected = elements
    let moved = expected.remove(at: i)
    let target = expected.firstIndex(of: elements[j])!
    expected.insert(moved, at: target + 1)

    s.relink(addresses[i], after: addresses[j])

    assertConsistent(s, equals: expected, "moving \(i) after \(j)", file: file, line: line)
  }

  /// Checks `relinkToStart(_:)` against a reference implementation on randomly generated lists,
  /// moving every element in turn to the start.
  ///
  /// The property under test is that relinking the element at position `i` to the start yields the
  /// same order as removing that element from a plain `Array` and re-inserting it at the front.
  func testRelinkToStartMatchesReferenceImplementation() {
    var rng = SplitMix64(seed: 0x5EED_CAFE)

    for _ in 0 ..< 100 {
      let elements = randomElements(maxCount: 8, using: &rng)
      guard !elements.isEmpty else { continue }

      let i = Int.random(in: 0 ..< elements.count, using: &rng)

      var s = List(elements)

      var expected = elements
      let moved = expected.remove(at: i)
      expected.insert(moved, at: 0)

      let a = Array(s.addresses)[i]
      s.relinkToStart(a)

      assertConsistent(s, equals: expected, "moving \(i) to start")
    }
  }

  /// Checks `relinkToEnd(_:)` against a reference implementation on randomly generated lists,
  /// moving every element in turn to the end.
  ///
  /// The property under test is that relinking the element at position `i` to the end yields the
  /// same order as removing that element from a plain `Array` and appending it at the back.
  func testRelinkToEndMatchesReferenceImplementation() {
    var rng = SplitMix64(seed: 0xC0FF_EE42)

    for _ in 0 ..< 100 {
      let elements = randomElements(maxCount: 8, using: &rng)
      guard !elements.isEmpty else { continue }

      let i = Int.random(in: 0 ..< elements.count, using: &rng)

      var s = List(elements)

      var expected = elements
      let moved = expected.remove(at: i)
      expected.append(moved)

      let a = Array(s.addresses)[i]
      s.relinkToEnd(a)

      assertConsistent(s, equals: expected, "moving \(i) to end")
    }
  }

  /// Returns a list of between `0` and `maxCount` distinct elements, drawn using `rng`.
  private func randomElements<R: RandomNumberGenerator>(
    maxCount: Int, using rng: inout R
  ) -> [String] {
    let n = Int.random(in: 0 ... maxCount, using: &rng)
    return (0 ..< n).map(String.init)
  }

  /// Asserts that `s` holds exactly `expected` when traversed forwards, backwards, and that its
  /// `count` agrees, so that both the `nextOffset` and `previousOffset` links are checked.
  private func assertConsistent(
    _ s: List<String>, equals expected: [String], _ message: String,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    let context = "n=\(expected.count) \(message)"

    XCTAssertEqual(Array(s), expected, "forwards: \(context)", file: file, line: line)
    XCTAssertEqual(s.count, expected.count, "count: \(context)", file: file, line: line)

    // Walk the list from its tail to its head following `previousOffset` links.
    var backwards: [String] = []
    var address = s.lastAddress
    while let a = address {
      backwards.append(s[a])
      address = s.address(before: a)
    }
    XCTAssertEqual(
      backwards, Array(expected.reversed()), "backwards: \(context)", file: file, line: line)
  }

}

/// A deterministic, seedable pseudo-random number generator, used to make the property-based
/// tests reproducible.
private struct SplitMix64: RandomNumberGenerator {

  private var state: UInt64

  init(seed: UInt64) {
    self.state = seed
  }

  mutating func next() -> UInt64 {
    state &+= 0x9E37_79B9_7F4A_7C15
    var z = state
    z = (z ^ (z >> 30)) &* 0xBF58_476D_1CE4_E5B9
    z = (z ^ (z >> 27)) &* 0x94D0_49BB_1331_11EB
    return z ^ (z >> 31)
  }

}
