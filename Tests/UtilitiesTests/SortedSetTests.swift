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

  func testRemove() {
    var s: SortedSet = ["a", "b", "c"]
    XCTAssertNotNil(s.remove("a"))
    XCTAssertNil(s.remove("a"))
    XCTAssertNil(s.remove("z"))
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

}
