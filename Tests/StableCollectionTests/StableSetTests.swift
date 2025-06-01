import XCTest
import MoreCollections

class StableSetTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = StableSet<String>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testIsEmpty() {
    var s = StableSet<String>()
    XCTAssert(s.isEmpty)
    s.insert("a")
    XCTAssertFalse(s.isEmpty)
  }

  func testCount() {
    var s = StableSet<String>()
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

  func testInitWithSequence() {
    let members = ["a", "b"]
    let s = StableSet<String>(members)
    XCTAssert(s.elementsEqual(members))
  }

  func testInitWithArrayLiteral() {
    let s: StableSet = ["a", "b"]
    XCTAssert(s.elementsEqual(["a", "b"]))
  }

  func testFirstIndexOf() {
    var s = StableSet<String>()
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
    XCTAssertEqual(s.firstIndex(of: "c"), 2)
  }


  func testContains() {
    var s = StableSet<String>()
    XCTAssertFalse(s.contains("a"))
    s.insert("a") // insert
    XCTAssert(s.contains("a"))
    s.remove("a") // delete
    XCTAssertFalse(s.contains("a"))
    s.remove("a") // no-op
    XCTAssertFalse(s.contains("a"))
  }


  func testInsert() {
    var s = StableSet<String>()

    let p0 = s.insert("a")
    XCTAssert(p0.inserted)
    XCTAssertEqual(p0.position, 0)
    XCTAssertEqual(s[p0.position], "a")

    let p1 = s.insert("a")
    XCTAssertFalse(p1.inserted)
    XCTAssertEqual(p1.position, 0)
    XCTAssertEqual(s[p0.position], "a")

    let p2 = s.insert("b")
    XCTAssert(p2.inserted)
    XCTAssertEqual(p2.position, 1)
    XCTAssertEqual(s[p2.position], "b")
  }

  func testReinsert() {
    var s: StableSet = ["a", "b", "c"]
    s.remove("b")
    s.insert("b")
    XCTAssertEqual(s.firstIndex(of: "b"), 1)
  }

  func testRemoveAt() {
    var s: StableSet = ["a", "b", "c"]
    XCTAssertEqual(s.remove(at: 1), "b")
    XCTAssertEqual(Array(s), ["a", "c"])
    XCTAssertEqual(s.remove(at: 2), "c")
    XCTAssertEqual(Array(s), ["a"])
  }

  func testRemoveMember() {
    var s: StableSet = ["a", "b", "c"]
    XCTAssert(s.remove("a"))
    XCTAssertFalse(s.remove("a"))
    XCTAssertFalse(s.remove("z"))
  }

  func testRemoveAll() {
    var s: StableSet = ["a", "b", "c"]
    s.removeAll()
    XCTAssert(s.isEmpty)

    s.insert("a")
    s.removeAll(keepingCapacity: true)
    XCTAssert(s.isEmpty)
    XCTAssertGreaterThanOrEqual(s.capacity, 1)

    s.insert("a")
    let t = s
    s.removeAll(keepingCapacity: true)
    XCTAssert(t.contains("a"))
    XCTAssert(s.isEmpty)
    XCTAssertGreaterThanOrEqual(s.capacity, 1)
  }

  func testReserveCapacity() {
    var s: StableSet = ["a", "b", "c"]
    let t = s
    s.reserveCapacity(100)
    XCTAssertEqual(s, t)
    XCTAssertNotEqual(s.capacity, t.capacity)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testIsValue() {
    let s: StableSet = ["a", "b", "c"]
    var t = s
    t.insert("d")
    XCTAssert(s.contains("a"))
    XCTAssert(t.contains("a"))
  }

  func testIsCollection() {
    var s: StableSet = ["a", "b", "c"]
    s.remove(at: 1)

    var i = s.startIndex
    XCTAssertEqual(s[i], "a")
    i = s.index(after: i)
    XCTAssertEqual(s[i], "c")
    i = s.index(after: i)
    XCTAssertEqual(i, s.endIndex)
  }

  func testIsBidirectionalCollection() {
    var s: StableSet = ["a", "b", "c"]
    s.remove(at: 1)

    var i = s.index(before: s.endIndex)
    XCTAssertEqual(s[i], "c")
    i = s.index(before: i)
    XCTAssertEqual(s[i], "a")
  }

  func testIsEquatable() {
    let s: StableSet = ["a", "b", "c"]
    let t: StableSet = ["a", "b", "c"]
    XCTAssertEqual(s, s)
    XCTAssertEqual(s, t)
    let u: StableSet = ["c", "b", "a"]
    XCTAssertNotEqual(s, u)
  }

  func testIsHashable() {
    let s: StableSet = ["a", "b", "c"]
    let t: StableSet = ["a", "b", "c"]
    XCTAssertEqual(s.hashValue, t.hashValue)
  }

  func testIsCustomStringConvertible() {
    let s: StableSet = [1, 2, 3]
    XCTAssertEqual(s.description, "[1, 2, 3]")
  }

}
