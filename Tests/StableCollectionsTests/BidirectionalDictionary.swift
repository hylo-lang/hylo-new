import StableCollections
import XCTest

final class BidirectionalDictionaryTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = BidirectionalDictionary<String, Int>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testInitWithKeyValuePairs() {
    let pairs = [("a", 1), ("b", 2)]
    let s = BidirectionalDictionary<String, Int>(uniqueKeysAndValues: pairs)
    XCTAssert(s.elementsEqual(pairs, by: { (a, b) in (a.0 == b.0) && (a.1 == b.1) }))
  }

  func testInitWithDictionaryLiteral() {
    let pairs = [("a", 1), ("b", 2)]
    let s: BidirectionalDictionary = ["a": 1, "b": 2]
    XCTAssert(s.elementsEqual(pairs, by: { (a, b) in (a.0 == b.0) && (a.1 == b.1) }))
  }

  func testIsEmpty() {
    var s = BidirectionalDictionary<String, Int>()
    XCTAssert(s.isEmpty)
    s.assignValue(1, forKey: "a")
    XCTAssertFalse(s.isEmpty)
  }

  func testCount() {
    var s = BidirectionalDictionary<String, Int>()
    XCTAssertEqual(s.count, 0)
    s.assignValue(100, forKey: "a")
    XCTAssertEqual(s.count, 1)
    s.assignValue(200, forKey: "b")
    XCTAssertEqual(s.count, 2)
    s.remove(key: "a")
    XCTAssertEqual(s.count, 1)
    s.remove(value: 200)
    XCTAssertEqual(s.count, 0)
  }

  func testKeySubscript() {
    var s = BidirectionalDictionary<String, Int>()
    s.assignValue(100, forKey: "a")
    XCTAssertEqual(s[key: "a"], 100)
    s.assignValue(200, forKey: "a")
    XCTAssertEqual(s[key: "a"], 200)
    s.assignValue(200, forKey: "b")
    XCTAssertEqual(s[key: "a"], nil)
  }

  func testAssignValueForKey() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2]

    // Update does not change any key/value pair.
    s.assignValue(3, forKey: "c")
    XCTAssertEqual(s[key: "c"], 3)
    XCTAssertEqual(s[value: 3], "c")

    // Updates modifies one end of an existing key/value pair.
    s.assignValue(4, forKey: "b")
    XCTAssertEqual(s[key: "b"], 4)
    XCTAssertEqual(s[value: 4], "b")
    XCTAssertNil(s[value: 2])

    // Update removes two existing key/value pairs.
    s.assignValue(3, forKey: "a")
    XCTAssertEqual(s[key: "a"], 3)
    XCTAssertEqual(s[value: 3], "a")
    XCTAssertNil(s[key: "c"])
    XCTAssertNil(s[value: 1])
  }

  func testRemoveKey() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2]
    let a = s.remove(key: "a")
    XCTAssertEqual(a, 1)
    XCTAssertNil(s[key: "a"])
    XCTAssertNil(s.remove(key: "c"))
  }

  func testRemoveValue() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2]
    let a = s.remove(value: 1)
    XCTAssertEqual(a, "a")
    XCTAssertNil(s[value: 1])
    XCTAssertNil(s.remove(value: 3))
  }

  func testRemoveAll() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2, "c": 3]
    s.removeAll()
    XCTAssert(s.isEmpty)

    s.assignValue(1, forKey: "a")
    s.removeAll(keepingCapacity: true)
    XCTAssert(s.isEmpty)
    XCTAssertGreaterThanOrEqual(s.capacity, 1)

    s.assignValue(1, forKey: "a")
    let t = s
    s.removeAll(keepingCapacity: true)
    XCTAssertEqual(t[key: "a"], 1)
    XCTAssert(s.isEmpty)
    XCTAssertGreaterThanOrEqual(s.capacity, 1)
  }

  func testReserveCapacity() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2, "c": 3]
    let t = s
    s.reserveCapacity(100)
    XCTAssertEqual(s, t)
    XCTAssertNotEqual(s.capacity, t.capacity)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testIsCollection() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2, "c": 3]
    s.remove(key: "b")

    var i = s.startIndex
    XCTAssert(s[i] == ("a", 1))
    i = s.index(after: i)
    XCTAssert(s[i] == ("c", 3))
    i = s.index(after: i)
    XCTAssertEqual(i, s.endIndex)
  }

  func testIsBidirectionalCollection() {
    var s: BidirectionalDictionary = ["a": 1, "b": 2, "c": 3]
    s.remove(key: "b")

    var i = s.index(before: s.endIndex)
    XCTAssert(s[i] == ("c", 3))
    i = s.index(before: i)
    XCTAssert(s[i] == ("a", 1))
  }


  func testIsCustomStringConvertible() {
    let s: BidirectionalDictionary = [1: -1, 2: -2]
    XCTAssertEqual(s.description, "[1: -1, 2: -2]")

    let l = (0 ..< 100).map({ ($0, $0.description) })
    let m = "[" + l.lazy.map({ (a, b) in "\(a): \(b)" }).joined(separator: ", ") + "]"
    let t: StableDictionary = .init(uniqueKeysAndValues: l)
    XCTAssertEqual(t.description, m)
  }

}
