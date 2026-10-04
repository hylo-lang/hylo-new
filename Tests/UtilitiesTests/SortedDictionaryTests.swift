import Utilities
import XCTest

final class SortedDictionaryTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = SortedDictionary<Int, String>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testInitWithDictionaryLiteral() {
    let s: SortedDictionary = [1: "a", 2: "b"]
    XCTAssert(s.keys.elementsEqual([1, 2]))
    XCTAssert(s.values.elementsEqual(["a", "b"]))
  }

  func testUpdateValueAt() {
    var s: SortedDictionary = ["abc": 123, "def": 456, "ghi": 789]
    let v = s.updateValue(0, at: 2)
    XCTAssertEqual(v, 789)
    XCTAssertEqual(s["ghi"], 0)
  }

  func testMerging() {
    let s0: SortedDictionary = [1: "a", 2: "b", 4: "d", 5: "e"]

    XCTAssert(s0.merging(SortedDictionary(), uniquingKeysWith: +) == s0)
    XCTAssert(SortedDictionary().merging(s0, uniquingKeysWith: +) == s0)

    let s1: SortedDictionary = [1: "a", 2: "b", 3: "c"]
    let s2: SortedDictionary = [2: "b", 6: "f"]

    let t0 = s0.merging(s1, uniquingKeysWith: +)
    XCTAssert(t0.keys.elementsEqual([1, 2, 3, 4, 5]))
    XCTAssert(t0.values.elementsEqual(["aa", "bb", "c", "d", "e"]))

    let t1 = s0.merging(s2, uniquingKeysWith: +)
    XCTAssert(t1.keys.elementsEqual([1, 2, 4, 5, 6]))
    XCTAssert(t1.values.elementsEqual(["a", "bb", "d", "e", "f"]))
  }

  func testRemoveAt() {
    var s: SortedDictionary = [1: "a", 2: "b", 3: "c", 4: "d"]
    s.remove(at: 1)
    XCTAssert(s.keys.elementsEqual([1, 3, 4]))
    XCTAssert(s.values.elementsEqual(["a", "c", "d"]))
    s.remove(at: 2)
    XCTAssert(s.keys.elementsEqual([1, 3]))
    XCTAssert(s.values.elementsEqual(["a", "c"]))
    s.remove(at: 0)
    XCTAssert(s.keys.elementsEqual([3]))
    XCTAssert(s.values.elementsEqual(["c"]))
  }

  func testRemoveAllWhere() {
    var s: SortedDictionary = [1: "a", 2: "b", 3: "c", 4: "d"]
    s.removeAll(where: { (i, _) in (i & 1) != 0 })
    XCTAssert(s.keys.elementsEqual([2, 4]))
    XCTAssert(s.values.elementsEqual(["b", "d"]))
  }

  func testRemoveLast() {
    var s: SortedDictionary = [1: "a", 2: "b", 3: "c", 4: "d"]
    s.removeLast(3)
    XCTAssert(s.keys.elementsEqual([1]))
    XCTAssert(s.values.elementsEqual(["a"]))
  }

}
