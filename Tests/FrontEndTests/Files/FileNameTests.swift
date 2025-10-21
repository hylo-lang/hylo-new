import Archivist
import FrontEnd
import XCTest

final class FileNameTests: XCTestCase {

  func testDescription() {
    XCTAssertEqual(FileName.local(.init(filePath: "/foo/bar")).description, "/foo/bar")
    XCTAssertEqual(FileName.virtual(1234).description, "virtual://ya")
    XCTAssertEqual(FileName.localInMemory(.init(filePath: "/foo/bar")).description, "/foo/bar#inmemory")
  }

  func testArchive() throws {
    let f1 = FileName.local(.init(filePath: "/foo/bar"))
    try XCTAssertEqual(f1, f1.storedAndLoaded())
    let f2 = FileName.virtual(1234)
    try XCTAssertEqual(f2, f2.storedAndLoaded())
    let f3 = FileName.localInMemory(.init(filePath: "/foo/bar"))
    try XCTAssertEqual(f3, f3.storedAndLoaded())
  }

  func testLexicographicallyPrecedes() {
    // local < localInMemory < virtual

    let f1 = FileName.local(.init(filePath: "/foo/bar"))
    let f2 = FileName.local(.init(filePath: "/foo/ham"))
    XCTAssert(f1.lexicographicallyPrecedes(f2))
    XCTAssertFalse(f2.lexicographicallyPrecedes(f1))
    XCTAssertFalse(f1.lexicographicallyPrecedes(f1))

    let f3 = FileName.virtual(1234)
    let f4 = FileName.virtual(1235)
    XCTAssert(f3.lexicographicallyPrecedes(f4))
    XCTAssertFalse(f4.lexicographicallyPrecedes(f3))
    XCTAssertFalse(f3.lexicographicallyPrecedes(f3))

    let f5 = FileName.localInMemory(.init(filePath: "/foo/bar"))
    let f6 = FileName.localInMemory(.init(filePath: "/foo/ham"))
    XCTAssert(f5.lexicographicallyPrecedes(f6))
    XCTAssertFalse(f6.lexicographicallyPrecedes(f5))
    XCTAssertFalse(f5.lexicographicallyPrecedes(f5))

    XCTAssert(f1.lexicographicallyPrecedes(f5))
    XCTAssertFalse(f5.lexicographicallyPrecedes(f1))
    XCTAssert(f5.lexicographicallyPrecedes(f3))
    XCTAssertFalse(f3.lexicographicallyPrecedes(f5))
    XCTAssert(f1.lexicographicallyPrecedes(f3))
    XCTAssertFalse(f3.lexicographicallyPrecedes(f1))
  }

  func testGNUPath() {
    let f = FileName.local(.init(filePath: "/foo/bar"))

    XCTAssertEqual(f.gnuPath(relativeTo: URL(filePath: "/foo")), "bar")
    XCTAssertEqual(f.gnuPath(relativeTo: URL(filePath: "/foo/bar")), ".")
    XCTAssertEqual(f.gnuPath(relativeTo: URL(filePath: "/ham")), "../foo/bar")
    XCTAssertEqual(f.gnuPath(relativeTo: URL(filePath: "/foo/bar/ham")), "..")

    XCTAssertNil(f.gnuPath(relativeTo: URL.init(string: "https://abc.ch")!))

    // localInMemory behaves the same as local
    let fInMemory = FileName.localInMemory(.init(filePath: "/foo/bar"))
    XCTAssertEqual(fInMemory.gnuPath(relativeTo: URL(filePath: "/foo")), "bar")
    XCTAssertEqual(fInMemory.gnuPath(relativeTo: URL(filePath: "/foo/bar")), ".")
    XCTAssertEqual(fInMemory.gnuPath(relativeTo: URL(filePath: "/ham")), "../foo/bar")
    XCTAssertEqual(fInMemory.gnuPath(relativeTo: URL(filePath: "/foo/bar/ham")), "..")
    XCTAssertNil(fInMemory.gnuPath(relativeTo: URL.init(string: "https://abc.ch")!))

    // Test that virtual returns nil
    let fVirtual = FileName.virtual(1234)
    XCTAssertNil(fVirtual.gnuPath(relativeTo: URL(filePath: "/foo")))
  }

}
