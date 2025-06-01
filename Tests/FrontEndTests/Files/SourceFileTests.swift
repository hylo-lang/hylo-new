import FrontEnd
import XCTest

final class SourceFileTests: XCTestCase {

  func testVirtualNames() {
    let f: SourceFile = "Hello."
    let g: SourceFile = "Hello."
    let h: SourceFile = "Bye."
    XCTAssertEqual(f.name, g.name)
    XCTAssertNotEqual(f.name, h.name)
  }

  func testVirtualText() {
    let f: SourceFile = "Hello."
    XCTAssertEqual(f.text, "Hello.")
  }

  func testLocalText() throws {
    try FileManager.default.withTemporaryFile(containing: "Hello.") { (u) in
      let f = try SourceFile(contentsOf: u)
      XCTAssertEqual(f.text, "Hello.")
    }
  }

  func testSpan() {
    let f: SourceFile = "Hello."
    XCTAssertEqual(f.span.region, f.text.startIndex ..< f.text.endIndex)
  }

  func testSubscript() {
    let f: SourceFile = "Hello."
    XCTAssertEqual(f[f.span], "Hello.")
  }

  func testLineIndex() throws {
    let f = SourceFile.helloWorld
    try XCTSkipIf(f.lineCount != 2)
    XCTAssertEqual(f.line(1).text.dropLast(), "Hello,")  // Handles newlines on Windows.
    XCTAssertEqual(f.line(2).text, "World!")
  }

  func testLineContaining() throws {
    let f = SourceFile.helloWorld
    let i1 = try XCTUnwrap(f.text.firstIndex(of: ","))
    XCTAssertEqual(f.line(containing: i1).number, 1)
    let i2 = try XCTUnwrap(f.text.firstIndex(of: "!"))
    XCTAssertEqual(f.line(containing: i2).number, 2)
  }

  func testLineAndColumnNumbers() {
    let f = SourceFile.helloWorld
    let p1 = SourcePosition(f.startIndex, in: f)
    XCTAssertEqual(p1.lineAndColumn.line, 1)
    XCTAssertEqual(p1.lineAndColumn.column, 1)

    let p2 = SourcePosition(f.endIndex, in: f)
    XCTAssertEqual(p2.lineAndColumn.line, 2)
    XCTAssertEqual(p2.lineAndColumn.column, 7)
  }

  func testLineDescription() {
    let f = SourceFile.helloWorld
    let l = f.line(containing: f.text.startIndex)
    XCTAssertEqual(l.description, "virtual://350c8wstjkie0:1")
  }

  func testPositionDescrption() throws {
    let f = SourceFile.helloWorld
    let i1 = try XCTUnwrap(f.text.firstIndex(of: ","))
    let p1 = SourcePosition(i1, in: f)
    XCTAssertEqual(p1.description, "virtual://350c8wstjkie0:1:6")
    let i2 = try XCTUnwrap(f.text.firstIndex(of: "!"))
    let p2 = SourcePosition(i2, in: f)
    XCTAssertEqual(p2.description, "virtual://350c8wstjkie0:2:6")
  }

  func testArchive() throws {
    let f = SourceFile.helloWorld
    try XCTAssertEqual(f, f.storedAndLoaded())
  }

}

extension SourceFile {

  fileprivate static let helloWorld: Self = """
    Hello,
    World!
    """

}
