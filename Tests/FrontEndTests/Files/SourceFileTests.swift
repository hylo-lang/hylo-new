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
    XCTAssertEqual(l.description, "virtual:///350c8wstjkie0:1")
  }

  func testVirtualPositionDescription() throws {
    let f = SourceFile.helloWorld
    let i1 = try XCTUnwrap(f.text.firstIndex(of: ","))
    let p1 = SourcePosition(i1, in: f)
    XCTAssertEqual(p1.description, "virtual:///350c8wstjkie0:1:6")
    let i2 = try XCTUnwrap(f.text.firstIndex(of: "!"))
    let p2 = SourcePosition(i2, in: f)
    XCTAssertEqual(p2.description, "virtual:///350c8wstjkie0:2:6")
  }

  func testFilePositionDescription() throws {
    let f = SourceFile(name: .virtual(URL(string: "file:///home/hylo/a.hylo")!), contents: "")
    let p = SourcePosition(f.startIndex, in: f)
    XCTAssertEqual(f.name.description, "/home/hylo/a.hylo")
    XCTAssertEqual(p.description, "/home/hylo/a.hylo:1:1")
  }

  func testLineCount() {
    XCTAssertEqual(SourceFile.helloWorld.lineCount, 2)
  }

  func testIndexAtStartOfFile() throws {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: 1, column: 1), f.text.startIndex)
  }

  func testIndexWithinFirstLine() throws {
    let f = SourceFile.helloWorld
    let comma = try XCTUnwrap(f.text.firstIndex(of: ","))
    XCTAssertEqual(f.index(line: 1, column: 6), comma)
  }

  func testIndexAtStartOfSecondLine() throws {
    let f = SourceFile.helloWorld
    let line2Start = f.text.index(after: try XCTUnwrap(f.text.firstIndex(where: \.isNewline)))
    XCTAssertEqual(f.index(line: 2, column: 1), line2Start)
  }

  func testIndexAtLastCharacter() throws {
    let f = SourceFile.helloWorld
    let bang = try XCTUnwrap(f.text.firstIndex(of: "!"))
    XCTAssertEqual(f.index(line: 2, column: 6), bang)
  }

  func testArchive() throws {
    let f = SourceFile.helloWorld
    try XCTAssertEqual(f, f.storedAndLoaded())
  }

  func testInMemoryContents() {
    let f = SourceFile(name: .local(URL(string: "file:///tmp/test.hylo")!), contents: "fun main()")
    XCTAssertEqual(f.text, "fun main()")
    XCTAssertEqual(f.name, .local(URL(string: "file:///tmp/test.hylo")!))
  }

  /// Tests that when a file is created with a relative URL, it is equivalent 
  /// to creating it with an absolute URL.
  func testRelativePath() {
    let nonCanonical = URL(fileURLWithPath: "a/../README.md")
    let relative = URL(fileURLWithPath: "README.md")
    let absolute = relative.absoluteURL

    let sn = SourceFile(name: .local(nonCanonical), contents: "hello")
    let sr = SourceFile(name: .local(relative), contents: "hello")
    let sa = SourceFile(name: .local(absolute), contents: "hello")

    XCTAssertEqual(sr.baseName, "README")
    XCTAssertEqual(sa.baseName, "README")
    XCTAssertEqual(sn.baseName, "README")

    XCTAssertEqual(sr, sa)
    XCTAssertEqual(sn, sa)
    XCTAssertEqual(sr.hashValue, sa.hashValue)
    XCTAssertEqual(sn.hashValue, sa.hashValue)

    XCTAssertEqual(sr.name.url, absolute)
    XCTAssertEqual(sn.name.url, absolute)
  }

  func testVirtualBaseName() {
    let s = SourceFile(name: .virtual(URL(string: "virtual:///tests/something.txt")!), contents: "")
    XCTAssertEqual(s.baseName, "something")
  }

}

extension SourceFile {

  fileprivate static let helloWorld: Self = """
    Hello,
    World!
    """

}
