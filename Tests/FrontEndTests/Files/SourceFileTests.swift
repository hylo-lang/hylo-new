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
    XCTAssertEqual(f.line(0).text.dropLast(), "Hello,")  // Handles newlines on Windows.
    XCTAssertEqual(f.line(1).text, "World!")
  }

  func testLineContaining() throws {
    let f = SourceFile.helloWorld
    let i1 = try XCTUnwrap(f.text.firstIndex(of: ","))
    XCTAssertEqual(f.line(containing: i1).index, 0)
    let i2 = try XCTUnwrap(f.text.firstIndex(of: "!"))
    XCTAssertEqual(f.line(containing: i2).index, 1)
  }

  func testLineAndOffsetNumbers() {
    let f = SourceFile.helloWorld
    let p1 = SourcePosition(f.startIndex, in: f)
    XCTAssertEqual(p1.lineAndOffset.line, 0)
    XCTAssertEqual(p1.lineAndOffset.offset, 0)

    let p2 = SourcePosition(f.endIndex, in: f)
    XCTAssertEqual(p2.lineAndOffset.line, 1)
    XCTAssertEqual(p2.lineAndOffset.offset, 6)
  }

  func testLineAndOffsetCountsSurrogatePairAsOneUnit() throws {
    // '😀' is U+1F600, a single grapheme cluster despite being 2 UTF-16 code units.
    // Grapheme-cluster offset of 'b' should be 2, not 3 as it would be for UTF-16.
    let f = SourceFile(contents: "a😀b")
    let b = try XCTUnwrap(f.text.firstIndex(of: "b"))
    let p = SourcePosition(b, in: f)
    XCTAssertEqual(p.lineAndOffset.line, 0)
    XCTAssertEqual(p.lineAndOffset.offset, 2)
  }

  func testLineAndUTF16OffsetAtStartOfFile() {
    let f = SourceFile.helloWorld
    let p = SourcePosition(f.startIndex, in: f)
    XCTAssertEqual(p.lineAndUTF16Offset.line, 0)
    XCTAssertEqual(p.lineAndUTF16Offset.offset, 0)
  }

  func testLineAndUTF16OffsetOfASCIICharacterOnFirstLine() throws {
    let f = SourceFile.helloWorld
    let comma = try XCTUnwrap(f.text.firstIndex(of: ","))
    let p = SourcePosition(comma, in: f)
    XCTAssertEqual(p.lineAndUTF16Offset.line, 0)
    XCTAssertEqual(p.lineAndUTF16Offset.offset, 5)
  }

  func testLineAndUTF16OffsetAtStartOfSecondLine() throws {
    let f = SourceFile.helloWorld
    let w = try XCTUnwrap(f.text.firstIndex(of: "W"))
    let p = SourcePosition(w, in: f)
    XCTAssertEqual(p.lineAndUTF16Offset.line, 1)
    XCTAssertEqual(p.lineAndUTF16Offset.offset, 0)
  }

  func testLineAndUTF16OffsetAtEndOfFile() {
    let f = SourceFile.helloWorld
    let p = SourcePosition(f.endIndex, in: f)
    XCTAssertEqual(p.lineAndUTF16Offset.line, 1)
    XCTAssertEqual(p.lineAndUTF16Offset.offset, 6)
  }

  func testLineAndUTF16OffsetCountsSurrogatePairAsTwoUnits() throws {
    // '😀' is U+1F600, encoded as a surrogate pair (2 UTF-16 code units).
    // UTF-16 offset of 'b' should be 3, not 2 as it would be for grapheme clusters.
    let f = SourceFile(contents: "a😀b")
    let b = try XCTUnwrap(f.text.firstIndex(of: "b"))
    let p = SourcePosition(b, in: f)
    XCTAssertEqual(p.lineAndUTF16Offset.line, 0)
    XCTAssertEqual(p.lineAndUTF16Offset.offset, 3)
  }

  func testLineAndUTF16OffsetAfterSurrogatePairOnSecondLine() throws {
    let f = SourceFile(contents: "😀\nb")
    let b = try XCTUnwrap(f.text.firstIndex(of: "b"))
    let p = SourcePosition(b, in: f)
    XCTAssertEqual(p.lineAndUTF16Offset.line, 1)
    XCTAssertEqual(p.lineAndUTF16Offset.offset, 0)
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
    XCTAssertEqual(f.index(line: 0, extendedGraphemeClusterOffset: 0), f.text.startIndex)
  }

  func testIndexWithinFirstLine() throws {
    let f = SourceFile.helloWorld
    let comma = try XCTUnwrap(f.text.firstIndex(of: ","))
    XCTAssertEqual(f.index(line: 0, extendedGraphemeClusterOffset: 5), comma)
  }

  func testIndexAtStartOfSecondLine() throws {
    let f = SourceFile.helloWorld
    let line2Start = f.text.index(after: try XCTUnwrap(f.text.firstIndex(where: \.isNewline)))
    XCTAssertEqual(f.index(line: 1, extendedGraphemeClusterOffset: 0), line2Start)
  }

  func testIndexAtLastCharacter() throws {
    let f = SourceFile.helloWorld
    let bang = try XCTUnwrap(f.text.firstIndex(of: "!"))
    XCTAssertEqual(f.index(line: 1, extendedGraphemeClusterOffset: 5), bang)
  }

  // MARK: - extendedGraphemeClusterOffset clamping

  func testGraphemeClusterColumnClampsNegativeLine() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: -1, extendedGraphemeClusterOffset: 0), f.startIndex)
  }

  func testGraphemeClusterColumnClampsLineOverflow() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: 100, extendedGraphemeClusterOffset: 0), f.endIndex)
  }

  func testGraphemeClusterColumnClampsOffsetOverflow() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: 0, extendedGraphemeClusterOffset: 999), f.endIndex)
  }

  // MARK: - UTF-16 index

  func testUTF16IndexAtStartOfFile() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: 0, utf16Offset: 0), f.text.startIndex)
  }

  func testUTF16IndexWithinFirstLine() throws {
    let f = SourceFile.helloWorld
    let comma = try XCTUnwrap(f.text.firstIndex(of: ","))
    XCTAssertEqual(f.index(line: 0, utf16Offset: 5), comma)
  }

  func testUTF16IndexAtStartOfSecondLine() throws {
    let f = SourceFile.helloWorld
    let line2Start = f.text.index(after: try XCTUnwrap(f.text.firstIndex(where: \.isNewline)))
    XCTAssertEqual(f.index(line: 1, utf16Offset: 0), line2Start)
  }

  func testUTF16IndexWithSurrogatePair() throws {
    // "a😀b" — '😀' is U+1F600, 2 UTF-16 code units
    let f = SourceFile(contents: "a😀b")
    let b = try XCTUnwrap(f.text.firstIndex(of: "b"))
    // 'a' at UTF-16 offset 0, '😀' at 1–2, 'b' at 3
    XCTAssertEqual(f.index(line: 0, utf16Offset: 3), b)
  }

  func testUTF16IndexAfterSurrogatePairOnSecondLine() throws {
    let f = SourceFile(contents: "😀\nb")
    let b = try XCTUnwrap(f.text.firstIndex(of: "b"))
    XCTAssertEqual(f.index(line: 1, utf16Offset: 0), b)
  }

  // MARK: - UTF-16 clamping

  func testUTF16IndexClampsNegativeLine() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: -1, utf16Offset: 0), f.startIndex)
  }

  func testUTF16IndexClampsLineOverflow() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: 100, utf16Offset: 0), f.endIndex)
  }

  func testUTF16IndexClampsOffsetOverflow() {
    let f = SourceFile.helloWorld
    XCTAssertEqual(f.index(line: 0, utf16Offset: 999), f.endIndex)
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
