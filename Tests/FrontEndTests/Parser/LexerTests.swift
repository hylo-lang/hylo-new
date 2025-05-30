import FrontEnd
import XCTest

final class LexerTests: XCTestCase {

  func testLineComments() throws {
    let input: SourceFile = """
      Hello // comment
      World
      """
    var scanner = Lexer(tokenizing: input)
    try assertNext(from: &scanner, is: .name)
    try assertNext(from: &scanner, is: .name)
    XCTAssertNil(scanner.next())
  }

  func testBlockComments() throws {
    let input: SourceFile = """
      Hello /* comment-0 *//* /* comment-1 */ comment-2 */
      World
      """
    var scanner = Lexer(tokenizing: input)
    try assertNext(from: &scanner, is: .name)
    try assertNext(from: &scanner, is: .name)
    XCTAssertNil(scanner.next())
  }

  func testUnterminatedBlockComment() throws {
    var scanner = Lexer(tokenizing: "/* /* comment-1 */ comment-2 World")
    try assertNext(from: &scanner, is: .unterminatedBlockComment)
    XCTAssertNil(scanner.next())
  }

  func testDelimiters() throws {
    var scanner = Lexer(tokenizing: "<<({[]})>>")
    try assertNext(from: &scanner, is: .leftAngle)
    try assertNext(from: &scanner, is: .leftAngle)
    try assertNext(from: &scanner, is: .leftParenthesis)
    try assertNext(from: &scanner, is: .leftBrace)
    try assertNext(from: &scanner, is: .leftBracket)
    try assertNext(from: &scanner, is: .rightBracket)
    try assertNext(from: &scanner, is: .rightBrace)
    try assertNext(from: &scanner, is: .rightParenthesis)
    try assertNext(from: &scanner, is: .rightAngle)
    try assertNext(from: &scanner, is: .rightAngle)
    XCTAssertNil(scanner.next())
  }

  func testError() throws {
    var scanner = Lexer(tokenizing: "\0.")
    try assertNext(from: &scanner, is: .error)
    try assertNext(from: &scanner, is: .dot)
    XCTAssertNil(scanner.next())
  }

  func testDecimalIntegerLiteral() throws {
    var scanner = Lexer(tokenizing: "0 001 42 00 1_234 1_2__34__ -1 -a")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "001")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "42")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "00")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "1_234")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "1_2__34__")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "-1")
    try assertNext(from: &scanner, is: .operator, withValue: "-")
    try assertNext(from: &scanner, is: .name, withValue: "a")
  }

  func testHexadecimalIntegerLiteral() throws {
    var scanner = Lexer(tokenizing: "0x0123 0xabcdef 0x1__0_a_ 0xg 0x -0x1")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0x0123")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0xabcdef")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0x1__0_a_")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .name, withValue: "xg")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .name, withValue: "x")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "-0x1")
  }

  func testOctalIntegerLiteral() throws {
    var scanner = Lexer(tokenizing: "0o0123 0o1__0_6_ 0o8 0o -0o1")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0o0123")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0o1__0_6_")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .name, withValue: "o8")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .name, withValue: "o")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "-0o1")
  }

  func testBinaryIntegerLiteral() throws {
    var scanner = Lexer(tokenizing: "0b01 0b1__0_1_ 0b8 0b -0b1")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0b01")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0b1__0_1_")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .name, withValue: "b8")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "0")
    try assertNext(from: &scanner, is: .name, withValue: "b")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "-0b1")
  }

  func testFloatingPointerLiteral() throws {
    var scanner = Lexer(tokenizing: "0.0 0_.0_ 0.1__2_ 1e1_000 1.12e+1_3 3.45E-6 1. 1.x 1e -1e2")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "0.0")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "0_.0_")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "0.1__2_")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "1e1_000")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "1.12e+1_3")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "3.45E-6")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "1")
    try assertNext(from: &scanner, is: .dot)
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "1")
    try assertNext(from: &scanner, is: .dot)
    try assertNext(from: &scanner, is: .name, withValue: "x")
    try assertNext(from: &scanner, is: .integerLiteral, withValue: "1")
    try assertNext(from: &scanner, is: .name, withValue: "e")
    try assertNext(from: &scanner, is: .floatingPointLiteral, withValue: "-1e2")
  }

  func testStringLiteral() throws {
    var scanner = Lexer(tokenizing: #""" "a 0+ " "a\nb" "a\"" "abc "#)
    try assertNext(from: &scanner, is: .stringLiteral, withValue: #""""#)
    try assertNext(from: &scanner, is: .stringLiteral, withValue: #""a 0+ ""#)
    try assertNext(from: &scanner, is: .stringLiteral, withValue: #""a\nb""#)
    try assertNext(from: &scanner, is: .stringLiteral, withValue: #""a\"""#)
    try assertNext(from: &scanner, is: .unterminatedStringLiteral, withValue: #""abc "#)
  }

  func testIdentifier() throws {
    var scanner = Lexer(tokenizing: "a _a _0 \u{3042}\u{3042} _")
    try assertNext(from: &scanner, is: .name, withValue: "a")
    try assertNext(from: &scanner, is: .name, withValue: "_a")
    try assertNext(from: &scanner, is: .name, withValue: "_0")
    try assertNext(from: &scanner, is: .name, withValue: "\u{3042}\u{3042}")
    try assertNext(from: &scanner, is: .underscore)
    XCTAssertNil(scanner.next())
  }

  func testKeywords() throws {
    let input: SourceFile = """
      auto case else enum extension false fun given if import infix init inout internal let match
      postfix prefix private public return set sink static struct subscript trait true type
      typealias var where
      """
    var scanner = Lexer(tokenizing: input)
    try assertNext(from: &scanner, is: .auto)
    try assertNext(from: &scanner, is: .case)
    try assertNext(from: &scanner, is: .else)
    try assertNext(from: &scanner, is: .enum)
    try assertNext(from: &scanner, is: .extension)
    try assertNext(from: &scanner, is: .false)
    try assertNext(from: &scanner, is: .fun)
    try assertNext(from: &scanner, is: .given)
    try assertNext(from: &scanner, is: .if)
    try assertNext(from: &scanner, is: .import)
    try assertNext(from: &scanner, is: .infix)
    try assertNext(from: &scanner, is: .`init`)
    try assertNext(from: &scanner, is: .inout)
    try assertNext(from: &scanner, is: .internal)
    try assertNext(from: &scanner, is: .let)
    try assertNext(from: &scanner, is: .match)
    try assertNext(from: &scanner, is: .postfix)
    try assertNext(from: &scanner, is: .prefix)
    try assertNext(from: &scanner, is: .private)
    try assertNext(from: &scanner, is: .public)
    try assertNext(from: &scanner, is: .return)
    try assertNext(from: &scanner, is: .set)
    try assertNext(from: &scanner, is: .sink)
    try assertNext(from: &scanner, is: .static)
    try assertNext(from: &scanner, is: .struct)
    try assertNext(from: &scanner, is: .subscript)
    try assertNext(from: &scanner, is: .trait)
    try assertNext(from: &scanner, is: .true)
    try assertNext(from: &scanner, is: .type)
    try assertNext(from: &scanner, is: .typealias)
    try assertNext(from: &scanner, is: .var)
    try assertNext(from: &scanner, is: .where)
    XCTAssertNil(scanner.next())
  }

  func testPoundLiteral() throws {
    var scanner = Lexer(tokenizing: "#a #0 #")
    try assertNext(from: &scanner, is: .poundLiteral, withValue: "#a")
    try assertNext(from: &scanner, is: .poundLiteral, withValue: "#0")
    try assertNext(from: &scanner, is: .error)
  }

  func testOperator() throws {
    var scanner = Lexer(tokenizing: "<= ++ & &&& -> == +* *+ *> (+)")
    try assertNext(from: &scanner, is: .leftAngle)
    try assertNext(from: &scanner, is: .assign)
    try assertNext(from: &scanner, is: .operator, withValue: "++")
    try assertNext(from: &scanner, is: .ampersand)
    try assertNext(from: &scanner, is: .operator, withValue: "&&&")
    try assertNext(from: &scanner, is: .arrow)
    try assertNext(from: &scanner, is: .equal)
    try assertNext(from: &scanner, is: .operator, withValue: "+*")
    try assertNext(from: &scanner, is: .star)
    try assertNext(from: &scanner, is: .operator, withValue: "+")
    try assertNext(from: &scanner, is: .star)
    try assertNext(from: &scanner, is: .rightAngle)
    try assertNext(from: &scanner, is: .oplus)
    XCTAssertNil(scanner.next())
  }

  func testConversionOperator() throws {
    var scanner = Lexer(tokenizing: "as as! as* as+")
    try assertNext(from: &scanner, is: .conversion, withValue: "as")
    try assertNext(from: &scanner, is: .conversion, withValue: "as!")
    try assertNext(from: &scanner, is: .conversion, withValue: "as*")
    try assertNext(from: &scanner, is: .conversion, withValue: "as")
    try assertNext(from: &scanner, is: .operator)
  }

  func testPunctuation() throws {
    var scanner = Lexer(tokenizing: "@,.: :: ; ... (+")
    try assertNext(from: &scanner, is: .at)
    try assertNext(from: &scanner, is: .comma)
    try assertNext(from: &scanner, is: .dot)
    try assertNext(from: &scanner, is: .colon)
    try assertNext(from: &scanner, is: .doubleColon)
    try assertNext(from: &scanner, is: .semicolon)
    try assertNext(from: &scanner, is: .ellipsis)
    try assertNext(from: &scanner, is: .leftParenthesis)
    try assertNext(from: &scanner, is: .operator)
    XCTAssertNil(scanner.next())
  }

}

private func assertNext(
  from scanner: inout Lexer, is expected: Token.Tag, withValue text: String? = nil,
  file: StaticString = #file, line: UInt = #line
) throws {
  let next = try XCTUnwrap(scanner.next())
  XCTAssertEqual(next.tag, expected, file: (file), line: line)
  if let s = text {
    XCTAssertEqual(String(next.text), s, file: (file), line: line)
  }
}
