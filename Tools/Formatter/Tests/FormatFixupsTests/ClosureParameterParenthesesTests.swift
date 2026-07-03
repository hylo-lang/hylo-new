import FormatFixups
import XCTest

final class ClosureParameterParenthesesTests: XCTestCase {

  func testParenthesizesSingleParameter() {
    XCTAssertEqual(
      applyingConventionFixups(to: "let f = xs.map({ e in e + 1 })\n"),
      "let f = xs.map({ (e) in e + 1 })\n")
  }

  func testParenthesizesTrailingClosureParameters() {
    XCTAssertEqual(
      applyingConventionFixups(to: "let f = xs.reduce(0) { a, b in a + b }\n"),
      "let f = xs.reduce(0) { (a, b) in a + b }\n")
  }

  func testLeavesAnonymousParameterAlone() {
    let s = "let f = xs.map({ _ in 0 })\n"
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testParenthesizesMixedAnonymousAndNamedParameters() {
    XCTAssertEqual(
      applyingConventionFixups(to: "let f = zip(xs, ys).map({ _, b in b })\n"),
      "let f = zip(xs, ys).map({ (_, b) in b })\n")
  }

  func testLeavesParenthesizedParametersAlone() {
    let s = "let f = xs.map({ (e) in e + 1 })\n"
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testLeavesShorthandArgumentsAlone() {
    let s = "let f = xs.map({ $0 + 1 })\n"
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testPreservesCaptureListAndReturnType() {
    XCTAssertEqual(
      applyingConventionFixups(to: "let f = { [x] e -> Int in e + x }\n"),
      "let f = { [x] (e) -> Int in e + x }\n")
  }

  func testIsIdempotent() {
    let once = applyingConventionFixups(to: "let f = xs.filter { e in e > 0 }\n")
    XCTAssertEqual(applyingConventionFixups(to: once), once)
  }

}
