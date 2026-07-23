import Demangler
import XCTest

final class TextDemanglerTests: XCTestCase {

  let mangled = "$hR1F06initlT01tR516selfsTR1tR5"
  let demangled = "Hylo.Bool.fun init: [Void](self: Hylo.Bool) let -> Void"

  func testRewriteDemanglesSymbolsInText() {
    let input = "undefined reference to '\(mangled)' and \(mangled)"

    XCTAssertEqual(
      TextDemangler.rewrite(input),
      "undefined reference to '\(demangled)' and \(demangled)")
  }

  func testRewritePreservesTextWithoutMangledSymbols() {
    let input = "clang: error: linker command failed with exit code 1"
    XCTAssertEqual(TextDemangler.rewrite(input), input)
  }

  func testMalformedMangledSymbolIsPreservedAndNotListed() {
    let input = "undefined reference to '$hello'"

    XCTAssertEqual(TextDemangler.rewrite(input), input)
    XCTAssertTrue(TextDemangler.symbols(in: input).isEmpty)
  }

  func testSymbolsListsEachOccurrence() {
    let symbols = TextDemangler.symbols(in: "\(mangled), \(mangled)")

    XCTAssertEqual(symbols.count, 2)
    XCTAssertEqual(symbols.map({ String($0.mangled) }), [mangled, mangled])
    XCTAssertEqual(symbols.map(\.demangled), [demangled, demangled])
  }

}
