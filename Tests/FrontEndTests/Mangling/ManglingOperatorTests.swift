import FrontEnd
import XCTest

@testable import FrontEnd

/// A collection of tests for `ManglingOperator`.
final class ManglingOperatorTests: XCTestCase {

  /// Tests that the `ManglingOperator` raw values follow the convention of being a string matching
  /// the regex "[a-z]*[A-Z]".
  func testLowerCaseUpperCaseConversion() {
    for op in ManglingOperator.allCases {
      let raw = op.rawValue
      XCTAssertFalse(raw.isEmpty, "raw value of \(op) is empty")
      let last = raw.last!
      XCTAssert(last.isUppercase, "raw value of \(op) does not end with an uppercase letter")
      let prefix = raw.dropLast()
      XCTAssert(prefix.allSatisfy { $0.isLowercase }, "raw value of \(op) has non-lowercase prefix")
    }
  }

  /// Tests that we can write all the mangling operators in a string and parse them back.
  func testRoundTrip() {
    // Write all operators into a single string.
    var mangled = ""
    for op in ManglingOperator.allCases {
      op.write(to: &mangled)
    }

    // Parse them back and verify we get the same operators in the same order.
    var remaining = mangled[...]
    for op in ManglingOperator.allCases {
      let parsed = ManglingOperator(prefixing: remaining)
      XCTAssertEqual(parsed, op, "expected \(op) but got \(String(describing: parsed))")
      remaining = remaining.dropFirst(op.rawValue.count)
    }
    XCTAssert(remaining.isEmpty, "unexpected trailing characters: \(remaining)")
  }

  /// Tests that each operator is classified as an entity or type operator, except for the
  /// witness-table operator which is intentionally treated as a special case.
  func testOperatorKinds() {
    let specialOperators: [ManglingOperator] = [.witnessTable]
    for op in ManglingOperator.allCases {
      XCTAssert(
        op.isEntityOperator || op.isTypeOperator || specialOperators.contains(op),
        "operator \(op) is neither entity nor type")
    }
  }

}
