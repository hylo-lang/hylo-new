import XCTest

@testable import FrontEnd

extension XCTestCase {

  /// Asserts that `m`, which is the mangling of the symbol described by `subject`, demangles
  /// without error.
  func assertDemanglingIsOk(
    mangled m: String, of subject: String? = nil,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    let demangled = DemangledSymbol(m).description
    XCTAssertFalse(
      demangled.contains("#!"),
      "demangling of \(subject ?? m) contains errors: \(demangled)\n(mangled: \(m))",
      file: file, line: line)
  }

  /// Fail the tests if `p` contains errors.
  func failIfContainsError(_ p: Program, file: StaticString = #filePath, line: UInt = #line) {
    if p.containsError {
      for d in p.diagnostics {
        print(d)
      }
      XCTFail("Unexpected error(s) in test program: \(p.diagnostics)", file: file, line: line)
    }
  }

}
