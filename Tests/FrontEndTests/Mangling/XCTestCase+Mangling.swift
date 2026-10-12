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

  /// Returns a type checked program containing the minimal standard library and `source` in a
  /// module named `M0`, along with the identity of that module, failing the current test if that
  /// program contains errors.
  func typeCheckedWithMinimalStandardLibrary(
    _ source: SourceFile, file: StaticString = #filePath, line: UInt = #line
  ) async -> (Program, Module.ID) {
    var p = await Program.withMinimalStandardLibrary()
    let m0 = p.addUserModule(named: "M0", source: source)
    p = await p.typeChecked()
    failIfContainsError(p, file: file, line: line)
    return (p, m0)
  }

  /// Fails the current test if `p` contains errors.
  func failIfContainsError(_ p: Program, file: StaticString = #filePath, line: UInt = #line) {
    if p.containsError {
      for d in p.diagnostics {
        print(d)
      }
      XCTFail("Unexpected error(s) in test program: \(p.diagnostics)", file: file, line: line)
    }
  }

}
