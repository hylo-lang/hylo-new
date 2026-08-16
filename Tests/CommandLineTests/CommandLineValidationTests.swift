import XCTest
@testable import hc

final class CommandLineValidationTests: XCTestCase {

  func testModuleEmission() {
    // '--emit-module-to' requires an output type that produces transformed IR.
    for emit in ["ast", "typed-ast", "raw-ir"] {
      assertRejects(
        ["--emit", emit, "--emit-module-to", "M.hylomodule"],
        withMessageContaining: "'--emit-module-to' cannot be used with '--emit \(emit)'")
    }
    for emit in ["ir", "llvm", "asm", "object", "binary"] {
      assertAccepts(["--emit", emit, "--emit-module-to", "M.hylomodule"])
    }
  }

  func testInterfaceHashEmission() {
    // '--emit-module-interface-hash-to' requires an output type that produces transformed IR.
    for emit in ["ast", "typed-ast", "raw-ir"] {
      assertRejects(
        ["--emit", emit, "--emit-module-interface-hash-to", "M.hash"],
        withMessageContaining:
          "'--emit-module-interface-hash-to' cannot be used with '--emit \(emit)'")
    }
    assertAccepts(["--emit", "object", "--emit-module-interface-hash-to", "M.hash"])
  }

  func testImportAndLinking() {
    // '--import' is not yet supported when the compiler links the output.
    assertRejects(
      ["--emit", "binary", "--import", "Foo"],
      withMessageContaining: "'--import' is not yet supported with '--emit binary'")

    // `binary` is the default output type.
    assertRejects(
      ["--import", "Foo"],
      withMessageContaining: "'--import' is not yet supported with '--emit binary'")

    assertAccepts(["--emit", "object", "--import", "Foo"])
  }

  func testSelfImport() {
    assertRejects(
      ["--emit", "object", "--module-name", "A", "--import", "A"],
      withMessageContaining: "module 'A' cannot import itself")

    // The default module name is 'Main' unless a single source file is given.
    assertRejects(
      ["--emit", "object", "--import", "Main"],
      withMessageContaining: "module 'Main' cannot import itself")
    assertRejects(
      ["--emit", "object", "--import", "Main", "src/"],
      withMessageContaining: "module 'Main' cannot import itself")
    assertRejects(
      ["--emit", "object", "--import", "Main", "a.hylo", "b.hylo"],
      withMessageContaining: "module 'Main' cannot import itself")

    // The default module name is the base name of a single source file input.
    assertRejects(
      ["--emit", "object", "--import", "foo", "path/to/foo.hylo"],
      withMessageContaining: "module 'foo' cannot import itself")
    assertAccepts(["--emit", "object", "--import", "Main", "path/to/foo.hylo"])
    assertAccepts(["--emit", "object", "--import", "foo", "src/"])

    assertAccepts(["--emit", "object", "--module-name", "A", "--import", "B"])
  }

  func testObjectToStandardOutput() {
    // Object files cannot be written to the standard output.
    assertRejects(
      ["--emit", "object", "-o", "-"],
      withMessageContaining: "object cannot be written to the standard output")

    assertAccepts(["--emit", "object", "-o", "out.o"])
    assertAccepts(["--emit", "asm", "-o", "-"])
  }

  func testCachingOptions() {
    // '--no-caching' and '--module-cache' are mutually exclusive.
    assertRejects(
      ["--no-caching", "--module-cache", "cache/"],
      withMessageContaining: "'--no-caching' and '--module-cache' are mutually exclusive")

    assertAccepts(["--no-caching"])
    assertAccepts(["--module-cache", "cache/"])
  }

  /// Asserts that parsing `arguments` fails with a message containing `expected`.
  private func assertRejects(
    _ arguments: [String], withMessageContaining expected: String,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    XCTAssertThrowsError(
      try hc.CommandLine.parse(arguments), file: file, line: line
    ) { (e) in
      let m = hc.CommandLine.message(for: e)
      XCTAssert(m.contains(expected), "unexpected message: \(m)", file: file, line: line)
    }
  }

  /// Asserts that parsing `arguments` succeeds.
  private func assertAccepts(
    _ arguments: [String], file: StaticString = #filePath, line: UInt = #line
  ) {
    XCTAssertNoThrow(try hc.CommandLine.parse(arguments), file: file, line: line)
  }

}
