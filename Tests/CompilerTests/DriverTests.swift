@testable import Driver
import Foundation
import SwiftyLLVM
import XCTest
import FrontEnd

final class DriverTests: XCTestCase {

  func testHostDriverCreation() throws {
    let driver = try Driver(targetSpecification: .host())

    // Should be generic
    XCTAssertEqual("", driver.target.cpu)
    XCTAssertEqual("", driver.target.features)
  }

  func testNativeDriverCreation() throws {
    let driver = try Driver(targetSpecification: .native())
    XCTAssertFalse(driver.target.cpu.isEmpty)
  }

  func testCreateDriverWithOptions() throws {
    let driver = try Driver(
      targetSpecification: .host(),
      optimization: .aggressive,
      relocation: .pic,
      codeModel: .small)
    XCTAssertEqual(driver.optimization, .aggressive)
    XCTAssertEqual(driver.relocation, .pic)
    XCTAssertEqual(driver.codeModel, .small)
  }

  func testModuleCacheDisabled() throws {
    let d = try Driver(moduleCachePath: nil, targetSpecification: .native())
    XCTAssertNil(d.archive(of: "test"))
  }

  func testModuleCacheNotFound() throws {
    let d = try Driver(
      moduleCachePath: FileManager.default.temporaryDirectory, 
      targetSpecification: .native())
    XCTAssertNil(d.archive(of: "test"))
  }

  func testLinkerErrorDemanglesHyloSymbols() {
    let mangled = "$hR1F06initlT01tR516selfsTR1tR5"
    let error = Process.NonzeroExit(
      exitCode: 1,
      standardOutput: "stdout: undefined reference to '\(mangled)'",
      standardError: "stderr: undefined reference to '\(mangled)'",
      executable: URL(fileURLWithPath: "/usr/bin/clang"),
      arguments: ["-o", "Test"])

    let demangled = error.demanglingHyloSymbols()

    XCTAssertEqual(
      demangled.standardOutput,
      "stdout: undefined reference to 'Hylo.Bool.fun init: [Void](self: Hylo.Bool) let -> Void'")
    XCTAssertEqual(
      demangled.standardError,
      "stderr: undefined reference to 'Hylo.Bool.fun init: [Void](self: Hylo.Bool) let -> Void'")
    XCTAssertEqual(demangled.exitCode, error.exitCode)
    XCTAssertEqual(demangled.executable, error.executable)
    XCTAssertEqual(demangled.arguments, error.arguments)
  }

  func testInvalidArchive() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (cacheRoot) in 
      try await FileManager.default.withUniqueTemporaryDirectory { (sourceRoot) in
        var d = try Driver(
          moduleCachePath: cacheRoot, 
          targetSpecification: .native())
        
        let cachePath = cacheRoot.appendingPathComponent("Main.hylomodule")
        // Write an invalid archive
        try "invalid".write(to: cachePath, atomically: true, encoding: .utf8)

        XCTAssertNotNil(d.archive(of: "Main"))


        // Now try to load it - this should fail
        do {
          try await d.load("Main", withSourcesAt: sourceRoot)
          XCTFail("Expected load to fail")
        } catch let error as Driver.Error {
          XCTAssertEqual(error.message, """
            Failed to parse module archive of 'Main' at '\(cacheRoot)'.

            Maybe the archive was compiled with a different version of the compiler. \
            Try erasing the module cache.
            """)

          XCTAssertEqual("\(error)", error.message)
        }
      }
    }
  }

}

final class CompilationErrorTests: XCTestCase {

  func testStringRepresentation() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(.error, "bang", at: s)
    let c = CompilationError(diagnostics: DiagnosticSet(CollectionOfOne(e)))

    XCTAssertEqual(
      "\(c)",
      """

      virtual:///1ssiyy33rbj6z:1.1-3: error: bang
      Hello.
      ~~

      """)

  }

}
