import Foundation
import Utilities
import XCTest

typealias Host = Utilities.Host


final class HostTests: XCTestCase {

  func testFindNativeExecutableThrowsForUnknownCommand() throws {
    XCTAssertThrowsError(
      try Host.findNativeExecutable(invokedAs: "randomNotFoundExecutable"), "",
      { (error) in
        if let e = error as? Host.ExecutableNotFound {
          XCTAssertEqual(e.name, "randomNotFoundExecutable")
          XCTAssertEqual(e.description, "Executable not found on PATH: randomNotFoundExecutable")
        } else {
          XCTFail("Expected Host.ExecutableNotFound, got \(error)")
        }
      })
  }

  #if os(Windows)
    func testFindNativeExecutableFindsAndExecutesWhereExe() throws {
      let whereExe = try Host.findNativeExecutable(invokedAs: "where")
      XCTAssertEqual(whereExe.lastPathComponent.lowercased(), "where.exe")

      let output = try Process.executionOutput(whereExe, arguments: ["cmd"])
      XCTAssertTrue(output.lowercased().contains("cmd.exe"))
    }
  #else
    func testFindNativeExecutableFindsAndExecutesBash() throws {
      let bash = try Host.findNativeExecutable(invokedAs: "bash")
      XCTAssertEqual(bash.lastPathComponent, "bash")

      let output = try Process.executionOutput(bash, arguments: ["-lc", "printf '%s' bash-ok"])
      XCTAssertEqual(output, "bash-ok")
    }
  #endif

  func testExecutionOutputThrowsOnNonzeroExit() throws {
    #if os(Windows)
      let executable = try Host.findNativeExecutable(invokedAs: "cmd")
      let arguments = ["/c", "exit", "42"]
    #else
      let executable = try Host.findNativeExecutable(invokedAs: "bash")
      let arguments = ["-lc", "exit 42"]
    #endif

    XCTAssertThrowsError(
      try Process.executionOutput(executable, arguments: arguments), "",
      { (error) in
        if let e = error as? Process.NonzeroExit {
          XCTAssertEqual(e.exitCode, 42)
          XCTAssertEqual(e.executable, executable)
          XCTAssertEqual(e.arguments, arguments)
        } else {
          XCTFail("Expected Process.NonzeroExit, got \(error)")
        }
      })
  }

  func testExecuteReturnsReportOnNonzeroExit() throws {
    #if os(Windows)
      let executable = try Host.findNativeExecutable(invokedAs: "cmd")
      let arguments = ["/c", "exit", "42"]
    #else
      let executable = try Host.findNativeExecutable(invokedAs: "bash")
      let arguments = ["-lc", "exit 42"]
    #endif

    let r = try Process.execute(executable, arguments: arguments)
    XCTAssertEqual(r.exitCode, 42)
    XCTAssertEqual(r.standardOutput, "")
    XCTAssertEqual(r.standardError, "")
  }

}
