import Foundation
import Utilities
import XCTest

typealias Host = Utilities.Host


final class HostTests: XCTestCase {

  func testFindBinaryExecutableThrowsForUnknownCommand() throws {
    XCTAssertThrowsError(
      try Host.findBinaryExecutable(invokedAs: "randomNotFoundExecutable"), "",
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
    func testFindBinaryExecutableFindsAndExecutesWhereExe() async throws {
      let whereExe = try Host.findBinaryExecutable(invokedAs: "where")
      XCTAssertEqual(whereExe.lastPathComponent.lowercased(), "where.exe")

      let output = try await withTimeout {
        try await Process.executionOutput(whereExe, arguments: ["cmd"])
      }
      XCTAssertTrue(output.lowercased().contains("cmd.exe"))
    }
  #else
    func testFindBinaryExecutableFindsAndExecutesBash() async throws {
      let bash = try Host.findBinaryExecutable(invokedAs: "bash")
      XCTAssertEqual(bash.lastPathComponent, "bash")

      let output = try await withTimeout {
        try await Process.executionOutput(bash, arguments: ["-lc", "printf '%s' bash-ok"])
      }
      XCTAssertEqual(output, "bash-ok")
    }
  #endif

  func testExecutionOutputThrowsOnNonzeroExit() async throws {
    #if os(Windows)
      let executable = try Host.findBinaryExecutable(invokedAs: "cmd")
      let arguments = ["/c", "exit", "42"]
    #else
      let executable = try Host.findBinaryExecutable(invokedAs: "bash")
      let arguments = ["-lc", "exit 42"]
    #endif

    do {
      _ = try await Process.executionOutput(executable, arguments: arguments)
      XCTFail("Expected Process.NonzeroExit to be thrown")
    } catch let e as Process.NonzeroExit {
      XCTAssertEqual(e.exitCode, 42)
      XCTAssertEqual(e.executable, executable)
      XCTAssertEqual(e.arguments, arguments)

      XCTAssert(e.description.contains("exited with status 42"))
    } catch {
      XCTFail("Expected Process.NonzeroExit, got \(error)")
    }
  }

  func testExecuteReturnsReportOnNonzeroExit() async throws {
    #if os(Windows)
      let executable = try Host.findBinaryExecutable(invokedAs: "cmd")
      let arguments = ["/c", "exit", "42"]
    #else
      let executable = try Host.findBinaryExecutable(invokedAs: "bash")
      let arguments = ["-lc", "exit 42"]
    #endif

    let r = try await withTimeout { try await Process.execute(executable, arguments: arguments) }
    XCTAssertEqual(r.exitCode, 42)
    XCTAssertEqual(r.standardOutput, "")
    XCTAssertEqual(r.standardError, "")
  }

}
