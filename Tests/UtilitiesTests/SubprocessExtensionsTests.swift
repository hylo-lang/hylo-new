import Foundation
import Subprocess
import HostUtilities
import Utilities
import XCTest

final class SubprocessExtensionsTests: XCTestCase {

  #if os(Windows)
    /// The executable used to run shell commands in tests.
    private let shell: Executable = .name("cmd")

    /// Returns the arguments running `command` with `shell`.
    private func arguments(running command: String) -> [String] { ["/c", command] }
  #else
    /// The executable used to run shell commands in tests.
    private let shell: Executable = .name("bash")

    /// Returns the arguments to run `command` with `shell`.
    private func arguments(running command: String) -> [String] { ["-lc", command] }
  #endif

  func testExecutionOutputThrowsForUnknownExecutable() async throws {
    do {
      _ = try await subprocessOutput(of: .name("randomNotFoundExecutable"))
      XCTFail("Expected an error")
    } catch let e as SubprocessError {
      XCTAssertEqual(e.code, .executableNotFound)
    } catch {
      XCTFail("Expected SubprocessError, got \(error)")
    }
  }

  func testExecutionOutputReturnsStandardOutput() async throws {
    let output = try await subprocessOutput(of: shell, arguments: arguments(running: "echo ok"))
    XCTAssertEqual(output.trimmingCharacters(in: .whitespacesAndNewlines), "ok")
  }

  func testExecutionOutputThrowsOnNonzeroExit() async throws {
    let a = arguments(running: "exit 42")
    do {
      _ = try await subprocessOutput(of: shell, arguments: a)
      XCTFail("Expected NonzeroExit")
    } catch let e as NonzeroExit {
      XCTAssertEqual(e.exitCode, 42)
      XCTAssertEqual(e.executable, shell)
      XCTAssertEqual(e.arguments, a)
      XCTAssert(e.description.contains("exited with status 42"))
    } catch {
      XCTFail("Expected NonzeroExit, got \(error)")
    }
  }

  func testRunReturnsResultOnNonzeroExit() async throws {
    let r = try await executeSubprocess(shell, arguments: arguments(running: "exit 42"))
    XCTAssertEqual(r.exitCode, 42)
    XCTAssertFalse(r.isAbnormalFailure)
    XCTAssertEqual(r.standardOutput, "")
    XCTAssertEqual(r.standardError, "")
  }

  func testExitCodeOnSignal() async throws {
    #if !os(Windows)
      let r = try await executeSubprocess(shell, arguments: arguments(running: "kill -TERM $$"))
      XCTAssertTrue(r.isAbnormalFailure)
      XCTAssertEqual(r.exitCode, SIGTERM)
    #else
      // Windows has no signals; exit code 3 is what the C runtime's `abort` produces.
      let r = try await executeSubprocess(shell, arguments: arguments(running: "exit 3"))
      XCTAssertEqual(r.exitCode, 3)
      XCTAssertTrue(r.isAbnormalFailure)
    #endif
  }

}
