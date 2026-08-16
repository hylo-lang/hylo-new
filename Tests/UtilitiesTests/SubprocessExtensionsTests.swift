import Foundation
import Subprocess
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
    XCTAssertEqual(r.terminationReason, .exit)
    XCTAssertEqual(r.standardOutput, "")
    XCTAssertEqual(r.standardError, "")
  }

  func testExitCodeOnSignal() async throws {
    #if !os(Windows)
      // The shell sends itself SIGTERM (15), which it does not catch by default.
      let r = try await execute(shell, arguments: arguments(running: "kill -TERM $$"))
      XCTAssertEqual(r.terminationReason, .uncaughtSignal)
      XCTAssertEqual(r.exitCode, SIGTERM)
    #else
      throw XCTSkip() // Not very easy to produce a signal on Windows.
    #endif
  }

}
