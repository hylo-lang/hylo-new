import Foundation
import Subprocess

/// The reason why a subprocess terminated.
public enum TerminationReason: Hashable, Sendable {

  /// The process exited normally, with an exit code.
  case exit

  /// The process was killed by an uncaught signal (or, on Windows, an unhandled exception).
  case uncaughtSignal

}

extension TerminationStatus {

  #if os(Windows)

  /// The exit code corresponding to `self`.
  ///
  /// Windows has no signals; a process killed by an unhandled exception exits with an NTSTATUS
  /// exit code. Like Foundation's `Process`, the exit code is masked with `0x3FFF_FFFF` so that
  /// such statuses are reported as positive numbers.
  public var exitCode: Int32 {
    switch self {
    case .exited(let code):
      return Int32(truncatingIfNeeded: code & 0x3FFF_FFFF)
    }
  }

  /// The termination reason corresponding to `self`.
  ///
  /// The process is considered killed by an "uncaught signal" if its exit code has the severity
  /// bits of an error, warning or customer NTSTATUS, or if it is `3`, which is the exit code used
  /// by the C runtime's `abort`. This is a heuristic mirroring the behavior of Foundation.
  public var terminationReason: TerminationReason {
    switch self {
    case .exited(let code):
      switch code & 0xF000_0000 {
      case 0xC000_0000, 0x8000_0000, 0xE000_0000:
        return .uncaughtSignal
      default:
        return code == 3 ? .uncaughtSignal : .exit
      }
    }
  }

  #else

  /// The exit code corresponding to `self`.
  ///
  /// If the process was terminated by a signal, this is the signal number.
  public var exitCode: Int32 {
    switch self {
    case .exited(let code):
      return Int32(truncatingIfNeeded: code)
    case .signaled(let signal):
      return Int32(truncatingIfNeeded: signal)
    }
  }

  /// The termination reason corresponding to `self`.
  public var terminationReason: TerminationReason {
    switch self {
    case .exited:
      return .exit
    case .signaled:
      return .uncaughtSignal
    }
  }

  #endif

}

extension ExecutionResult {

  /// The exit code of the process.
  ///
  /// If the process was terminated by a signal, this is the signal number.
  public var exitCode: Int32 { terminationStatus.exitCode }

  /// The reason why the process terminated.
  public var terminationReason: TerminationReason { terminationStatus.terminationReason }

}

extension Executable {

  /// The executable located at `url`.
  public static func path(_ url: URL) -> Self {
    .path(.init(url.path))
  }

}

/// The result of a subprocess execution with captured string outputs.
public typealias ExecutionReport = ExecutionResult<Void, StringOutput<UTF8>, StringOutput<UTF8>>

/// Runs `executable` with `arguments` in `workingDirectory` (or the current directory if `nil`),
/// capturing its standard output and standard error as strings.
public func execute(
  _ executable: Executable, arguments: [String] = [], workingDirectory: URL? = nil
) async throws -> ExecutionReport {
  try await run(
    executable, arguments: .init(arguments),
    workingDirectory: workingDirectory.map({ .init($0.path) }),
    output: .string(limit: .max), error: .string(limit: .max))
}

/// The error thrown when a process exits with a non-zero status.
public struct NonzeroExit: Error, CustomStringConvertible {

  /// The exit code of the process.
  public let exitCode: Int32

  /// The data written to the standard output of the process.
  public let standardOutput: String

  /// The data written to the standard error of the process.
  public let standardError: String

  /// The executable ran by the process.
  public let executable: Executable

  /// The arguments passed to the process.
  public let arguments: [String]

  /// A textual description of the failure.
  public var description: String {
    """
    '\(executable) \(arguments.joined(separator: " "))' exited with status \(exitCode).

    Standard Output:
    \(standardOutput)

    Standard Error:
    \(standardError)
    """
  }

}

/// Runs `executable` with `arguments` and returns the data written to the standard output.
///
/// Throws a `NonzeroExit` upon terminating with non-zero exit code.
public func executionOutput(
  of executable: Executable, arguments: [String] = []
) async throws -> String {
  let r = try await execute(executable, arguments: arguments)
  guard r.terminationStatus.isSuccess else {
    throw NonzeroExit(
      exitCode: r.exitCode,
      standardOutput: r.standardOutput,
      standardError: r.standardError,
      executable: executable,
      arguments: arguments)
  }
  return r.standardOutput
}
