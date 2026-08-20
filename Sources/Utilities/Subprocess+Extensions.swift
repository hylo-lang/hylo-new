import Foundation
import Subprocess

extension TerminationStatus {

  /// The exit code or signal number.
  public var exitCode: Int32 {
    #if os(Windows)
    switch self {
    case .exited(let code):
      // Ensure status codes are reported as positive numbers.
      // See: https://github.com/swiftlang/swift-corelibs-foundation/blob/6f4ac1e917b98c7c40a51acb25a47a2aa89b3855/Sources/Foundation/Process.swift#L653 [allow long]
      return Int32(truncatingIfNeeded: code & 0x3FFF_FFFF)
    }
    #else
    switch self {
    case .exited(let code):
      return Int32(truncatingIfNeeded: code)
    case .signaled(let signal):
      return Int32(truncatingIfNeeded: signal)
    }
    #endif
  }

  /// `true` iff the process was killed by an uncaught signal or an unhandled exception.
  ///
  /// On Windows, the process is considered to have failed abnormally if its exit code has the
  /// severity bits of an error, warning or customer NTSTATUS, or if it is `3`, which is the exit
  /// code used by the C runtime's `abort`.
  public var isAbnormalFailure: Bool {
    #if os(Windows)
    // - Heuristic borrowed from: https://github.com/swiftlang/swift-corelibs-foundation/blob/6f4ac1e917b98c7c40a51acb25a47a2aa89b3855/Sources/Foundation/Process.swift#L653 [allow long]
    switch self {
    case .exited(let code):
      switch code & 0xF000_0000 {
      case 0xC000_0000, 0x8000_0000, 0xE000_0000:
        return true
      default:
        return code == 3
      }
    }
    #else
    if case .signaled = self { return true } else { return false }
    #endif
  }

}

extension ExecutionResult {

  /// The exit code of the process.
  ///
  /// If the process was terminated by a signal, this is the signal number.
  public var exitCode: Int32 { terminationStatus.exitCode }

  /// `true` iff the process was killed by an uncaught signal or an unhandled exception.
  public var isAbnormalFailure: Bool { terminationStatus.isAbnormalFailure }

}

extension Executable {

  /// The executable located at `url`.
  public static func path(_ url: URL) -> Self {
    .path(.init(url.path))
  }

}

/// The result of a subprocess execution with captured string outputs.
public typealias ExecutionReport = ExecutionResult<Void, StringOutput<UTF8>, StringOutput<UTF8>>

/// Runs `executable` with `arguments` and `environment` in `workingDirectory` (or the current
/// directory if `nil`), capturing its standard output and standard error as strings.
public func executeSubprocess(
  _ executable: Executable, arguments: [String] = [], workingDirectory: URL? = nil,
  environment: Environment = .inherit
) async throws -> ExecutionReport {
  try await run(
    executable, arguments: .init(arguments), environment: environment,
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
public func subprocessOutput(
  of executable: Executable, arguments: [String] = []
) async throws -> String {
  let r = try await executeSubprocess(executable, arguments: arguments)
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
