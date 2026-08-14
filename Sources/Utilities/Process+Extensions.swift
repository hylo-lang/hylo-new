import Dispatch
import Foundation

/// A file handle being read to the end of its contents on a dedicated thread.
private struct AsynchronousDrain: ~Copyable {

  /// The state shared with the reading thread.
  ///
  /// - Thread safety: `data` is written only by the reading thread, before it signals `finished`,
  ///   and read only after `finished` was awaited.
  private final class State: @unchecked Sendable {

    /// The data read from the handle, meaningful only after `finished` was signaled.
    var data = Data()

    /// Signaled once `data` holds the complete contents of the handle.
    let finished = DispatchSemaphore(value: 0)

  }

  /// The state shared with the reading thread.
  private let state = State()

  /// Starts reading the contents of `handle` on a new thread, signaling `s.finished` when done.
  init(_ handle: FileHandle) {
    let s = state
    Thread {
      s.data = handle.readDataToEndOfFile()
      s.finished.signal()
    }.start()
  }

  /// Returns the complete contents of the handle, blocking until it has been fully read.
  consuming func contents() -> Data {
    state.finished.wait()
    return state.data
  }

}

extension Process {

  /// Returns the contents of `a` and `b`, read until their end.
  ///
  /// The two streams are drained concurrently to avoid deadlocks.
  private static func drainedOutputs(_ a: Pipe, _ b: Pipe) -> (a: String, b: String) {
    let bContents = AsynchronousDrain(b.fileHandleForReading)
    let aContents = a.fileHandleForReading.readDataToEndOfFile()

    return (
      aContents.decodedAsRepairedUTF8(),
      bContents.contents().decodedAsRepairedUTF8())
  }

  /// The error thrown when a process exits with a non-zero status.
  public struct NonzeroExit: Error, CustomStringConvertible {

    /// The exit code of the process.
    public let exitCode: Int32

    /// The data written to the standard output of the process.
    public let standardOutput: String

    /// The data written to the standard error of the process.
    public let standardError: String

    /// The path to the executable ran by the process.
    public let executable: URL

    /// The arguments passed to the process.
    public let arguments: [String]

    /// A textual description of the failure.
    public var description: String {
      """
      '\(executable.path) \(arguments.joined(separator: " "))' exited with status \(exitCode).

      Standard Output:
      \(standardOutput)

      Standard Error:
      \(standardError)
      """
    }

  }

  /// Runs `executable` with `arguments` and returns the data written
  /// to the standard output.
  ///
  /// Throws a `NonzeroExit` upon terminating with non-zero exit code.
  public static func executionOutput(
    _ executable: URL, arguments: [String] = []
  ) throws -> String {
    let x = try execute(executable, arguments: arguments)
    if x.exitCode != 0 {
      throw NonzeroExit(
        exitCode: x.exitCode,
        standardOutput: x.standardOutput,
        standardError: x.standardError,
        executable: executable,
        arguments: arguments)
    }
    return x.standardOutput
  }

  /// Runs `executable` with `arguments`, setting the working
  /// directory if provided, and returns its execution report.
  public static func execute(
    _ executable: URL, arguments: [String] = [], workingDirectory: URL? = nil
  ) throws -> ExecutionReport {
    let process = Process()
    let standardOutput = Pipe()
    let standardError = Pipe()
    process.arguments = arguments
    process.executableURL = executable
    process.standardOutput = standardOutput
    process.standardError = standardError
    if let d = workingDirectory {
      process.currentDirectoryURL = d
    }
    try process.run()

    let (output, error) = drainedOutputs(standardOutput, standardError)

    process.waitUntilExit()

    return .init(
      standardOutput: output,
      standardError: error,
      exitCode: process.terminationStatus,
      terminationReason: process.terminationReason)
  }

  /// The result of executing a process.
  public struct ExecutionReport {

    /// The data written to the standard output of the process.
    public let standardOutput: String

    /// The data written to the standard error of the process.
    public let standardError: String

    /// The exit code of the process.
    public let exitCode: Int32

    /// The reason why the process terminated.
    public let terminationReason: Process.TerminationReason

    /// Creates an instance from its parts.
    public init(
      standardOutput: String, standardError: String, exitCode: Int32,
      terminationReason: Process.TerminationReason
    ) {
      self.standardOutput = standardOutput
      self.standardError = standardError
      self.exitCode = exitCode
      self.terminationReason = terminationReason
    }

  }
}

extension Data {

  /// Decodes `self` as UTF-8, repairing any invalid code units.
  public func decodedAsRepairedUTF8() -> String {
    var repaired = Data()

    _ = transcode(
      self.makeIterator(), from: UTF8.self, to: UTF8.self,
      stoppingOnError: false, into: { repaired.append($0) })

    return String(data: repaired, encoding: .utf8)!
  }

}
