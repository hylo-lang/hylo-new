import Foundation

extension Process {

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
      '\(executable) \(arguments.joined(separator: " "))' exited with status \(exitCode).

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
  ) async throws -> String {
    let x = try await execute(executable, arguments: arguments)
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
  ///
  /// Task cancellation during execution has no effect.
  public static func execute(
    _ executable: URL, arguments: [String] = [], workingDirectory: URL? = nil
  ) async throws -> ExecutionReport {
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

    // Drain both pipes concurrently while the process runs.
    async let output = readToEnd(standardOutput.fileHandleForReading)
    async let error = readToEnd(standardError.fileHandleForReading)

    // Launch the process and wait for it to exit.
    //
    // Cancellation of the current task is ignored. We always wait for the process to terminate.
    do {
      try await withCheckedThrowingContinuation { (continuation) in
        process.terminationHandler = { (_) in continuation.resume() }
        do {
          try process.run()
        } catch {
          continuation.resume(throwing: error)
        }
      }
    } catch {
      // Close files when `run` fails, then rethrow.
      try? standardOutput.fileHandleForWriting.close()
      try? standardError.fileHandleForWriting.close()
      throw error
    }

    // Read failures are rethrown once the process has exited.
    return .init(
      standardOutput: try await output.get().decodedAsRepairedUTF8(),
      standardError: try await error.get().decodedAsRepairedUTF8(),
      exitCode: process.terminationStatus,
      terminationReason: process.terminationReason)
  }

  /// The result of executing a process.
  public struct ExecutionReport: Sendable {

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

/// Returns the data read from `handle` until end-of-file, or the error that
/// interrupted the read.
private func readToEnd(_ handle: FileHandle) async -> Result<Data, any Error> {
  await withCheckedContinuation { (continuation) in
    Thread {
      // Block the thread until we read the file to end.
      continuation.resume(returning: Result { try handle.readToEnd() ?? Data() })
    }.start()
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
