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

    // Read pipes on background threads to prevent deadlock if output
    // exceeds pipe buffer size.  The child process will block if pipe
    // buffers fill up, so we must drain them continuously.
    let stdoutData = readPipeInBackground(standardOutput)
    let stderrData = readPipeInBackground(standardError)

    process.waitUntilExit()

    // Retrieve the data (blocks until background reads complete)
    let output = stdoutData().decodedAsRepairedUTF8()
    let error = stderrData().decodedAsRepairedUTF8()

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

/// Starts reading all data from `pipe` using event-driven I/O.
///
/// Returns a closure that blocks until reading completes and returns the data.
/// This prevents pipe buffer deadlocks by draining pipes while the process runs.
/// Uses non-blocking I/O with readability handlers for efficiency.
private func readPipeInBackground(_ pipe: Pipe) -> () -> Data {
  // Box to safely share mutable state across concurrency boundary
  final class ReadCompletion: Operation, @unchecked Sendable {
    var data = Data()
    override init() {
      super.init()
      self.qualityOfService = .userInteractive
      self.queuePriority = .veryHigh
    }
  }

  let completion = ReadCompletion()
  pipe.fileHandleForReading.readabilityHandler = { handle in
    let chunk = handle.availableData
    if chunk.isEmpty {  // EOF on the pipe
      pipe.fileHandleForReading.closeFile()
      pipe.fileHandleForReading.readabilityHandler = nil
      completion.start()
    } else {
      completion.data.append(chunk)
    }
  }

  return {
    completion.waitUntilFinished()
    return completion.data
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
