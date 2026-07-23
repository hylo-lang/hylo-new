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

    /// Creates an instance with the given process result.
    public init(
      exitCode: Int32, standardOutput: String, standardError: String, executable: URL,
      arguments: [String]
    ) {
      self.exitCode = exitCode
      self.standardOutput = standardOutput
      self.standardError = standardError
      self.executable = executable
      self.arguments = arguments
    }

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
  public static func executionOutput(
    _ executable: URL, arguments: [String] = []
  ) throws -> String {
    let process = Process()
    let standardOutput = Pipe()
    let standardError = Pipe()
    process.executableURL = executable
    process.arguments = arguments
    process.standardOutput = standardOutput
    process.standardError = standardError
    try process.run()
    process.waitUntilExit()

    let output = String(
      decoding: standardOutput.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let error = String(
      decoding: standardError.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)

    if process.terminationStatus != 0 {
      throw NonzeroExit(
        exitCode: process.terminationStatus,
        standardOutput: output,
        standardError: error,
        executable: executable,
        arguments: arguments)
    }

    return output
  }

  /// Runs `executable` with `arguments` and returns its execution report.
  public static func execute(
    _ executable: URL, arguments: [String] = []
  ) throws -> ExecutionReport {
    let process = Process()
    let standardOutput = Pipe()
    let standardError = Pipe()
    process.arguments = arguments
    process.executableURL = executable
    process.standardOutput = standardOutput
    process.standardError = standardError
    try process.run()
    process.waitUntilExit()

    let output = String(
      decoding: standardOutput.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let error = String(
      decoding: standardError.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)

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
