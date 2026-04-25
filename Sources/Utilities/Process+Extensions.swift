import Foundation

extension Process {

  /// The error thrown when a process exits with a non-zero status.
  public struct NonzeroExit: Error {

    /// The exit code of the terminated process.
    public let exitCode: Int32

    /// The collected standard output of the terminated process.
    public let standardOutput: String

    /// The collected standard error of the terminated process.
    public let standardError: String

    /// The executable used to run the terminated process.
    public let executable: URL

    /// The arguments passed to the executable.
    public let arguments: [String]

  }

  /// Runs `executable` with `arguments` and returns its standard output.
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

    let output = String(decoding: standardOutput.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let error = String(decoding: standardError.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)

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
}
