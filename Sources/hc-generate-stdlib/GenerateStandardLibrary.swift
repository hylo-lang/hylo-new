import ArgumentParser
import Foundation

/// The top-level command of `hc-generate-stdlib`.
@main struct CommandLine: ParsableCommand {
  
  @Option(
    help: ArgumentHelp(
      "The output directory to generate Hylo declarations into. (Default: StandardLibrary/Sources/Core/Generated)"
    ),
    transform: URL.init(fileURLWithPath:))
  private var output: URL = URL(fileURLWithPath: #filePath)
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .appending(path: "StandardLibrary/Sources/Core/Generated")

  /// Executes the CLI command, generating output files within `output`
  public func run() throws {
    let integers = try generateIntegerTypes()
    try integers.write(
      to: output.appending(path: "Integers.hylo"),
      atomically: true, encoding: .utf8)
  }

}
