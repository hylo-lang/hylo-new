import ArgumentParser
import Foundation

/// The top-level command of `hc-generate-stdlib`.
@main struct CommandLine: ParsableCommand {

  @Option(
    name: .customLong("output"),
    help: ArgumentHelp("The output file to generate Hylo declarations into."),
    transform: URL.init(fileURLWithPath:))
  private var outputFile: URL

  /// Executes the CLI command, generating output file at `outputFile`.
  public func run() throws {
    let contents = try generateIntegerTypes()
    try contents.write(to: outputFile, atomically: true, encoding: .utf8)
  }

}
