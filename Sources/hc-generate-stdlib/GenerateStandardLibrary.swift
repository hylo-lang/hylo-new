import ArgumentParser
import Foundation
import Utilities

/// The top-level command of `hc-generate-stdlib`.
@main internal struct CommandLine: ParsableCommand {

  @Option(
    name: .customLong("output"),
    help: ArgumentHelp("The output file to generate Hylo declarations into."),
    transform: URL.init(fileURLWithPath:))
  private var outputFile: URL

  /// Executes the CLI command, writing the generated declarations to `outputFile`.
  internal func run() throws {
    let s = generateIntegerTypes()
    // On Windows, `swift package clean` would fail if it contained a read-only file.
    #if os(Windows)
      try s.write(to: outputFile, atomically: false, encoding: .utf8)
    #else
      try s.forceWriteReadonly(to: outputFile, encoding: .utf8)
    #endif
  }

}
