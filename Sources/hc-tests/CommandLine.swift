import ArgumentParser
import Foundation

/// The top-level command of `hc-tests`.
@main struct CommandLine: AsyncParsableCommand {

  /// Configuration for this command.
  public static let configuration = CommandConfiguration(commandName: "hc-tests")

  /// The path of the file to which test cases are written.
  @Option(
    name: [.customShort("o")],
    help: ArgumentHelp("Write output to <file>.", valueName: "output-swift-file"),
    transform: URL.init(fileURLWithPath:))
  private var output: URL?

  /// Whether the command should only list test cases.
  @Flag(
    name: [.customShort("l"), .customLong("list")],
    help: ArgumentHelp("Only list test cases without generating them."))
  private var shouldOnlyList: Bool = false

  /// Whether the command should remove observed files.
  @Flag(
    name: [.customShort("c"), .customLong("clean")],
    help: ArgumentHelp("Remove '*.observed' files."))
  private var shouldCleanObservations: Bool = false

  /// The root path of the compiler test target.
  @Argument(transform: URL.init(fileURLWithPath:))
  private var root: URL =
    URL(fileURLWithPath: #filePath)
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .appending(components: "Tests", "CompilerTests")

  /// The root of the directory containing negative tests.
  private var negative: URL {
    root.appending(component: "negative", directoryHint: .isDirectory)
  }

  /// The root of the directory containing positive tests.
  private var positive: URL {
    root.appending(component: "positive", directoryHint: .isDirectory)
  }

  /// Returns the URLs in `suite` having a ".hylo" or ".package" extension.
  private func testCases(_ suite: URL) throws -> [URL] {
    let urls = try FileManager.default.contentsOfDirectory(
      at: suite,
      includingPropertiesForKeys: nil, options: .skipsHiddenFiles)
    return urls.filter { (u) in u.pathExtension == "hylo" || u.pathExtension == "package" }
  }

  private func testCaseIdentifier(_ testCase: URL) -> String {
    testCase.deletingPathExtension().lastPathComponent.replacingOccurrences(of: "-", with: "_")
  }

  /// Creates a new instance with default options.
  public init() {}

  /// Executes the command.
  public func run() async throws {
    if shouldCleanObservations {
      try cleanObservations()
    }

    if shouldOnlyList {
      try dumpTestCaseNames()
    } else {
      try generateSwiftSourceFile()
    }
  }

  /// Removes all '.observed' files under the root path.
  private func cleanObservations() throws {
    let items = FileManager.default.enumerator(
      at: root,
      includingPropertiesForKeys: [.isRegularFileKey],
      options: [.skipsHiddenFiles, .skipsPackageDescendants])!
    for case let u as URL in items where u.pathExtension == "observed" {
      try FileManager.default.removeItem(at: u)
    }
  }

  /// Dumps a list of all test cases to the standard output.
  private func dumpTestCaseNames() throws {
    var result = ""
    for u in try testCases(negative) { print(u.path(), to: &result) }
    for u in try testCases(positive) { print(u.path(), to: &result) }
    if result.isEmpty {
      throw CommandError.noTestFound
    }
    print(result, terminator: "")
  }

  /// Generates a Swift source defining all test cases.
  private func generateSwiftSourceFile() throws {
    var result = "extension CompilerTests {\n"

    for u in try testCases(negative) {
      let i = testCaseIdentifier(u)
      result += """

          func test_negative_\(i)() async throws {
            try await negative(.init("\(u.absoluteURL.path())"))
          }

        """
    }

    for u in try testCases(positive) {
      let i = testCaseIdentifier(u)
      result += """

          func test_positive_\(i)() async throws {
            try await positive(.init("\(u.absoluteURL.path())"))
          }

        """
    }

    result.append("\n}")
    try result.write(
      to: output ?? root.appending(component: "CompilerTests+GeneratedTests.swift"),
      atomically: true, encoding: .utf8)
  }

}

/// An error that occurred during the execution of `CommandLine`.
public enum CommandError: Error, CustomStringConvertible {

  /// Not test case was found.
  case noTestFound

  /// Returns a textual description of `self`.
  public var description: String {
    switch self {
    case .noTestFound:
      return "No tests were found."
    }
  }

}
