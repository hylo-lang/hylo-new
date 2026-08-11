import Foundation
import PackagePlugin

/// The SPM plugin generating compiler test cases as part of our build process.
@main
struct CompilerTestsPlugin: BuildToolPlugin {

  func createBuildCommands(
    context: PackagePlugin.PluginContext, target: any PackagePlugin.Target
  ) async throws -> [PackagePlugin.Command] {
    let output = context.pluginWorkDirectoryURL
      .appending(component: "CompilerTests+GeneratedTests.swift")

    let snapshot = context.pluginWorkDirectoryURL.appending(component: "test-cases.txt")
    let tests = testCases(in: target.directoryURL)
      .map({ (u) in u.path(percentEncoded: false) })
      .sorted()
      .joined(separator: "\n")

    if (try? String(contentsOf: snapshot, encoding: .utf8)) != tests {
      try tests.write(to: snapshot, atomically: true, encoding: .utf8)
    }

    let c = PackagePlugin.Command.buildCommand(
      displayName: "Generating compiler test cases into \(output)",
      executable: try context.tool(named: "hc-tests").url,
      arguments: ["-o", output.path(percentEncoded: true)],
      environment: [:],
      inputFiles: [snapshot],
      outputFiles: [output])
    return [c]
  }

  /// Returns the URLs of the test case files in the "negative" and "positive" suites of the
  /// target rooted at `root`.
  private func testCases(in root: URL) -> [URL] {
    ["negative", "positive"].flatMap { (suite) -> [URL] in
      let d = root.appending(component: suite, directoryHint: .isDirectory)
      let files = (try? FileManager.default.contentsOfDirectory(
        at: d, includingPropertiesForKeys: nil, options: .skipsHiddenFiles)) ?? []
      return files.filter { (u) in u.pathExtension == "hylo" || u.pathExtension == "package" }
    }
  }

}
