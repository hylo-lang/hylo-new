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

    let c = PackagePlugin.Command.buildCommand(
      displayName: "Generating compiler test cases into \(output)",
      executable: try context.tool(named: "hc-tests").url,
      arguments: ["-o", output.path(percentEncoded: true)],
      environment: [:],
      inputFiles: [],
      outputFiles: [output])
    return [c]
  }

}
