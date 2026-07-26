import Foundation
import PackagePlugin

/// The SPM plugin generating repetitive parts of the standard library using `hc-generate-stdlib`.
@main
struct GenerateStandardLibraryPlugin: BuildToolPlugin {

  func createBuildCommands(
    context: PackagePlugin.PluginContext, target: any PackagePlugin.Target
  ) async throws -> [PackagePlugin.Command] {
    let output = context.pluginWorkDirectoryURL.appending(component: "Generated.hylo")

    let c = PackagePlugin.Command.buildCommand(
      displayName: "Generating Hylo standard library declarations into \(output)",
      executable: try context.tool(named: "hc-generate-stdlib").url,
      arguments: ["--output=\(output.path(percentEncoded: false))"],
      environment: [:],
      inputFiles: [],
      outputFiles: [output])
    return [c]
  }

}
