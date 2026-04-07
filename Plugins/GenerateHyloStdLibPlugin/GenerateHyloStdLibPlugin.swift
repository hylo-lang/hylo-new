import Foundation
import PackagePlugin

/// The SPM plugin generating Hylo integer type declarations into Numbers.hylo.
@main
struct GenerateHyloIntegersPlugin: BuildToolPlugin {

  func createBuildCommands(
    context: PackagePlugin.PluginContext, target: any PackagePlugin.Target
  ) async throws -> [PackagePlugin.Command] {
    let pluginOutputPath = context.pluginWorkDirectoryURL.appending(component: "Generated")
    let stdlibGeneratedPath = context.package.directoryURL
      .appending(components: "StandardLibrary", "Sources", "Core", "Numbers", "Generated")
    
    let integersOutput = pluginOutputPath.appending(component: "Integers.hylo")

    try ensureSymbolicLink(at: pluginOutputPath, pointingTo: stdlibGeneratedPath)

    let c = PackagePlugin.Command.buildCommand(
      displayName: "Generating Hylo integer type declarations into \(integersOutput.lastPathComponent)",
      executable: try context.tool(named: "hc-generate-stdlib").url,
      arguments: ["--output=\(integersOutput.path(percentEncoded: true))"],
      environment: [:],
      inputFiles: [],
      outputFiles: [integersOutput])
    return [c]
  }

  private func ensureSymbolicLink(at link: URL, pointingTo destination: URL) throws {
    let fm = FileManager.default
    let linkPath = link.path(percentEncoded: false)
    let destinationPath = destination.path(percentEncoded: false)

    if fm.fileExists(atPath: linkPath) {
      try fm.removeItem(atPath: linkPath)
    }

    try fm.createSymbolicLink(
      atPath: linkPath,
      withDestinationPath: destinationPath)
  }

}
