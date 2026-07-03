import FormatFixups
import Foundation

/// A command that formats Swift sources according to the Hylo coding guidelines.
///
/// Formatting is performed in two steps: sources are first rewritten by `swift-format` using the
/// configuration at the root of the repository, and then by the fixups in `FormatFixups`, which
/// implement the conventions that `swift-format` cannot express.
@main struct HyloFormat {

  /// The way in which nonconforming files are handled.
  enum Mode {

    /// Nonconforming files are rewritten in place.
    case format

    /// Nonconforming files are reported and the command exits with a nonzero status.
    case check

  }

  /// An error caused by an invalid invocation or a failure of an underlying tool.
  struct CommandError: Error, CustomStringConvertible {

    /// A message explaining the error to the user.
    let description: String

  }

  /// The paths formatted when none are passed on the command line.
  static let defaultRoots = ["Package.swift", "Plugins", "Sources", "Tests", "Tools"]

  /// Parses the command line and runs the formatter, reporting errors on the standard error.
  static func main() {
    do {
      try run(arguments: Array(CommandLine.arguments.dropFirst()))
    } catch {
      FileHandle.standardError.write(Data("error: \(error)\n".utf8))
      exit(1)
    }
  }

  /// Runs the formatter as described by `arguments`.
  static func run(arguments: [String]) throws {
    var mode: Mode = .format
    var configuration = ".swift-format.json"
    var roots: [String] = []

    var remainder = arguments[...]
    while let a = remainder.popFirst() {
      switch a {
      case "--check":
        mode = .check
      case "--configuration":
        guard let v = remainder.popFirst() else {
          throw CommandError(description: "missing value after '--configuration'")
        }
        configuration = v
      case "--help", "-h":
        print(usage)
        return
      default:
        roots.append(a)
      }
    }

    guard FileManager.default.fileExists(atPath: configuration) else {
      throw CommandError(
        description: """
          cannot find '\(configuration)'; run from the repository root or pass '--configuration'
          """)
    }

    if roots.isEmpty {
      roots = defaultRoots.filter({ (r) in FileManager.default.fileExists(atPath: r) })
    }

    let files = swiftFiles(under: roots)
    if files.isEmpty { throw CommandError(description: "no Swift sources found") }

    let nonconforming = try format(files, configuration: configuration, mode: mode)
    switch mode {
    case .format:
      print("Reformatted \(nonconforming.count) of \(files.count) files.")
    case .check:
      for f in nonconforming { print("\(f.relativePath): needs formatting") }
      if !nonconforming.isEmpty {
        throw CommandError(
          description: "\(nonconforming.count) of \(files.count) files need formatting")
      }
      print("All \(files.count) files are properly formatted.")
    }
  }

  /// A short description of the command line interface.
  static let usage = """
    USAGE: hylo-format [--check] [--configuration <path>] [<path> ...]

    Formats the Swift sources at the given paths (files or directories) according to the Hylo
    coding guidelines. Paths default to '\(defaultRoots.joined(separator: "', '"))'.

    OPTIONS:
      --check                 Report nonconforming files instead of rewriting them; exit with a
                              nonzero status if there are any.
      --configuration <path>  The swift-format configuration to use (default:
                              '.swift-format.json' in the current directory).
    """

  /// Formats the contents of `files` using the swift-format configuration at `configuration`,
  /// rewriting them in place iff `mode` is `.format`, and returns the ones that were not
  /// conforming.
  ///
  /// Formatting is computed on temporary copies so that `files` are never left half-formatted,
  /// even if an underlying tool fails.
  static func format(_ files: [URL], configuration: String, mode: Mode) throws -> [URL] {
    let sources = try files.map({ (f) in try String(contentsOf: f, encoding: .utf8) })

    let staging = FileManager.default.temporaryDirectory
      .appendingPathComponent("hylo-format-\(UUID().uuidString)")
    try FileManager.default.createDirectory(at: staging, withIntermediateDirectories: true)
    defer { try? FileManager.default.removeItem(at: staging) }

    let copies = try sources.enumerated().map { (i, s) in
      let c = staging.appendingPathComponent("\(i).swift")
      try s.write(to: c, atomically: true, encoding: .utf8)
      return c
    }

    try runSwiftFormat(
      ["format", "--in-place", "--parallel", "--configuration", configuration]
        + copies.map(\.path))

    var nonconforming: [URL] = []
    for (i, f) in files.enumerated() {
      let formatted = applyingConventionFixups(
        to: try String(contentsOf: copies[i], encoding: .utf8))
      if formatted == sources[i] { continue }
      nonconforming.append(f)
      if mode == .format {
        try formatted.write(to: f, atomically: true, encoding: .utf8)
        print("Reformatted \(f.relativePath)")
      }
    }
    return nonconforming
  }

  /// Runs `swift-format` with `arguments`, forwarding its standard error.
  static func runSwiftFormat(_ arguments: [String]) throws {
    let p = Process()
    p.executableURL = URL(fileURLWithPath: "/usr/bin/env")
    p.arguments = ["swift-format"] + arguments
    let diagnostics = Pipe()
    p.standardError = diagnostics
    try p.run()
    let forwarded = diagnostics.fileHandleForReading.readDataToEndOfFile()
    p.waitUntilExit()
    FileHandle.standardError.write(forwarded)
    if p.terminationStatus != 0 {
      throw CommandError(
        description: "swift-format exited with status \(p.terminationStatus)")
    }
  }

  /// Returns the Swift source files at or under `roots`, skipping hidden files and directories.
  ///
  /// The result is sorted by path so that output order is deterministic.
  static func swiftFiles(under roots: [String]) -> [URL] {
    var files: [URL] = []
    for r in roots {
      let root = URL(fileURLWithPath: r, relativeTo: URL(fileURLWithPath: "."))
      var isDirectory: ObjCBool = false
      guard FileManager.default.fileExists(atPath: r, isDirectory: &isDirectory) else { continue }

      if !isDirectory.boolValue {
        if r.hasSuffix(".swift") { files.append(root) }
        continue
      }

      let children = FileManager.default.enumerator(
        at: root, includingPropertiesForKeys: nil, options: [.skipsHiddenFiles])
      while let c = children?.nextObject() as? URL {
        if c.pathExtension == "swift" { files.append(c) }
      }
    }
    return files.sorted(by: { (l, r) in l.path < r.path })
  }

}
