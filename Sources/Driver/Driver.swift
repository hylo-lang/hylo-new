import Archivist
import Foundation
import FrontEnd
import LLVMEmitter
import StandardLibrary
import SwiftyLLVM

public typealias LLVMModule = SwiftyLLVM.Module
public typealias Module = FrontEnd.Module // Shadowing the name ambiguity

import Utilities

/// A helper to drive the compilation of Hylo source files.
public struct Driver {

  /// A selection of a backend target property.
  public enum TargetSelection: Equatable, Sendable {

    /// Uses the host machine's value for the selected property.
    case host

    /// Using the given value for the selected property.
    case specified(String)

    /// Returns the specified value from the enum or the given host value.
    public func resolvedWith(hostValue: String) -> String {
      switch self {
      case .host:
        return hostValue
      case .specified(let s):
        return s
      }
    }

  }

  /// Configuration for LLVM target selection.
  public struct TargetConfiguration {

    /// The LLVM target triple selection.
    public var targetTriple: TargetSelection

    /// The LLVM target CPU selection.
    public var cpu: TargetSelection

    /// The LLVM target CPU features selection.
    public var features: TargetSelection

    /// Creates an instance with the given properties.
    public init(
      targetTriple: TargetSelection = .host,
      cpu: TargetSelection = .host,
      features: TargetSelection = .host
    ) {
      self.targetTriple = targetTriple
      self.cpu = cpu
      self.features = features
    }

  }

  /// The path containing cached module data.
  public let moduleCachePath: URL?

  /// The target configuration used by the LLVM backend.
  public var targetConfiguration: TargetConfiguration

  /// The list of directories in which to search for libraries to link.
  public var librarySearchPaths: [URL]

  /// The names of the libraries to link.
  public var libraries: [String]

  /// `true` if the standard library and its shim should be excluded from compilation and linking.
  public var isFreestanding: Bool = false

  /// The standard library to use during compilation.
  public var standardLibrary: StandardLibraryDefinition

  /// The program being compiled by the driver.
  public var program: Program

  /// The corresponding LLVM module for each Hylo module.
  ///
  /// It's set after LLVM lowering.
  private var llvmModules: [Module.ID: LLVMModuleBox] = [:]

  private var executableOutputs: [Module.ID: URL] = [:]

  /// Creates an instance with the given properties.
  public init(
    moduleCachePath: URL? = nil, targetConfiguration: TargetConfiguration = .init(),
    librarySearchPaths: [URL] = [], libraries: [String] = [],
    standardLibrary: StandardLibraryDefinition = .full()
  ) {
    self.moduleCachePath = moduleCachePath
    self.targetConfiguration = targetConfiguration
    self.librarySearchPaths = librarySearchPaths
    self.libraries = libraries
    self.standardLibrary = standardLibrary

    self.program = .init()
  }

  /// `true` iff the driver should read/write modules from/to the cache.
  public var cachingIsEnabled: Bool {
    moduleCachePath != nil
  }

  /// Parses the source files in `inputs` and adds them to `module`.
  @discardableResult
  public mutating func parse(
    _ sources: [SourceFile], into module: Module.ID
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      modify(&program[module]) { (m) in
        for s in sources { m.addSource(s) }
      }
    }
    return (elapsed, program[module].containsError)
  }

  /// Assigns the trees in `module` to their scopes.
  @discardableResult
  public mutating func assignScopes(
    of module: Module.ID
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = await clock.measure {
      await program.assignScopes(module)
    }
    return (elapsed, program[module].containsError)
  }

  /// Assigns the trees in `module` to their types.
  @discardableResult
  public mutating func assignTypes(
    of module: Module.ID
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.assignTypes(module)
    }
    return (elapsed, program[module].containsError)
  }

  /// Lowers the contents of `module` to IR.
  @discardableResult
  public mutating func lower(
    _ module: Module.ID
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.lower(module)
    }
    return (elapsed, program[module].containsError)
  }

  /// Applies mandatory transformation passes on the IR of `module`.
  @discardableResult
  public mutating func applyTransformationPasses(
    _ module: Module.ID
  ) async -> (elapsed: Duration, containsError: Bool) {
    let elapsed = ContinuousClock().measure {
      program.applyTransformationPasses(module)
    }
    return (elapsed, program[module].containsError)
  }

  /// Generates backend code for `module`.
  public mutating func lowerToLLVM(_ module: Module.ID) async throws ->
    (elapsed: Duration, containsError: Bool) {
    precondition(llvmModules[module] == nil, "LLVM code is already generated for module \(moduleName(module))")

    let elapsed = try ContinuousClock().measure {
      let context = try CodeGenerationContext.transpiling(
        module, in: program, compilingFor: try makeTargetMachine())
      var m = context.extractModule()
      try m.verify()
      m.runDefaultModulePasses()
      try m.verify()
      llvmModules[module] = LLVMModuleBox(consume m)
    }
    return (elapsed, program[module].containsError)
  }

  /// Generates executable from `module`, linking the standard library unless `isFreestanding` is true.
  ///
  /// - Requires: `lowerToLLVM(_:)` has been called for `module`.
  public mutating func generateExecutable(
    for module: Module.ID,
    writingTo output: URL? = nil
  ) async throws -> (elapsed: Duration, containsError: Bool) {

    let fm = FileManager.default

    let elapsed = try ContinuousClock().measure {
      var modulesToLink = [module]
      if !isFreestanding {

        modulesToLink.append(module)
        modulesToLink.removeLast() // dummy mutation

        // modulesToLink.append(program.modules[.standardLibrary]!.identity) //todo enable this after we can lower the standard library
      }

      try fm.withUniqueTemporaryDirectory{ objectDirectory in

        let objectFiles = try writeObjectFiles(for: modulesToLink, into: objectDirectory)

        let canonicalExecutable = output ?? URL(fileURLWithPath: moduleName(module))
        let executable = canonicalExecutable.withHostExecutableSuffix()
        try fm.createDirectory(at: executable.deletingLastPathComponent(), withIntermediateDirectories: true)

        try linkExecutable(at: executable, with: objectFiles)

        executableOutputs[module] = executable
      }
    }
    return (elapsed, program[module].containsError)
  }

  /// Returns the LLVM IR generated for `module`, or `nil` if backend code has not been generated.
  public func llvmIR(of module: Module.ID) -> String? {
    llvmModules[module]?.module.llCode()
  }

  /// Returns the assembly generated for `module`.
  ///
  /// - Requires: `lowerToLLVM(_:)` has been called for `module`.
  public mutating func assembly(of module: Module.ID) throws -> String {
    let buffer = try llvmModules[module]!.module.compile(.assembly)
    return Self.decode(buffer)
  }

  /// Returns the executable produced for `module`, or `nil` if no executable has been generated.
  public func executableURL(of module: Module.ID) -> URL? {
    executableOutputs[module]
  }

  /// Writes object files for `modules` into `directory` and returns their paths.
  ///
  /// - Requires: `lowerToLLVM(_:)` has been called for each module in `modules`.
  @discardableResult
  public mutating func writeObjectFiles(
    for modules: [Module.ID], into directory: URL
  ) throws -> [URL] {
    try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
    var objectFiles = try modules.map { (module) in
      let object = directory.appendingPathComponent(moduleName(module) + ".o", isDirectory: false)
      try llvmModules[module]!.module.write(.objectFile, to: object.path)
      return object
    }
    if !isFreestanding {
      let shimsObject = directory.appendingPathComponent("stdlib_shims.o", isDirectory: false)
      _ = try runCommand(
        try findExecutable("clang"),
        arguments: ["-c", standardLibrary.shim.path, "-o", shimsObject.path])
      objectFiles.append(shimsObject)
    }
    return objectFiles
  }

  /// Loads `module`, whose sources are in `root`, into `program`.
  ///
  /// If `moduleCachePath` is set, the module is loaded from cache if an archive is found and its
  /// fingerprint matches the fingerprint of the source files in `root`. Otherwise, the module is
  /// compiled from sources and an archive is stored at `moduleCachePath`. If `moduleCachePath` is
  /// not set, the module is unconditionally compiled from sources and no archive is stored.
  public mutating func load(
    _ module: Module.Name, withSourcesAt root: URL
  ) async throws {
    // Compute a fingerprint of all source files.
    var sources: [SourceFile] = []
    try SourceFile.forEach(in: root) { (s) in
      sources.append(s)
    }

    // Attempt to load the module from disk.
    if cachingIsEnabled, let data = archive(of: module) {
      let h = SourceFile.fingerprint(contentsOf: sources)
      var a = ReadableArchive(data)
      let (_, fingerprint) = try Module.header(&a)
      if h == fingerprint {
        a = ReadableArchive(data)
        _ = try program.load(module: module, from: &a)
        return
      }
    }

    // Compile the module from sources.
    let m = program.demandModule(module)

    await parse(sources, into: m)
    try throwIfContainsError(m)

    await assignScopes(of: m)
    try throwIfContainsError(m)

    await assignTypes(of: m)
    try throwIfContainsError(m)

    if cachingIsEnabled {
      let a = try program.archive(module: m)
      let f = moduleCachePath!.appending(component: module + ".hylomodule")
      try a.write(into: f)
    }
  }

  /// Loads the standard library with `load(_:withSourcesAt:)`.
  ///
  /// Use the `USE_BUNDLED_STANDARD_LIBRARY` compiler flag to control whether the
  /// bundled or local standard library is used. Defaults to local.
  public mutating func loadStandardLibrary() async throws {
    let sourceRoot: URL
    #if USE_BUNDLED_STANDARD_LIBRARY // Set compiler flag in distributable builds.
    sourceRoot = bundledStandardLibrarySources
    #else
    sourceRoot = localStandardLibrarySources
    #endif
    try await load(Module.standardLibraryName, withSourcesAt: sourceRoot)
  }

  /// Searches for an archive of `module` in `librarySearchPaths`, returning it if found.
  public func archive(of module: Module.Name) -> Data? {
    if let prefix = moduleCachePath {
      let path = prefix.appending(path: module + ".hylomodule")
      return try? Data(contentsOf: path)
    } else {
      return nil
    }
  }

  /// Throws the diagnostics of `m` if those contain an error.
  private func throwIfContainsError(_ m: Module.ID) throws {
    if program[m].containsError {
      throw CompilationError(diagnostics: .init(program[m].diagnostics))
    }
  }

  /// Creates a target machine according to the provided target configuration, resolving the host values when needed.
  private func makeTargetMachine() throws -> SwiftyLLVM.TargetMachine {
    let host = try SwiftyLLVM.TargetMachine.host()
    let triple = targetConfiguration.targetTriple.resolvedWith(hostValue: host.triple)
    let options = SwiftyLLVM.TargetMachineOptions(
      cpu: targetConfiguration.cpu.resolvedWith(hostValue: host.cpu),
      features: targetConfiguration.features.resolvedWith(hostValue: host.features),
      relocation: defaultRelocationModel())

    return try SwiftyLLVM.TargetMachine(options: options, triple: triple)
  }

  /// The relocation model that all Hylo object files will get (for the time being).
  private func defaultRelocationModel() -> SwiftyLLVM.RelocationModel {
    #if os(Windows)
      .default
    #else
      .pic
    #endif
  }

  private func linkExecutable(at output: URL, with objectFiles: [URL]) throws {
    var arguments = ["-fuse-ld=lld", "-o", output.path]
    arguments.append(contentsOf: librarySearchPaths.map({ "-L\($0.path)" }))
    arguments.append(contentsOf: objectFiles.map(\.path))
    #if os(macOS)
    let sdk = try runCommand(
      try findExecutable("xcrun"),
      arguments: ["--sdk", "macosx", "--show-sdk-path"]).standardOutput
      .trimmingCharacters(in: .whitespacesAndNewlines)
    arguments += ["-isysroot", sdk, "-lSystem"]
    #elseif os(Windows)
    arguments.append("-lucrt")
    #endif
    arguments.append(contentsOf: libraries.map({ "-l\($0)" }))
    _ = try runCommand(try findExecutable("clang"), arguments: arguments)
  }

  private func resolvedExecutableURL(for module: Module.ID, writingTo output: URL?) -> URL {
    let base = output ?? URL(fileURLWithPath: moduleName(module))
    if base.pathExtension == hostExecutableExtension { return base }
    return base.appendingPathExtension(hostExecutableExtension)
  }

  private var hostExecutableExtension: String {
    #if os(Windows)
      "exe"
    #else
      ""
    #endif
  }

  private func findExecutable(_ invocationName: String) throws -> URL {
    let executableName = hostExecutableExtension.isEmpty
      ? invocationName
      : invocationName + ".\(hostExecutableExtension)"
    let environment = ProcessInfo.processInfo.environment
    let path = environment[hostPathEnvironmentVariable] ?? ""

    for root in path.split(separator: hostPathSeparator) {
      let candidate = URL(fileURLWithPath: String(root)).appendingPathComponent(executableName)
      if FileManager.default.isExecutableFile(atPath: candidate.path) {
        return candidate
      }
    }

    throw DriverFailure.missingExecutable(invocationName)
  }

  private var hostPathEnvironmentVariable: String {
    #if os(Windows)
      "Path"
    #else
      "PATH"
    #endif
  }

  private var hostPathSeparator: Character {
    #if os(Windows)
      ";"
    #else
      ":"
    #endif
  }

  private func runCommand(_ executable: URL, arguments: [String]) throws -> ExecutionResult {
    let process = Process()
    let standardOutput = Pipe()
    let standardError = Pipe()
    process.executableURL = executable
    process.arguments = arguments
    process.standardOutput = standardOutput
    process.standardError = standardError
    try process.run()
    process.waitUntilExit()

    let output = String(
      decoding: standardOutput.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let error = String(
      decoding: standardError.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)

    guard process.terminationStatus == 0 else {
      throw DriverFailure.commandFailed(
        executable.path, arguments, process.terminationStatus, error.isEmpty ? output : error)
    }

    return .init(standardOutput: output, standardError: error, terminationStatus: process.terminationStatus)
  }

  private func moduleName(_ module: Module.ID) -> String {
    program.modules.elements[module].key
  }

  private static func decode(_ buffer: borrowing SwiftyLLVM.MemoryBuffer) -> String {
    buffer.withUnsafeBytes({ (bytes) in
      String(decoding: bytes.map(UInt8.init(bitPattern:)), as: UTF8.self)
    })
  }

  private final class LLVMModuleBox {

    var module: LLVMModule

    init(_ module: consuming LLVMModule) {
      self.module = module
    }

  }

  private struct ExecutionResult {
    let standardOutput: String
    let standardError: String
    let terminationStatus: Int32
  }

  private enum DriverFailure: LocalizedError, CustomStringConvertible {

    case commandFailed(String, [String], Int32, String)
    case missingBackendArtifact(String)
    case missingExecutable(String)

    var errorDescription: String {
      switch self {
      case .commandFailed(let executable, let arguments, let status, let output):
        let command = ([executable] + arguments).joined(separator: " ")
        if output.isEmpty {
          return "command failed with exit code \(status): \(command)"
        } else {
          return "command failed with exit code \(status): \n $ \(command)\n\(output)"
        }
      case .missingBackendArtifact(let module):
        return "missing backend artifact for module '\(module)'"
      case .missingExecutable(let executable):
        return "required executable not found on PATH: \(executable)"
      }
    }

    var description: String { "\n\(errorDescription)" }

  }

}

extension FileManager {
  /// Creates an empty temporary directory for the duration of the given observer.
  public func withUniqueTemporaryDirectory<T>(_ observer: (URL) throws -> T) throws -> T {
    let directory = temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
    try createDirectory(at: directory, withIntermediateDirectories: true)
    defer { try? removeItem(at: directory) }
    return try observer(directory)
  }  
  
  /// Creates an empty temporary directory for the duration of the given observer.
  public func withUniqueTemporaryDirectory<T>(_ observer: (URL) async throws -> T) async throws -> T {
    let directory = temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
    try createDirectory(at: directory, withIntermediateDirectories: true)
    defer { try? removeItem(at: directory) }
    return try await observer(directory)
  }
}

extension URL {
  /// Ensures that the URL has an executable extension corresponding to the host platform.
  public func withHostExecutableSuffix() -> URL {
    #if os(Windows)
    return pathExtension == "exe" ? self : appendingPathExtension("exe")
    #else
    return self
    #endif
  }
}