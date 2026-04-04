import Archivist
import BackEnd
import Foundation
import FrontEnd
import StandardLibrary
import SwiftyLLVM
import Utilities

/// Utilities and constants related to the host machine.
private typealias Host = Utilities.Host

/// A SwiftyLLVM module.
private typealias LLVMModule = SwiftyLLVM.Module

/// A FrontEnd module.
public typealias Module = FrontEnd.Module // Shadowing the name ambiguity

/// A helper to drive the compilation of Hylo source files.
public struct Driver {

  /// The path containing cached module data.
  public let moduleCachePath: URL?

  /// The target specification (triple + CPU + features).
  public var target: TargetSpecification

  /// The optimization level for code generation.
  public var optimization: OptimizationLevel

  /// The relocation model for code generation.
  public var relocation: RelocationModel

  /// The code model for code generation.
  public var codeModel: CodeModel

  /// The list of directories in which to search for libraries to link.
  public var librarySearchPaths: [URL]

  /// The names of the native libraries to link.
  public var librariesToLink: [String]

  /// `true` iff the standard library and its shim should be excluded from compilation and linking.
  public var noStandardLibrary: Bool = false

  /// The program being compiled by the driver.
  public var program: Program

  /// A map from a Hylo module to its corresponding LLVM module, populated by `lowerToLLVM(_:)`.
  private var llvmModules: [Module.ID: LLVMModuleBox] = [:]

  /// The relocation model that suits the host platform when none is specified.
  ///
  /// On Linux, the system toolchain links position-independent executables (PIE) by default, which
  /// requires position-independent object code; emitting code with the target's own default (which
  /// is `static` on x86-64 Linux) produces absolute relocations that the PIE linker rejects.
  /// Elsewhere we defer to the target's default.
  public static var defaultRelocationModel: RelocationModel {
    #if os(Linux)
      return .pic
    #else
      return .default
    #endif
  }

  /// Creates an instance with the given properties.
  public init(
    moduleCachePath: URL? = nil, targetSpecification: TargetSpecification,
    optimization: OptimizationLevel = .none,
    relocation: RelocationModel = Driver.defaultRelocationModel,
    codeModel: CodeModel = .default,
    librarySearchPaths: [URL] = [], librariesToLink: [String] = []
  ) {
    self.moduleCachePath = moduleCachePath
    self.target = targetSpecification
    self.optimization = optimization
    self.relocation = relocation
    self.codeModel = codeModel
    self.librarySearchPaths = librarySearchPaths
    self.librariesToLink = librariesToLink
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
  ) async -> PhaseResult {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      modify(&program[module]) { (m) in
        for s in sources { m.addSource(s) }
      }
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Assigns the trees in `module` to their scopes.
  @discardableResult
  public mutating func assignScopes(
    of module: Module.ID
  ) async -> PhaseResult {
    let clock = ContinuousClock()
    let elapsed = await clock.measure {
      await program.assignScopes(module)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Assigns the trees in `module` to their types.
  @discardableResult
  public mutating func assignTypes(
    of module: Module.ID,
    loggingInferenceWhere isLoggingEnabled: ((AnySyntaxIdentity, Program) -> Bool)? = nil
  ) async -> PhaseResult {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.assignTypes(module, loggingInferenceWhere: isLoggingEnabled)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Lowers the contents of `module` to IR.
  @discardableResult
  public mutating func lower(
    _ module: Module.ID
  ) async -> PhaseResult {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.lower(module)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Applies mandatory transformation passes on the IR of `module`.
  @discardableResult
  public mutating func applyTransformationPasses(
    _ module: Module.ID
  ) async -> PhaseResult {
    let elapsed = ContinuousClock().measure {
      program.applyTransformationPasses(module)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Lowers the program to LLVM IR and stores the result in `self.llvmModules`.
  ///
  /// - Requires:
  ///   - `module` has been lowered and all required transformation passes have been run.
  ///   - `module` has not been lowered to LLVM IR yet.
  public mutating func compileToLLVM(_ module: Module.ID) throws -> PhaseResult {
    precondition(
      llvmModules[module] == nil, "LLVM IR already generated for '\(moduleName(module))'")

    let elapsed = try ContinuousClock().measure {
      let t = TargetMachine(
        target: target, optimization: optimization, relocation: relocation, codeModel: codeModel)
      var m = try program.compileToLLVM(module, target: t)

      try verify(m)
      m.runDefaultModulePasses(optimization: optimization)
      try verify(m)

      llvmModules[module] = LLVMModuleBox(consume m)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Applies LLVM IR verification passes to `module` iff this file has been compiled in debug
  /// mode; does nothing otherwise.
  ///
  /// - Throws: if the contents of `module` failed verification.
  private func verify(_ module: borrowing SwiftyLLVM.Module) throws {
    do {
      try module.verifyInDebugBuilds()
    } catch let e as LLVMError {
      throw Error(
        message: """
        LLVM verification failed with the following message: \(e.description)

        Module contents:
        \(module.description)
        """)
    }
  }

  /// Generates an executable from `module` and its dependencies.
  ///
  /// - Requires: `module` has been lowered to LLVM.
  /// - Throws: if the parent folder of `output` doesn't exist.
  public mutating func generateExecutable(
    from module: Module.ID,
    writingTo output: URL
  ) throws -> PhaseResult {
    let elapsed = try ContinuousClock().measure {
      let modulesToLink = [module]
      // FIXME: link the dependencies of `module`.

      if !noStandardLibrary {
        // FIXME: Enable this after we can lower the standard library
        // modulesToLink.append(program.modules[.standardLibrary]!.identity)
      }

      try FileManager.default.withUniqueTemporaryDirectory { (d) in
        let objects = try writeObjectFiles(for: modulesToLink, into: d)
        try linkExecutable(from: objects, writingTo: output)
      }
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Returns the LLVM IR generated for `module`, if any.
  public func llvmIR(of module: Module.ID) -> String? {
    llvmModules[module]?.module.llCode()
  }

  /// Returns the assembly of module `m`.
  ///
  /// - Requires: module `m` has been lowered to LLVM.
  public func assembly(of m: Module.ID) throws -> String {
    try llvmModules[m]!.module.compile(.assembly).utf8Decoded
      .unwrapOrThrow(Error(message: "Failed to decode assembly as an UTF8 string."))
  }

  /// Writes object files for `modules` into `destinationDirectory` and returns their paths.
  ///
  /// - Requires: each element of `modules` has been lowered to LLVM.
  /// - Throws: if `destinationDirectory` doesn't exist.
  @discardableResult
  public func writeObjectFiles(
    for modules: [Module.ID], into destinationDirectory: URL
  ) throws -> [URL] {
    try modules.map { (m) in
      let o = destinationDirectory.appendingPathComponent(moduleName(m) + ".o", isDirectory: false)
      try llvmModules[m]!.module.write(.objectFile, to: o.path)
      return o
    }
  }

  /// Loads `module`, whose sources are in `root`, into `program`.
  ///
  /// If `moduleCachePath` is set, the module is loaded from cache if an archive is found and its
  /// fingerprint matches the fingerprint of the source files in `root`. Otherwise, the module is
  /// compiled from sources and an archive is stored at `moduleCachePath`. If `moduleCachePath` is
  /// not set, the module is unconditionally compiled from sources and no archive is stored.
  public mutating func load(
    _ module: Module.Name, withSourcesAt root: URL, additionalSources: [SourceFile] = []
  ) async throws {
    // Compute a fingerprint of all source files.
    var sources: [SourceFile] = additionalSources
    try SourceFile.forEach(in: root) { (s) in
      sources.append(s)
    }

    // Attempt to load the module from disk.
    do {
      if cachingIsEnabled, let data = archive(of: module) {
        let h = SourceFile.fingerprint(contentsOf: sources)
        var a = ReadableArchive(data)
        let (_, fingerprint) = try Module.header(&a)
        if h == fingerprint {
          a = ReadableArchive(data)
          try program.load(module: module, from: &a)
          return
        }
      }
    } catch ArchiveError.invalidInput {
      let m = """
        Failed to parse module archive of '\(module)' at '\(moduleCachePath, default: "nil")'.

        Maybe the archive was compiled with a different version of the compiler. \
        Try erasing the module cache.
        """
      throw Error(message: m)
    }

    // Compile the module from sources.
    let m = program.demandModule(module)

    await parse(sources, into: m)
    try throwIfContainsError(m)

    await assignScopes(of: m)
    try throwIfContainsError(m)

    await assignTypes(of: m)
    try throwIfContainsError(m)

    await lower(m)
    try throwIfContainsError(m)

    await applyTransformationPasses(m)
    try throwIfContainsError(m)

    if cachingIsEnabled {
      let a = try program.archive(module: m)
      let f = moduleCachePath!.appending(component: module + ".hylomodule")
      try a.write(into: f)
    }
  }

  /// Loads the standard library with `load(_:withSourcesAt:)`.
  /// 
  /// Use the `USE_BUNDLED_STANDARD_LIBRARY` compiler flag to control whether the  bundled or local
  /// standard library is used. Defaults to local.
  public mutating func loadStandardLibrary() async throws {
    #if USE_BUNDLED_STANDARD_LIBRARY // Set compiler flag in distributable builds.
    let sourceRoot = bundledStandardLibrarySources
    #else
    let sourceRoot = localStandardLibrarySources
    #endif
    try await load(Module.standardLibraryName, withSourcesAt: sourceRoot, 
      additionalSources: [SourceFile(contentsOf: generatedStandardLibrarySource)])
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

  /// Links the provided object files into an executable at `output`, using lld.
  ///
  /// - Throws: if the parent folder of `output` doesn't exist.
  private func linkExecutable(from objectFiles: [URL], writingTo output: URL) throws {
    var arguments = ["-o", output.path]
    arguments += librarySearchPaths.map({ "-L\($0.path)" })
    arguments += librariesToLink.map({ "-l\($0)" })
    arguments += objectFiles.map(\.path)

    #if os(macOS)
    let xcrun = try Host.findNativeExecutable(invokedAs: "xcrun")
    let sdk = try Process.executionOutput(xcrun, arguments: ["--sdk", "macosx", "--show-sdk-path"])
      .trimmingCharacters(in: .whitespacesAndNewlines)
    arguments += ["-isysroot", sdk, "-lSystem"]
    #endif

    let clang = try Host.findNativeExecutable(invokedAs: "clang")
    _ = try Process.executionOutput(clang, arguments: arguments)
  }

  /// The name of `module`.
  private func moduleName(_ module: Module.ID) -> String {
    program.modules.elements[module].key
  }

  /// A reference-semantic wrapper for the non-copiable `LLVMModule` type.
  ///
  /// Allows `LLVMModule` to be stored in a collection.
  private final class LLVMModuleBox {

    /// The wrapped module.
    var module: LLVMModule

    /// Wraps `module` by consuming it.
    init(_ module: consuming LLVMModule) {
      self.module = module
    }

  }

  /// An error thrown by the driver.
  public struct Error: Swift.Error, CustomStringConvertible {

    /// The error message.
    public let message: String

    /// The error message.
    public var description: String {
      message
    }

  }

  /// The result of a compilation phase.
  ///
  /// Used for logging and early termination.
  public struct PhaseResult {

    /// The elapsed time during the subtask's execution.
    public let elapsed: Duration

    /// `true` iff after the subtask's execution, the program contains errors.
    public let containsError: Bool

    /// Creates a new instance from its parts.
    public init(elapsed: Duration, containsError: Bool) {
      self.elapsed = elapsed
      self.containsError = containsError
    }

  }

}

extension SwiftyLLVM.Module {

  /// Verifies the IR in `self` iff this function has been compiled in debug mode.
  fileprivate func verifyInDebugBuilds() throws {
    var isDebug = false
    assert({ isDebug = true ; return isDebug }())
    if isDebug { try self.verify() }
  }

}
