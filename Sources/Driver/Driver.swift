import Archivist
import BackEnd
import Foundation
import FrontEnd
import StandardLibrary
import Subprocess
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

  /// The linker's library search path.
  public var librarySearchPath: [URL]

  /// The directories in which imported module archives (`.hylomodule` files) are searched.
  public var moduleSearchPath: [URL]

  /// The names of the native libraries to link (in addition to any imported Hylo dependencies).
  public var librariesToLink: [String]

  /// `true` iff compilation and linking depend on the standard library and its shim.
  public private(set) var usesStandardLibrary: Bool = false

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

  #if USE_BUNDLED_STANDARD_LIBRARY // Set compiler flag in distributable builds.
  /// The root folder of the standard library's sources.
  public static let standardLibraryRoot = bundledStandardLibrarySources
  #else
  /// The root folder of the standard library's sources.
  public static let standardLibraryRoot = localStandardLibrarySources
  #endif

  /// The file within `standardLibraryRoot` implementing the standard library's
  /// `@extern_c_indirect` declarations.
  ///
  /// Build systems linking Hylo objects must compile and link this except in freestanding mode.
  public static var standardLibraryCShim: URL {
    standardLibraryRoot.appending(component: cShimSource)
  }

  /// Creates an instance with the given properties.
  public init(
    moduleCachePath: URL? = nil, targetSpecification: TargetSpecification,
    optimization: OptimizationLevel = .none,
    relocation: RelocationModel = Driver.defaultRelocationModel,
    codeModel: CodeModel = .default,
    librarySearchPath: [URL] = [], moduleSearchPath: [URL] = [],
    librariesToLink: [String] = []
  ) {
    self.moduleCachePath = moduleCachePath
    self.target = targetSpecification
    self.optimization = optimization
    self.relocation = relocation
    self.codeModel = codeModel
    self.librarySearchPath = librarySearchPath
    self.moduleSearchPath = moduleSearchPath
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
  public mutating func assignScopes(of module: Module.ID) async -> PhaseResult {
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
  public mutating func lower(_ module: Module.ID) async -> PhaseResult {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.lower(module)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Applies mandatory transformation passes on the IR of `module`.
  @discardableResult
  public mutating func applyTransformationPasses(_ module: Module.ID) async -> PhaseResult {
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
      var llvm = try program.compileToLLVM(module, target: t)

      try verify(llvm)
      llvm.runDefaultModulePasses(optimization: optimization)
      try verify(llvm)

      llvmModules[module] = LLVMModuleBox(consume llvm)
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Applies LLVM IR verification passes to `m` iff this file has been compiled in debug
  /// mode; does nothing otherwise.
  ///
  /// - Throws: if the contents of `m` failed verification.
  private func verify(_ m: borrowing SwiftyLLVM.Module) throws {
    do {
      try m.verifyInDebugBuilds()
    } catch let e as LLVMError {
      throw Error.llvmVerificationFailure(message: e.description, contents: m.description)
    }
  }

  /// Generates an executable from `module` and its dependencies.
  ///
  /// - Requires: `module` has been lowered to LLVM.
  /// - Throws: if the parent folder of `output` doesn't exist.
  public mutating func generateExecutable(
    from module: Module.ID,
    withCSources cSources: [URL] = [],
    writingTo output: URL
  ) async throws -> PhaseResult {
    // FIXME: Enable this after we can lower the standard library
    // modulesToLink.append(program.modules[.standardLibrary]!.identity)
    let shimObject: URL? = if usesStandardLibrary {
      try await StandardLibraryShimCache.shared.object(compiledWith: relocation)
    } else {
      nil
    }

    let elapsed = try await ContinuousClock().measure {
      let modulesToLink = [module]
      // FIXME: link the dependencies of `module`.

      try await FileManager.default.withUniqueTemporaryDirectory { (d) in
        let hyloObjects = try emitObjectFiles(for: modulesToLink, into: d)
        var cObjects: [URL] = []
        for s in cSources {
          cObjects.append(try await compileCToObject(source: s, destinationDirectory: d))
        }
        if let o = shimObject {
          cObjects.append(o)
        }
        try await linkExecutable(from: hyloObjects + cObjects, writingTo: output)
      }
    }
    return .init(elapsed: elapsed, containsError: program[module].containsError)
  }

  /// Returns the LLVM IR generated for `module`, if any.
  public func llvmIR(of module: Module.ID) -> String? {
    llvmModules[module]?.module.llCode()
  }

  /// Returns the assembly of `module`.
  ///
  /// - Requires: `module` has been lowered to LLVM.
  public func assembly(of module: Module.ID) throws -> String {
    try llvmModules[module]!.module.compile(.assembly).utf8Decoded
      .unwrapOrThrow(Error.invalidAssemblyEncoding)
  }

  /// Writes object files for `modules` into `destinationDirectory` and returns their paths.
  ///
  /// - Requires: each element of `modules` has been lowered to LLVM.
  /// - Throws: if `destinationDirectory` doesn't exist.
  @discardableResult
  public func emitObjectFiles(
    for modules: [Module.ID], into destinationDirectory: URL
  ) throws -> [URL] {
    try modules.map { (m) in
      let o = destinationDirectory.appendingPathComponent(moduleName(m) + ".o", isDirectory: false)
      try emitObjectFile(of: m, to: o)
      return o
    }
  }

  /// Writes the object file of `module` to `output`.
  ///
  /// - Requires: `module` has been already lowered to LLVM.
  public func emitObjectFile(of module: Module.ID, to output: URL) throws {
    try llvmModules[module]!.module.write(.objectFile, to: output.path)
  }

  /// Compiles `source` using `clang` to an object file.
  ///
  /// Returns the path to the object file within `destinationDirectory`.
  public func compileCToObject(source: URL, destinationDirectory: URL) async throws -> URL {
    let uniquePrefix = source.hashValue
    let fileName = source.deletingPathExtension().appendingPathExtension("o").lastPathComponent

    let o = destinationDirectory.appendingPathComponent("\(uniquePrefix)-\(fileName)",
      isDirectory: false)

    var a = ["-c", source.path, "-o", o.path]
    if let r = relocation.asClangArgument { a.append(r) }

    _ = try await subprocessOutput(of: .name("clang"), arguments: a)
    return o
  }

  /// Loads `module`, whose sources are at `root`, into `program`.
  ///
  /// If `moduleCachePath` is set, the module is loaded from cache if an archive is found and its
  /// fingerprint matches the fingerprint of the source files in `root`. Otherwise, the module is
  /// compiled from sources and an archive is stored at `moduleCachePath`; A cached archive that
  /// cannot be parsed is compiled from sources and overwritten.
  public mutating func load(
    _ module: Module.Name, withSourcesAt root: URL, additionalSources: [SourceFile] = []
  ) async throws {
    let sources = additionalSources + (try sources(at: root))

    // If caching is enabled, load the module from disk or compile and cache it if that failed.
    if cachingIsEnabled {
      if try !loadCached(module, matching: sources) {
        let m = try await compile(module, from: sources)
        try writeToCache(m)
      }
    }
    // Otherwise, ignore the cache entirely.
    else {
      _ = try await compile(module, from: sources)
    }
  }

  /// Loads `module` from its cache and returns `true` iff its fingerprint matches that of `s`
  private mutating func loadCached(_ module: Module.Name, matching s: [SourceFile]) throws -> Bool {
    guard let data = cachedArchive(of: module) else { return false }
    do {
      var a = ReadableArchive(data)
      let (name, fingerprint) = try Module.header(&a)
      // Invalid name or fingerprint.
      guard name == module, fingerprint == SourceFile.fingerprint(contentsOf: s) else {
        return false
      }

      a = ReadableArchive(data)
      try program.load(module: module, from: &a)
      return true
    } catch is ArchiveError {
      return false
    }
  }

  /// Compiles the module named `n` from `sources` to refined IR, returning its identifier.
  private mutating func compile(
    _ n: Module.Name, from sources: [SourceFile]
  ) async throws -> Module.ID {
    let m = program.demandModule(n)

    if usesStandardLibrary && (n != Module.standardLibraryName) {
      program[m].addDependency(Module.standardLibraryName)
    }

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

    return m
  }

  /// Writes `module` to the module cache.
  ///
  /// - Requires: `cachingIsEnabled` is `true`.
  private func writeToCache(_ module: Module.ID) throws {
    let f = moduleCachePath!.appending(component: program[module].name + ".hylomodule")
    try writeArchive(of: module, to: f)
  }

  /// Loads the standard library with `load(_:withSourcesAt:)` and makes
  /// standard library a dependency of modules loaded thereafter.
  ///
  /// Use the `USE_BUNDLED_STANDARD_LIBRARY` compiler flag to control whether the  bundled or local
  /// standard library is used. Defaults to local.
  public mutating func loadStandardLibrary() async throws {
    try await load(
      Module.standardLibraryName, withSourcesAt: Driver.standardLibraryRoot,
      additionalSources: [SourceFile(contentsOf: generatedStandardLibrarySource)])
    usesStandardLibrary = true
  }

  /// Replaces the program of `self` with `p`, which contains an already loaded standard library,
  /// and makes the standard library a dependency of modules loaded thereafter.
  public mutating func installStandardLibrary(from p: Program) {
    precondition(p.modules[Module.standardLibraryName] != nil,
      "program does not contain the standard library")
    program = p
    usesStandardLibrary = true
  }

  /// Returns the archive of `module` in the module cache if present, `nil` otherwise.
  internal func cachedArchive(of module: Module.Name) -> Data? {
    guard let c = moduleCachePath else { return nil }
    return try? Data(contentsOf: c.appending(path: module + ".hylomodule"))
  }

  /// Returns the location and contents of `module`'s archive found in `moduleSearchPath`, if any.
  ///
  /// - Throws if an archive exists but cannot be read.
  private func importedArchive(of module: Module.Name) throws -> (url: URL, data: Data)? {
    for prefix in moduleSearchPath {
      let u = prefix.appending(path: module + ".hylomodule")
      if FileManager.default.fileExists(atPath: u.path) {
        do {
          return (u, try Data(contentsOf: u))
        } catch {
          throw Error.unreadableModuleArchive(module: module, location: u, cause: error)
        }
      }
    }
    return nil
  }

  /// Loads `module` and its dependencies from archives found in `moduleSearchPath`, returning the
  /// identity of `module`.
  ///
  /// Unlike the module cache, which silently recompiles unusable entries, a malformed archive in a
  /// module search path is reported as an `Error` naming the offending file.
  @discardableResult
  public mutating func loadArchivedModule(_ module: Module.Name) throws -> Module.ID {
    var ms = Set<Module.Name>()
    return try loadArchivedModule(module, modulesStartedLoading: &ms)
  }

  /// Loads `module` and its dependencies from archives found in `moduleSearchPath`, returning the
  /// identity of `module` and using `modulesStartedLoading` to detect circular dependencies.
  @discardableResult
  private mutating func loadArchivedModule(
    _ module: Module.Name, modulesStartedLoading: inout Set<Module.Name>
  ) throws -> Module.ID {
    // Nothing to do if the module is already loaded.
    if let module = program.identity(module: module) { return module }

    if !modulesStartedLoading.insert(module).inserted {
      throw Error.circularModuleDependency(module: module)
    }

    guard let (source, data) = try importedArchive(of: module) else {
      throw Error.moduleArchiveNotFound(module: module, searchPaths: moduleSearchPath)
    }

    // TODO: save fingerprint of dependencies and check that they match the version `module` was
    // compiled against.

    // Ensure the dependencies are loaded before we load `module`.
    var a = ReadableArchive(data)

    let h: (name: Module.Name, fingerprint: UInt64, dependencies: [Module.Name])
    do { h = try Module.headerAndDependencies(&a) }
    catch { throw Error.invalidModuleArchive(module: module, location: source) }

    guard h.name == module else {
      throw Error.moduleNameMismatch(module: module, location: source, name: h.name)
    }
    for d in h.dependencies {
      try loadArchivedModule(d, modulesStartedLoading: &modulesStartedLoading)
    }

    var body = ReadableArchive(data)
    do {
      return try program.load(module: module, from: &body).identity
    } catch is ArchiveError {
      throw Error.invalidModuleArchive(module: module, location: source)
    }
  }

  /// Writes the archive of `module` to `output`.
  ///
  /// The parent directories of `output` are expected to exist.
  public func writeArchive(of module: Module.ID, to output: URL) throws {
    try program.archive(module: module).write(into: output)
  }

  /// Returns a hash of `module` that a build system can use as a rebuild key for its dependents.
  public func moduleInterfaceHash(of module: Module.ID) throws -> UInt64 {
    // TODO: Make the interface hash resilient to changes in function bodies.
    // https://github.com/hylo-lang/hylo-new/issues/321

    // Note: avoiding `.hashValue` for consistency across runs and host platforms.
    let a = try program.archive(module: module)
    return FNV1.hash(a, into: FNV1.u64()).state
  }

  /// Throws the diagnostics of `module` if those contain an error.
  private func throwIfContainsError(_ module: Module.ID) throws {
    if program[module].containsError {
      throw CompilationError(diagnostics: .init(program[module].diagnostics))
    }
  }

  /// Links the provided object files into an executable at `output`, using lld.
  ///
  /// - Throws: if the parent folder of `output` doesn't exist.
  private func linkExecutable(from objectFiles: [URL], writingTo output: URL) async throws {
    var arguments = ["-o", output.path]
    arguments += librarySearchPath.map({ "-L\($0.path)" })
    arguments += librariesToLink.map({ "-l\($0)" })
    arguments += objectFiles.map(\.path)

    #if os(macOS)
    let sdk = try await subprocessOutput(
      of: .name("xcrun"), arguments: ["--sdk", "macosx", "--show-sdk-path"])
      .trimmingCharacters(in: .whitespacesAndNewlines)
    arguments += ["-isysroot", sdk, "-lSystem"]
    #endif
    #if os(Linux)
    // Instruction selection may lower some instructions (e.g., `frem`) to libm calls.
    arguments += ["-lm"]
    #endif

    _ = try await subprocessOutput(of: .name("clang"), arguments: arguments)
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
    init(_ m: consuming LLVMModule) {
      self.module = m
    }

  }

  /// An error thrown by the driver.
  public enum Error: Swift.Error, CustomStringConvertible {

    /// The `.hylomodule` archive of `module` at `location` could not be parsed.
    case invalidModuleArchive(module: Module.Name, location: URL)

    /// The `.hylomodule` archive of `module` at `location` could not be read because of `cause`.
    case unreadableModuleArchive(module: Module.Name, location: URL, cause: Swift.Error)

    /// The `.hylomodule` archive of `module` at `location` declares another module named `name`.
    case moduleNameMismatch(module: Module.Name, location: URL, name: Module.Name)

    /// No `.hylomodule` archive of `module` was found in the directories `searchPaths`.
    case moduleArchiveNotFound(module: Module.Name, searchPaths: [URL])

    /// A circular dependency was detected while loading `module`.
    case circularModuleDependency(module: Module.Name)

    /// LLVM verification failed with `message` while processing a module with `contents`.
    case llvmVerificationFailure(message: String, contents: String)

    /// The assembly of a module could not be decoded as an UTF-8 string.
    case invalidAssemblyEncoding

    /// A textual description of the error.
    public var description: String {
      switch self {
      case .invalidModuleArchive(let module, let location):
        """
        Failed to parse the module archive of '\(module)' at '\(location.path)'.

        Maybe the archive was compiled with a different version of the compiler. \
        Try erasing the module cache.
        """
      case .unreadableModuleArchive(let module, let location, let cause):
        "Failed to read module archive of '\(module)' at '\(location.path)': \(cause)"
      case .moduleNameMismatch(let module, let location, let name):
        "Archive of '\(module)' at '\(location.path)' declares a module named '\(name)'."
      case .moduleArchiveNotFound(let module, let searchPaths):
        """
        No archive found for module '\(module)' in module search paths \
        [\(searchPaths.map(\.path).joined(separator: ", "))].
        """
      case .circularModuleDependency(let module):
        "Circular dependency detected while loading module '\(module)'."
      case .llvmVerificationFailure(let message, let contents):
        """
        LLVM verification failed with the following message: \(message)

        Module contents:
        \(contents)
        """
      case .invalidAssemblyEncoding:
        "Failed to decode assembly as an UTF8 string."
      }
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

  /// A process-wide cache of object files compiled from the standard library's C shim, keyed by the
  /// relocation model with which they were compiled.
  private actor StandardLibraryShimCache {

    /// The shared instance.
    static let shared = StandardLibraryShimCache()

    /// The location of the compiled shim for each relocation model.
    private var objects: [RelocationModel: URL] = [:]

    /// Returns an object file compiled from the standard library's C shim with `relocation`,
    /// compiling it at most once per process into a temporary directory that lives until the
    /// process exits.
    func object(compiledWith relocation: RelocationModel) async throws -> URL {
      if let o = objects[relocation] { return o }

      let d = try FileManager.default.createUniqueTemporaryDirectory()
      let s = Driver.standardLibraryCShim
      let o = d.appendingPathComponent("shims.o", isDirectory: false)

      var a = ["-c", s.path, "-o", o.path]
      if let r = relocation.asClangArgument { a.append(r) }

      _ = try await subprocessOutput(of: .name("clang"), arguments: a)
      objects[relocation] = o
      return o
    }

  }

}

/// Returns the source files at `path`.
///
/// If `path` is a file, the result contains that file.
/// If `path` is a directory, the result contains all source files in that
/// directory and subdirectories.
private func sources(at path: URL) throws -> [SourceFile] {
  if path.pathExtension == "hylo" {
    return [try SourceFile(contentsOf: path)]
  } else {
    var s: [SourceFile] = []
    try SourceFile.forEach(in: path) {
      s.append($0)
    }
    return s
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
