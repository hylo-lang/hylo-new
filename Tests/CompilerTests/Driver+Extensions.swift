import Driver
import Foundation
import FrontEnd
import Utilities

/// The program containing the standard library, initialized exactly once per process.
///
/// The standard library is loaded from the archive cache if an up-to-date archive exists and
/// compiled from its sources otherwise.
private let sharedStandardLibrary = Task { () throws -> Program in
  do {
    return try await standardLibraryProgram()
  } catch Driver.Error.invalidModuleArchive(_, .some(let location)) {
    let a = location.appending(component: Module.standardLibraryName + ".hylomodule")
    try? FileManager.default.removeItem(at: a)
    return try await standardLibraryProgram()
  }
}

extension Driver {

  /// Replaces the `program` of `self` with the process-wide cache of the standard library.
  mutating func installCachedStandardLibrary() async throws {
    program = try await sharedStandardLibrary.value
  }

}

/// Returns a program containing the standard library, loaded from the archive cache or compiled
/// from its sources.
private func standardLibraryProgram() async throws -> Program {
  var d = try Driver(moduleCachePath: sharedModuleCachePath(), targetSpecification: .native())
  try await d.loadStandardLibrary()
  return d.program
}

/// Returns a stable folder for caching compilation artifacts, persistent across test runs
/// with the same executable.
private func sharedModuleCachePath() -> URL {
  let root = URL(filePath: #filePath)
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .deletingLastPathComponent()  
    .appending(components: ".build", "hylo-test-module-cache")
  let key = currentBinaryFingerprint()
  let path = root.appending(component: key)

  let m = FileManager.default
  try! m.createDirectory(at: path, withIntermediateDirectories: true)

  // Remove caches left over by other compiler builds.
  if let entries = try? m.contentsOfDirectory(at: root, includingPropertiesForKeys: nil) {
    for e in entries where e.lastPathComponent != key {
      try? m.removeItem(at: e)
    }
  }

  return path
}

/// Returns a fingerprint of the binary containing the compiler code under test.
///
/// The fingerprint captures the last modification time and file size.
private func currentBinaryFingerprint() -> String {
  let binary = currentBinary()
  var h = FNV1.native()
  h.combine(binary.path)
  if let a = try? FileManager.default.attributesOfItem(atPath: binary.path) {
    if let d = a[.modificationDate] as? Date {
      h.combine(d.timeIntervalSince1970.bitPattern)
    }
    if let s = a[.size] as? NSNumber {
      h.combine(s.uint64Value)
    }
  }
  return String(UInt(bitPattern: h.state), radix: 16)
}

/// Returns the path to the binary in which this code is running.
private func currentBinary() -> URL {
  Bundle(for: BundleToken.self).executableURL ??
    URL(fileURLWithPath: Swift.CommandLine.arguments[0])
}

/// A token used to locate the bundle containing the test.
private final class BundleToken {}
