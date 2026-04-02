import Foundation

/// The root folder of the standard library's sources.
///
/// This folder should be preferred during development. It is the Driver's default unless the
/// flag `USE_BUNDLED_STANDARD_LIBRARY` is set.
public let localStandardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Full/Sources")

/// The path to the bundled standard library's root folder.
///
/// This folder is meant to be used in distributable builds in order to bundle the standard library
/// together with the executable. Set the flag `USE_BUNDLED_STANDARD_LIBRARY` to select it.
public let bundledStandardLibrarySources = Bundle.module.url(forResource: "Full/Sources", withExtension: nil)!


/// Identifies a standard library to use during compilation.
public struct StandardLibraryDefinition {

  /// The root directory of this standard library variant.
  ///
  /// The root is expected to contain a `Sources/` subdirectory with Hylo sources and a
  /// `shim.c` file with platform-specific C shims.
  public let root: URL

  private init(root: URL) {
    self.root = root
  }

  /// The full standard library bundled with the compiler.
  public static func full() -> StandardLibraryDefinition {
    StandardLibraryDefinition(
      root: Bundle.module.resourceURL!.appendingPathComponent("Full"))
  }

  /// A minimal standard library used for testing.
  public static func minimal() -> StandardLibraryDefinition {
    StandardLibraryDefinition(
      root: Bundle.module.resourceURL!.appendingPathComponent("Minimal"))
  }

  /// A standard library rooted at `root`.
  public static func custom(_ root: URL) -> StandardLibraryDefinition {
    StandardLibraryDefinition(root: root)
  }

  /// The URL to the directory containing Hylo source files for this stdlib.
  public var sourceRoot: URL {
    root.appendingPathComponent("Sources")
  }

  /// The URL to the C shim source file for this stdlib.
  ///
  /// By convention the shim lives at `Shims/shim.c` relative to the stdlib root, which keeps C
  /// files inside a directory resource and avoids SPM's mixed-language-target restriction.
  public var shim: URL {
    root.appendingPathComponent("Shims/shim.c")
  }

}
