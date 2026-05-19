import Foundation

/// The root folder of the standard library's sources.
///
/// This folder should be preferred during development. It is the Driver's default unless the
/// flag `USE_BUNDLED_STANDARD_LIBRARY` is set.
public let localStandardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Minimal/Sources")

/// The path to the bundled standard library's root folder.
///
/// This folder is meant to be used in distributable builds in order to bundle the standard library
/// together with the executable. Set the flag `USE_BUNDLED_STANDARD_LIBRARY` to select it.
public let bundledStandardLibrarySources = Bundle.module.url(
  forResource: "Minimal/Sources", withExtension: nil)!

/// Identifies a standard library to use during compilation.
public struct StandardLibraryRoot {

  /// The root directory of this standard library variant.
  ///
  /// The root is expected to contain a `Sources/` subdirectory with Hylo sources and a
  /// `Shims/shim.c` that can expose functionality from the C standard library.
  public let root: URL

  /// Creates an instance representing the standard library at `root`.
  private init(root: URL) {
    self.root = root
  }

  /// The path to the bundled full standard library's root folder.
  ///
  /// This folder is meant to be used in distributable builds in order to bundle the standard library
  /// together with the executable. Set the flag `USE_BUNDLED_STANDARD_LIBRARY` to select it.
  public static func bundledFull() -> StandardLibraryRoot {
    StandardLibraryRoot(
      root: Bundle.module.resourceURL!.appendingPathComponent("Full"))
  }

  /// The root folder of the full standard library's sources.
  ///
  /// This folder should be preferred during development. It is the Driver's default unless the
  /// flag `USE_BUNDLED_STANDARD_LIBRARY` is set.
  public static func localFull() -> StandardLibraryRoot {
    StandardLibraryRoot(
      root: URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent()
        .appendingPathComponent("Full"))
  }

  /// The local or bundled full standard library root.
  ///
  /// Set the flag `USE_BUNDLED_STANDARD_LIBRARY` to use the bundled version.
  public static func full() -> StandardLibraryRoot {
    #if USE_BUNDLED_STANDARD_LIBRARY
      return bundledFull()
    #else
      return localFull()
    #endif
  }

  /// The root folder of the minimal standard library's sources.
  ///
  /// This is meant to be used for testing.
  public static func localMinimal() -> StandardLibraryRoot {
    StandardLibraryRoot(
      root: URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent()
        .appendingPathComponent("Minimal"))
  }

  /// A standard library rooted at `root`, containing `Sources` and `Shims` directories.
  public static func custom(_ root: URL) -> StandardLibraryRoot {
    StandardLibraryRoot(root: root)
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
