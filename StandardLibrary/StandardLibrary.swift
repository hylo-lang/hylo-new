import Foundation

#if os(Windows)
  import WinSDK
#endif

/// The root folder of the standard library's sources.
///
/// This folder should be preferred during development. It is the driver's default unless its
/// sources are built with flag `USE_BUNDLED_STANDARD_LIBRARY` is set.
package let localStandardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()

/// The path to the bundled standard library's root folder.
///
/// This folder is intended to be used in distributable builds, in order to bundle the standard
/// library together with the executable. The driver will pick this folder over the local one if
/// its sources are compiled with the flag `USE_BUNDLED_STANDARD_LIBRARY` set.
public let bundledStandardLibrarySources = resourceDirectory

/// The bundled path of the source file containing the generated parts of the standard library.
package let generatedStandardLibrarySource = resourceDirectory.appending(
  component: "Generated.hylo", directoryHint: .notDirectory)

/// The file name of the standard library's C shim source file within the standard library root.
package let cShimSource = "shims.c"

#if os(Linux) || os(Windows)

  /// The directory holding this target's resources beside the executable.
  private let resourceDirectory: URL = {
    let d = executableURL().deletingLastPathComponent()
    // For SPM's native build system:
    let r = d.appending(component: "Hylo_StandardLibrary.resources", directoryHint: .isDirectory)
    // For Swift Build:
    return FileManager.default.fileExists(atPath: r.path)
      ? r : d.appending(component: "Hylo_StandardLibrary.bundle", directoryHint: .isDirectory)
  }()

  /// Returns the location of the running executable.
  private func executableURL() -> URL {
    #if os(Linux)
      return URL(fileURLWithPath: "/proc/self/exe").resolvingSymlinksInPath()
    #else
      let maxPathLength = 32_768
      var p = [WCHAR](repeating: 0, count: maxPathLength)
      let n = Int(GetModuleFileNameW(nil, &p, DWORD(maxPathLength)))
      precondition(n > 0, "cannot locate the running executable")
      return URL(fileURLWithPath: String(decoding: p[..<n], as: UTF16.self), isDirectory: false)
    #endif
  }

#else

  /// The directory holding this target's resources.
  private let resourceDirectory = Bundle.module.resourceURL!

#endif
