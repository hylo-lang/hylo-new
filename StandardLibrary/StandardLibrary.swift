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

  /// The directory holding this target's resources, which SwiftPM, like the distributable bundles,
  /// puts next to the executables.
  private let resourceDirectory = executableURL().deletingLastPathComponent().appending(
    component: "Hylo_StandardLibrary.resources", directoryHint: .isDirectory)

  /// Returns the location of the running executable (on Linux, with symbolic links resolved).
  private func executableURL() -> URL {
    #if os(Linux)
      let p = try! FileManager.default.destinationOfSymbolicLink(atPath: "/proc/self/exe")
      return URL(fileURLWithPath: p, isDirectory: false)
    #else
      var buffer = [WCHAR](repeating: 0, count: Int(MAX_PATH))
      while true {
        let n = Int(GetModuleFileNameW(nil, &buffer, DWORD(buffer.count)))
        precondition(n != 0, "cannot locate the running executable")
        if n < buffer.count {
          return URL(
            fileURLWithPath: String(decoding: buffer[..<n], as: UTF16.self), isDirectory: false)
        }
        // The path was truncated.
        buffer = [WCHAR](repeating: 0, count: buffer.count * 2)
      }
    #endif
  }

#else

  /// The directory holding this target's resources.
  private let resourceDirectory = Bundle.module.resourceURL!

#endif
