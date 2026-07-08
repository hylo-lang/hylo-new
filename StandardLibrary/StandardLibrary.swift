import Foundation

/// The root folder of the standard library's sources. 
/// 
/// This folder should be preferred during development. It is the driver's default unless its
/// sources are built with flag `USE_BUNDLED_STANDARD_LIBRARY` is set.
public let localStandardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Sources")

/// The path to the bundled standard library's root folder.
/// 
/// This folder is intended to be used in distributable builds, in order to bundle the standard
/// library together with the executable. The driver will pick this folder over the local one if
/// its sources are compiled with the flag `USE_BUNDLED_STANDARD_LIBRARY` set.
public let bundledStandardLibrarySources = Bundle.module.url(
  forResource: "Sources", withExtension: nil)!

/// The file name of the standard library's C shim source file within the standard library root.
package let cShimSource = "shims.c"
