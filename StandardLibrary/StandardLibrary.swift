import Foundation

/// The root folder of the standard library's sources. 
/// 
/// This folder should be preferred during development. It is the Driver's default unless the
/// flag `USE_BUNDLED_STANDARD_LIBRARY` is set.
public let localStandardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Sources")

/// The path to the bundled standard library's root folder.
/// 
/// This folder is meant to be used in distributable builds in order to bundle the standard library
/// together with the executable. Set the flag `USE_BUNDLED_STANDARD_LIBRARY` to select it.
public let bundledStandardLibrarySources = Bundle.module.url(forResource: "Sources", withExtension: nil)!