import Foundation

/// The root folder of the standard library's sources. 
/// 
/// Use this for development time. Driver's default, unless USE_BUNDLED_STANDARD_LIBRARY option is set.
public let localStandardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Sources")

/// The path to the bundled standard library's root folder.
/// 
/// Use this in distributable builds. Set compiler flag USE_BUNDLED_STANDARD_LIBRARY to true for Driver to use this.
public let bundledStandardLibrarySources = Bundle.module.url(forResource: "Sources", withExtension: nil)!