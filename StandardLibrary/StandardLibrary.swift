import Foundation

/// The root folder of the standard library's sources. 
/// 
/// Use this for development time.
public let standardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Sources")

/// The path to the bundled standard library's root folder.
/// 
/// Use this in production.
public let bundledStandardLibrarySources = Bundle.module.url(forResource: "Sources", withExtension: nil)!