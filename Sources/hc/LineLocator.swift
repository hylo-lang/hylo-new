import ArgumentParser
import Foundation

/// The location of a specific line in a source file.
public struct LineLocator: Hashable, Sendable {

  /// The path of the source file containing the line.
  public let path: URL

  /// The 1-based index of the line in the source file.
  public let line: Int

  /// Creates an instance with the given properties.
  public init(path: URL, line: Int) {
    self.path = path.absoluteURL
    self.line = line
  }

}

extension LineLocator: ExpressibleByArgument {

  public init?(argument description: String) {
    guard let i = description.firstIndex(of: ":") else { return nil }
    guard let l = Int(description[description.index(after: i)...]) else { return nil }
    self = .init(path: URL(filePath: String(description[..<i])), line: l)
  }

}
