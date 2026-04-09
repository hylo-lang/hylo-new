import Foundation

/// The platform on which the compiler or interpreter is running.
public enum Host: Sendable {

  /// The name of the environment variable containing the executable search path.
  public static func pathEnvironmentVariableName() -> String {
    if Platform.hostOperatingSystem == .windows {
      ProcessInfo.processInfo.environment.keys
        .first(where: { $0.caseInsensitiveCompare("Path") == .orderedSame }) ?? "Path"
    } else {
      "PATH"
    }
  }

  /// The entries of the environment's executable search path.
  public static func pathEntries() -> [String] {
    (ProcessInfo.processInfo.environment[pathEnvironmentVariableName()]?
      .split(separator: Host.pathEnvironmentSeparator) ?? [])
      .map(String.init)
  }

  /// The separator between elements of the environment's executable search path.
  public static let pathEnvironmentSeparator: Character =
    Platform.hostOperatingSystem == .windows ? ";" : ":"
}

extension URL {
  /// Returns the URL with an executable suffix added if not already present.
  public func withHostExecutableSuffix() -> URL {
    #if os(Windows)
    return pathExtension == "exe" ? self : appendingPathExtension("exe")
    #else
    return self
    #endif
  }
}