import Foundation

/// The platform on which the compiler or interpreter is running.
public enum Host: Sendable {

  #if os(macOS)
    /// The host operating system.
    public static let operatingSystem: Platform.OperatingSystem = .macOS
  #elseif os(Linux)
    /// The host operating system.
    public static let operatingSystem: Platform.OperatingSystem = .linux
  #elseif os(Windows)
    /// The host operating system.
    public static let operatingSystem: Platform.OperatingSystem = .windows
  #else
    #error("Unsupported host operating system")
  #endif

  #if arch(x86_64)
    /// The host architecture.
    public static let architecture: Platform.Architecture = .x86_64
  #elseif arch(arm64)
    /// The host architecture.
    public static let architecture: Platform.Architecture = .arm64
  #else
    #error("Unsupported host architecture")
  #endif

  /// A view of the environment variables.
  public struct Environment: Sendable {

    /// Returns the value of the environment variable named `key`, if any.
    ///
    /// On Windows, the comparison is case-insensitive and takes linear time.
    public subscript(_ key: String) -> String? {
      #if os(Windows)
        ProcessInfo.processInfo.environment
          .first(where: { $0.key.caseInsensitiveCompare(key) == .orderedSame })?.value
      #else
        ProcessInfo.processInfo.environment[key]
      #endif
    }

    /// Returns the value of the environment variable named `key` or `d` if it's not set.
    ///
    /// On Windows, the comparison is case-insensitive and takes linear time.
    public subscript(_ key: String, default d: String) -> String {
      self[key] ?? d
    }

  }

  /// The environment variables of the current process.
  public static let environment = Environment()

  /// The suffix of binary executables.
  public static let binaryExecutableSuffix = operatingSystem == .windows ? ".exe" : ""

}
