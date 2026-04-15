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

  /// The locations of the executable search path (aka the `PATH` environment variable).
  public static func searchPathLocations() -> [String] {
    Host.environment["PATH", default: ""]
      .split(separator: Host.searchPathSeparator)
      .map(String.init)
  }

  /// The separator between individual locations in executable search path.
  public static let searchPathSeparator: Character = Host.operatingSystem == .windows ? ";" : ":"

  /// The suffix of native executables.
  public static let nativeExecutableSuffix = operatingSystem == .windows ? ".exe" : ""

  /// Returns the location of the native executable invoked as `name` using the search path or
  /// throws `ExecutableNotFound` if no executable could be found.
  ///
  /// `name` shall be supplied without the native executable suffix, e.g. without `.exe` on Windows.
  /// Only native executables are resolved. Script files such as `.cmd`, `.bat`, and `.ps1` are not.
  public static func findNativeExecutable(invokedAs name: String) throws -> URL {
   for base in searchPathLocations() {
     let p =  URL(fileURLWithPath: base).appendingPathComponent(name + nativeExecutableSuffix)
     if FileManager.default.isExecutableFile(atPath: p.path) { return p }
   }
   throw ExecutableNotFound(name: name)
  }

  /// Error thrown when an executable is not found on the PATH.
  public struct ExecutableNotFound: Error, CustomStringConvertible {
    
    /// Name of the executable without native executable suffix.
    public let name: String

    /// A description of the error.
    public var description: String {
      "Executable not found on PATH: \(name)"
    }

  }

}
