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

  /// A subscriptable view of the environment variables, working around the lack of named subscripts.
  public struct Environment: Sendable {

    /// Looks up the value of the environment variable with the given `key`.
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

    /// Looks up the value of the environment variable with the given `key`.
    ///
    /// If the environment variable is not set, returns `default`.
    /// On Windows, the comparison is case-insensitive and takes linear time.
    public subscript(_ key: String, default d: String) -> String {
      self[key] ?? d
    }

  }

  /// A subscriptable view of the environment variables, using case-insensitive comparison on Windows.
  public static let environment = Environment()

  /// The elements of the environment's executable search path.
  public static func pathElements() -> [String] {
    Host.environment["PATH", default: ""]
      .split(separator: Host.pathEnvironmentSeparator)
      .map(String.init)
  }

  /// The separator between elements of the environment's executable search path.
  public static let pathEnvironmentSeparator: Character = Host.operatingSystem == .windows ? ";" : ":"

  /// The suffix of native executables.
  public static let nativeExecutableSuffix = operatingSystem == .windows ? ".exe" : ""

  /// Finds the native executable invoked as `name` in the environment's executable search path or throws `ExecutableNotFound` otherwise.
  ///
  /// On Windows, `name` shall be supplied without the `.exe` suffix.
  /// Only native executables are resolved. Script files such as `.cmd`, `.bat`, and `.ps1` are not.
  public static func findNativeExecutable(invokedAs name: String) throws -> URL {
    try pathElements().firstNonNil { base in
      let p = URL(fileURLWithPath: base).appendingPathComponent(name + nativeExecutableSuffix)
      return FileManager.default.isExecutableFile(atPath: p.path) ? p : nil
    }.unwrapOrThrow(ExecutableNotFound(name: name))
  }

  /// Error thrown when an executable is not found on the PATH.
  public struct ExecutableNotFound: Error, CustomStringConvertible {
    
    /// Name of the executable without native executable suffix.
    public let name: String

    /// Human-friendly error message.
    public var description: String {
      "Executable not found on PATH: \(name)"
    }

  }

}
