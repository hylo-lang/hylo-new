/// The platform on which the compiler or interpreter is running/targeting.
public enum Platform: Sendable {

  /// An operating system on which the compiler/interpreter/target program can run.
  public enum OperatingSystem: Codable, CustomStringConvertible, Sendable {

    case macOS, linux, windows

    /// String representation that matches the possible values used for conditional compilation.
    public var description: String {
      switch self {
      case .macOS: return "macOS"
      case .linux: return "Linux"
      case .windows: return "Windows"
      }
    }

  }

  /// An architecture on which the compiler/interpreter/target program can run.
  public enum Architecture: String, Codable, CustomStringConvertible, Sendable {

    case x86_64, arm64

    /// String representation.
    public var description: String {
      return rawValue
    }

  }

}
