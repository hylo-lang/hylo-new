/// The platform on which the compiler or interpreter is running/targeting.
public enum Platform: Sendable {

  /// An operating system on which the Hylo compiler toolchain can run as a host.
  public enum OperatingSystem: String, Codable, CustomStringConvertible, Sendable {

    case macOS = "macOS"

    case linux = "Linux"

    case windows = "Windows"

    /// A description of `self`.
    public var description: String {
      rawValue
    }

  }

  /// An architecture on which the Hylo compiler toolchain can run as a host.
  public enum Architecture: String, Codable, CustomStringConvertible, Sendable {

    case x86_64, arm64

    /// String representation.
    public var description: String {
      return rawValue
    }

  }


  #if os(macOS)
    /// The host operating system.
    public static let hostOperatingSystem: OperatingSystem = .macOS
  #elseif os(Linux)
    /// The host operating system.
    public static let hostOperatingSystem: OperatingSystem = .linux
  #elseif os(Windows)
    /// The host operating system.
    public static let hostOperatingSystem: OperatingSystem = .windows
  #endif

  #if arch(i386)
    /// The host architecture.
    public static let hostArchitecture: Architecture = .i386
  #elseif arch(x86_64)
    /// The host architecture.
    public static let hostArchitecture: Architecture = .x86_64
  #elseif arch(arm)
    /// The host architecture.
    public static let hostArchitecture: Architecture = .arm
  #elseif arch(arm64)
    /// The host architecture.
    public static let hostArchitecture: Architecture = .arm64
  #endif

}
