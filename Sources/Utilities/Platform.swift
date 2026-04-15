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

}
