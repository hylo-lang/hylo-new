import Utilities

/// The factors that influence conditional compilation.
public struct ConditionalCompilationFactors: Sendable {

  /// The target operating system.
  public let operatingSystem: Platform.OperatingSystem

  /// The target architecture.
  public let architecture: Platform.Architecture

  /// The version of the compiler.
  public let compilerVersion: SemanticVersion

  /// The version of the Hylo language recognized by the compiler.
  public let hyloVersion: SemanticVersion

  /// `true` if the standard library exposes only non-OS-dependent parts.
  public let freestanding: Bool

  public init(
    operatingSystem os: Platform.OperatingSystem = Platform.hostOperatingSystem,
    architecture a: Platform.Architecture = Platform.hostArchitecture,
    compilerVersion cv: SemanticVersion = SemanticVersion(major: 0, minor: 1, patch: 0),
    hyloVersion hv: SemanticVersion = SemanticVersion(major: 0, minor: 1, patch: 0),
    freestanding f: Bool = false
  ) {
    self.operatingSystem = os
    self.architecture = a
    self.compilerVersion = cv
    self.hyloVersion = hv
    self.freestanding = f
  }

}

extension ConditionalCompilationFactors: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "operatingSystem=\(operatingSystem), "
      + "architecture=\(architecture), "
      + "compilerVersion=\(compilerVersion), "
      + "hyloVersion=\(hyloVersion), "
      + "freestanding=\(freestanding)"
  }

}
