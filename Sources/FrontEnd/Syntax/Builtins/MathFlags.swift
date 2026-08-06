import Archivist

/// A set of customizations to the behavior of floating point operations.
///
/// The meaning of each customization is given by the LLVM option of the same name. The raw value
/// of each flag matches its position in `LLVMFastMathFlags` (see llvm-c/Core.h).
public struct MathFlags: OptionSet, Hashable, Sendable {

  public typealias RawValue = UInt8

  public let rawValue: UInt8

  public init(rawValue: UInt8) {
    self.rawValue = rawValue
  }

  public static let reassoc = MathFlags(rawValue: 1 << 0)

  public static let nnan = MathFlags(rawValue: 1 << 1)

  public static let ninf = MathFlags(rawValue: 1 << 2)

  public static let nsz = MathFlags(rawValue: 1 << 3)

  public static let arcp = MathFlags(rawValue: 1 << 4)

  public static let contract = MathFlags(rawValue: 1 << 5)

  public static let afn = MathFlags(rawValue: 1 << 6)

  /// All flags; implies every other customization, as in LLVM.
  public static let fast: MathFlags = [.reassoc, .nnan, .ninf, .nsz, .arcp, .contract, .afn]

}

extension MathFlags: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    self = try archive.readOrThrow(rawValueOf: MathFlags.self, in: &context)
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(rawValueOf: self, in: &context)
  }

}

extension MathFlags: LosslessStringConvertible {

  /// The instance whose only element is named `description`, or `nil` if no such flag exists.
  public init?(_ description: String) {
    self.init(description[...])
  }

  /// The instance whose only element is named `description`, or `nil` if no such flag exists.
  public init?(_ description: Substring) {
    switch description {
    case "afn":
      self = .afn
    case "arcp":
      self = .arcp
    case "contract":
      self = .contract
    case "fast":
      self = .fast
    case "ninf":
      self = .ninf
    case "nnan":
      self = .nnan
    case "nsz":
      self = .nsz
    case "reassoc":
      self = .reassoc
    default:
      return nil
    }
  }

  /// The contribution this set of flags makes to name of a function in the `Builtin` module.
  public var description: String {
    if self.contains(.fast) { return "fast" }
    var result: [String] = []
    if self.contains(.afn) { result.append("afn") }
    if self.contains(.arcp) { result.append("arcp") }
    if self.contains(.contract) { result.append("contract") }
    if self.contains(.ninf) { result.append("ninf") }
    if self.contains(.nnan) { result.append("nnan") }
    if self.contains(.nsz) { result.append("nsz") }
    if self.contains(.reassoc) { result.append("reassoc") }
    return result.joined(separator: "_")
  }

}
