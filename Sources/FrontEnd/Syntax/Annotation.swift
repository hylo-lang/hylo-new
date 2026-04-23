import Archivist

/// An annotation on a syntax tree.
@Archivable
public struct Annotation: Hashable, Sendable {

  /// The value of an annotation argument.
  @Archivable
  public enum Argument: Hashable, Sendable, CustomStringConvertible {

    /// A character string.
    case string(String)

    /// A numeric value.
    case number(Int)

    /// The value of this argument if it is a character string.
    public var string: String? {
      if case .string(let s) = self { return s } else { return nil }
    }

    /// The value of this argument if it is a number.
    public var number: Int? {
      if case .number(let n) = self { return n } else { return nil }
    }

    /// A textual description of this argument.
    public var description: String {
      switch self {
      case .string(let s): return s
      case .number(let n): return n.description
      }
    }

  }

  /// The name of the annotation.
  public let identifier: Parsed<String>

  /// The arguments of the annotation.
  public let arguments: [Parsed<Argument>]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(identifier: Parsed<String>, arguments: [Parsed<Argument>], site: SourceSpan) {
    self.identifier = identifier
    self.arguments = arguments
    self.site = site
  }

}

extension Annotation: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if arguments.isEmpty {
      return "@\(identifier.value)"
    } else {
      let a = arguments.map(\.description).joined(separator: ", ")
      return "@\(identifier.value)(\(a))"
    }
  }

}
