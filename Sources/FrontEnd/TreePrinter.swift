import Utilities

public protocol Showable {

  /// Returns a textual representation of `self` using `printer`.
  func show(using printer: inout TreePrinter) -> String

}

/// State for printing the textual representations of syntax and type trees.
public struct TreePrinter {

  /// Settings used for printing syntax and type trees.
  public struct Configuration {

    /// `true` if types shouls be printed with a verbose representation.
    public let useVerboseTypes: Bool

    /// Creates an instance with the given properties.
    public init(useVerboseTypes: Bool) {
      self.useVerboseTypes = useVerboseTypes
    }

    /// The default configuration.
    public static var `default`: Configuration {
      .init(useVerboseTypes: false)
    }

  }

  /// The configuration of the printer.
  public let configuration: Configuration

  /// A reference to the program containing the items to show.
  public let program: Program

  /// A map from identifier to keys items having that identifier.
  private var identifiers: [String: [AnyHashable]]

  /// Creates an instance from printing contents in `program` using the given configuration.
  public init(program: Program, configuration: Configuration = .default) {
    self.configuration = configuration
    self.program = program
    self.identifiers = [:]
  }

  /// Returns `message` with placeholders replaced by their corresponding values in `arguments`.
  public mutating func format(_ message: String, _ arguments: [Any]) -> String {
    program.format(message, arguments)
  }

  /// Returns a textual representation of `item` using the given configuration.
  public mutating func show<T: Showable>(_ item: T) -> String {
    item.show(using: &self)
  }

  /// Returns a textual representation of `items`, separating each element by `separator`.
  public mutating func show<T: Sequence>(
    _ items: T, separatedBy separator: String = ", "
  ) -> String where T.Element: Showable {
    items.map({ (n) in show(n) }).joined(separator: separator)
  }

  /// Returns a textual representation of the adjunct conformance.
  public mutating func showAdjunct(_ conformances: [ConformanceDeclaration.ID]) -> String {
    var result = ""
    var first = true
    for c in conformances {
      if first { first = false } else { result.append(" & ") }
      let s = program.seenAsConformanceTypeExpression(program[c].witness)!
      result.append("\(show(s.concept))")
      if !s.arguments.isEmpty {
        result.append("<\(show(s.arguments))>")
      }
    }
    return result
  }

  /// Returns `s` optionally suffixed by a discriminator in case this method has been already been
  /// called with `s` and a different `key`.
  public mutating func uniquized(_ s: String, for key: AnyHashable) -> String {
    let i = modify(&identifiers[s, default: []]) { (ts) in
      if let i = ts.firstIndex(of: key) {
        return i
      } else {
        defer { ts.append(key) }
        return ts.count
      }
    }
    return (i == 0) ? s : s + superscript(i)
  }

  /// Returns `n` as a superscript.
  private func superscript(_ n: Int) -> String {
    if n == 0 { return Self.digitToSuperscript[0] }

    var a = ""
    var v = n
    while v != 0 {
      let i = v % 10
      v /= 10
      a.append(Self.digitToSuperscript[i])
    }
    return a
  }

  /// A table from digit to its representation as a superscript.
  private static let digitToSuperscript = [
    "\u{2070}",
    "\u{00b9}",
    "\u{00b2}",
    "\u{00b3}",
    "\u{2074}",
    "\u{2075}",
    "\u{2076}",
    "\u{2077}",
    "\u{2078}",
    "\u{2079}",
  ]

}
