import Archivist
import Utilities

/// An operator notation.
@Archivable
public enum OperatorNotation: UInt8, Sendable {

  /// No notation.
  case none = 0

  /// The infix notation.
  case infix = 1

  /// The prefix notation.
  case prefix = 2

  /// The postfix notation.
  case postfix = 3

}

/// The argument labels of a name.
@Archivable
public struct ArgumentLabels: Sendable {

  /// The value of each label.
  public let values: [String?]

  /// Creates an instance with `values`.
  public init<S: Sequence<String?>>(_ values: S) {
    self.values = .init(values)
  }

}

extension ArgumentLabels: Hashable {}

extension ArgumentLabels: RandomAccessCollection {

  public typealias Element = String?

  public typealias Index = Array<String?>.Index

  public var startIndex: Index { values.startIndex }

  public var endIndex: Index { values.endIndex }

  public func index(after i: Index) -> Index { values.index(after: i) }

  public func index(before i: Index) -> Index { values.index(before: i) }

  public subscript(i: Index) -> Element { values[i] }

}

extension ArgumentLabels: ExpressibleByArrayLiteral {

  public init(arrayLiteral elements: String?...) {
    self.init(elements)
  }

}

extension ArgumentLabels: CustomStringConvertible {

  public var description: String {
    values.map({ (label) in "\(label ?? "_"):" }).joined()
  }

}

/// An unqualified name denoting an entity.
@Archivable
public struct Name: Hashable, Sendable {

  /// The identifier of the referred entity.
  public let identifier: String

  /// The argument labels of the referred entity, given that it is a function.
  public let labels: ArgumentLabels

  /// The operator notation of the referred entity, given that it is an operator.
  public let notation: OperatorNotation

  /// The method introducer of the referred entity, given that it is a method implementation.
  ///
  /// The introducer, if any, is incorporated during parsing, after the original `Name` is created.
  public let introducer: AccessEffect?

  /// Creates an instance with the given properties.
  public init(
    identifier: String,
    labels: ArgumentLabels = [],
    notation: OperatorNotation = .none,
    introducer: AccessEffect? = nil
  ) {
    self.identifier = identifier
    self.labels = labels
    self.notation = notation
    self.introducer = introducer
  }

  /// `true` iff `self` has no argument labels, operator notation, or introducer.
  public var isSimple: Bool {
    labels.isEmpty && (notation == .none) && (introducer == .none)
  }

  /// Returns `true` iff `self` identifies an operator with the given notation.
  public func isOperator(_ n: OperatorNotation) -> Bool {
    notation == n
  }

  /// Returns `true` iff `scrutinee` can be used to refer to a declaration named after `pattern`.
  public static func ~= (pattern: Name, scrutinee: Name) -> Bool {
    pattern.identifier == scrutinee.identifier
      && (pattern.labels.isEmpty || pattern.labels.elementsEqual(scrutinee.labels))
      && (pattern.notation == .none || pattern.notation == scrutinee.notation)
      && (pattern.introducer == .none || pattern.notation == scrutinee.notation)
  }

}

extension Name: ExpressibleByStringLiteral {

  public init(stringLiteral value: StringLiteralType) {
    assert(!value.contains("."))
    self.init(identifier: value)
  }

}

extension Name: CustomStringConvertible {

  public var description: String {
    if notation != .none {
      return "\(notation)\(identifier)"
    } else if labels.isEmpty {
      let introducer = introducer.map({ (i) in "@\(i)" }) ?? ""
      return identifier + introducer
    } else {
      let introducer = introducer.map({ (i) in "@\(i)" }) ?? ""
      return "\(identifier)(\(labels))" + introducer
    }
  }

}
