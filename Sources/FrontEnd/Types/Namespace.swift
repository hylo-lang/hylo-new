import Archivist

/// The type of a namespace.
@Archivable
public struct Namespace: TypeTree {

  /// The identifier of a namespace.
  @Archivable
  public enum Identifier: Hashable, Sendable {

    /// The built-in module
    case builtin

    /// A module.
    case module(Module.ID)

  }

  /// The unique identifier of the namespace.
  public let identifier: Identifier

  /// Creates an instance with the given identifier.
  public init(identifier: Identifier) {
    self.identifier = identifier
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension Namespace: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(identifier)
  }

}

extension Namespace.Identifier: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .builtin:
      return "Builtin"
    case .module(let m):
      return printer.program[m].name.rawValue
    }
  }

}
