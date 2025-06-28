/// The identity of a lexical scope.
public struct ScopeIdentity: Hashable {

  /// The internal representation of this identity.
  private var representation: AnySyntaxIdentity

  /// Creates an instance representing the scope formed by `file`.
  public init(file: SourceFile.ID) {
    self.representation = .scope(of: file)
  }

  /// Creates an instance representing the scope formed by `syntax`.
  public init<T: Scope>(node: T.ID) {
    self.representation = node.erased
  }

  /// Creates an instance representing the scope formed by `syntax`, assuming it is a scope.
  public init(uncheckedFrom node: AnySyntaxIdentity) {
    self.representation = node
  }

  /// The module containing this scope.
  public var module: Module.ID {
    representation.module
  }

  /// The source file containing this scope.
  public var file: SourceFile.ID {
    representation.file
  }

  /// `true` iff `self` represents a file.
  public var isFile: Bool {
    representation.offset == UInt32.max
  }

  /// The syntax tree that `self` represents, or `nil` if `self` represents a file.
  public var node: AnySyntaxIdentity? {
    isFile ? nil : .init(uncheckedFrom: representation)
  }

}

extension ScopeIdentity: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let n = node {
      return printer.show(n)
    } else {
      return printer.show(file)
    }
  }

}
