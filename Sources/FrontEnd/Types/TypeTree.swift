import Archivist

/// An (abstract syntax) representation of some Hylo type.
///
/// `TypeTree`s are analogous to textual type expressions in Hylo syntax. Thus, distinct `TypeTree`
/// values can represent the same semantic type value.
///
/// In fact, these syntactic types are all we have, beceause the computation of a single canonical
/// type value for semantically-equivalent forms [is undecidable](https://arxiv.org/pdf/2502.20546).
public protocol TypeTree: Hashable, Showable, Archivable, Sendable {

  /// Properties about `self` and its children, which are types in `program`.
  var properties: TypeProperties { get }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Self

}

extension TypeTree {

  /// The identity of an instance of `Self`.
  public typealias ID = ConcreteTypeIdentity<Self>

  /// `true` iff `self` is a type variable.
  public var isVariable: Bool {
    self is TypeVariable
  }

  /// Returns `true` iff `self` has the same tree representation as `other`.
  public func equals(_ other: any TypeTree) -> Bool {
    self == other as? Self
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Self {
    self
  }

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}
