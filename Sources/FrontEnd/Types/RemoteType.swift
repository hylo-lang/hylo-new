import Archivist

/// The type of a projected value.
@Archivable
public struct RemoteType: TypeTree {

  /// The type of the projected value.
  public let projectee: AnyTypeIdentity

  /// The capabilities of the projection.
  public let access: AccessEffect

  /// Creates an instance with the given properties.
  public init(projectee: AnyTypeIdentity, access: AccessEffect) {
    self.projectee = projectee
    self.access = access
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    projectee.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> RemoteType {
    .init(projectee: store.map(projectee, transform), access: access)
  }

}

extension RemoteType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(access) \(printer.show(projectee))"
  }

}
