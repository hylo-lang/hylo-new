import Archivist

/// A parameter of a callable abstraction.
@Archivable
public struct Parameter: Hashable, Sendable {

  /// The label of the parameter.
  public let label: String?

  /// The capabilities of the parameter on its argument.
  public let access: AccessEffect

  /// The type of the values that can be passed to the parameter.
  public let type: AnyTypeIdentity

  /// The default value of the parameter, if any.
  public let defaultValue: ExpressionIdentity?

  /// Creates an instance with the given properties.
  public init(
    label: String? = nil,
    access: AccessEffect,
    type: AnyTypeIdentity,
    defaultValue: ExpressionIdentity? = nil
  ) {
    self.label = label
    self.access = access
    self.type = type
    self.defaultValue = defaultValue
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Parameter {
    let t = store.map(type, transform)
    return .init(label: label, access: access, type: t, defaultValue: defaultValue)
  }

}

extension Parameter: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let l = label {
      return "\(l): \(access) \(printer.show(type))"
    } else {
      return "\(access) \(printer.show(type))"
    }
  }

}
