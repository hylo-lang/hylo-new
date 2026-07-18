import FrontEnd
import Utilities

/// The identity of a concrete (non-generic) type.
struct ConcreteTypeIdentity: Regular {

  /// The underlying type identity, guaranteed to have no generic parameters.
  public let underlying: AnyTypeIdentity

  /// Creates an instance wrapping `t` as `ConcreteTypeIdentity`.
  ///
  /// - Precondition: `t` doesn't have any generic parameter.
  public init(_ t: AnyTypeIdentity) {
    underlying = t
  }

}
