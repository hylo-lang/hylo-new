import FrontEnd
import Utilities

/// The identity of a monomorphic type.
struct MonomorphicTypeIdentity: Regular {

  /// The underlying type identity having no generic parameters or
  /// unification variables.
  public let underlying: AnyTypeIdentity

  /// Creates an instance wrapping `t` as `MonomorphicTypeIdentity`.
  ///
  /// - Precondition: `t` is monomorphic.
  public init(_ t: AnyTypeIdentity) {
    precondition(!t[.hasGenericParameter] && !t[.hasVariable])
    underlying = t
  }

}
