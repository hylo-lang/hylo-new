import FrontEnd
import Utilities

/// The identity of a concrete type.
public struct MonomorphicTypeIdentity: Hashable, Sendable {

  /// The underlying type identity having no generic parameters or
  /// unification variables.
  public let underlying: AnyTypeIdentity

  /// Creates an instance wrapping `t` as `MonomorphicTypeIdentity`.
  ///
  /// - Precondition: `t` is monomorphic and not a type variable.
  public init(_ t: AnyTypeIdentity) {
    precondition(!t[.hasGenericParameter] && !t[.hasVariable])
    underlying = t
  }

}

extension MonomorphicTypeIdentity {

  /// Creates an instance with the given bit representation.
  public init(bits: UInt64) {
    self = .init(AnyTypeIdentity(bits: bits))
  }

  /// The bit representation of `self`.
  public var bits: UInt64 { self.underlying.bits }

}
