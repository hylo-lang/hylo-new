import FrontEnd

extension Program {

  /// Returns the tag of `t`.
  internal func tag(_ t: AnyTypeIdentity) -> any TypeTree.Type {
    types.tag(of: t).value
  }

  /// Returns the type identified by `t`, cast to `U`.
  internal func type<U: TypeTree>(_ t: AnyTypeIdentity, as u: U.Type) -> U {
    types[types.cast(t, to: u)!]
  }

  /// Returns the underlying type of `t`, defined in `p`, after unwrapping
  /// type applications and aliases.
  internal mutating func underlyingType(_ t: AnyTypeIdentity) -> AnyTypeIdentity {
    var t = types.dealiased(t)
    while tag(t) == TypeApplication.self {
      t = type(t, as: TypeApplication.self).abstraction
    }
    return t
  }

}
