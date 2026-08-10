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
  internal func underlyingType(_ t: AnyTypeIdentity) -> AnyTypeIdentity {
    let u = tag(t)
    if u == TypeApplication.self {
      let a = type(t, as: TypeApplication.self)
      return underlyingType(a.abstraction)
    } else if u == TypeAlias.self {
      let a = type(t, as: TypeAlias.self)
      return underlyingType(a.aliasee)
    } else {
      return t
    }
  }

}
