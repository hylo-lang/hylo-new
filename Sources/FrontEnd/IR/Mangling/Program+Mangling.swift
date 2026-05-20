extension Program {

  /// Returns the mangled representation of `d`.
  public func mangled(_ d: DeclarationIdentity) -> String {
    mangled(d, applying: { (s, m, o) in m.mangled(decl: s, to: &o) })
  }

  /// Returns the mangled representation of `t`.
  public func mangled(_ t: AnyTypeIdentity) -> String {
    mangled(t, applying: { (s, m, o) in m.mangled(type: s, to: &o) })
  }

  /// Returns the mangled representation of `w`.
  public func mangled(_ w: IRWitnessTable) -> String {
    mangled(w, applying: { (s, m, o) in m.mangled(table: s, to: &o) })
  }

  /// Returns the mangled representation of `f` from module `m`.
  public func mangled(_ f: IRFunction.ID, of m: Module.ID) -> String {
    mangled(f, applying: { (s, me, o) in me.mangled(function: s, of: m, to: &o) })
  }

  /// Returns the mangled representation of `s`, applying `mangle` to build it.
  private func mangled<T>(
    _ s: T, applying mangle: (T, inout ManglingEncoding, inout ManglingContext) -> Void
  ) -> String {
    var m = ManglingEncoding(self)
    var o = ManglingContext(self)
    mangle(s, &m, &o)
    return o.output.assemblySanitized
  }

}
