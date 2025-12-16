extension IRFunction {

  /// Combines instructions to form fewer instructions.
  internal mutating func foldRedundantInstructions() {
    for i in instructions() {
      switch tag(of: i) {
      case IRSubfield.self:
        fold(castUnchecked(i, to: IRSubfield.self))
      default:
        continue
      }
    }
  }

  /// Combines `i` with its user if there is only one.
  private mutating func fold(_ i: IRSubfield.ID) {
    let s = at(i)
    if let u = uses[.register(i.erased)]?.uniqueElement, let t = at(u.user) as? IRSubfield {
      let folded = IRSubfield(
        base: s.base, path: s.path.appending(contentsOf: t.path),
        typeOfSubfield: t.typeOfSubfield, anchor: t.anchor)
      replace(u.user, for: folded)
      remove(i.erased)
    }
  }

}
