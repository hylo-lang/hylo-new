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
      let p = s.part.appending(contentsOf: t.part)
      let x = IRSubfield(whole: s.whole, part: p, partType: t.partType, anchor: t.anchor)
      replace(u.user, with: x)
      remove(i.erased)
    }
  }

}
