extension IRFunction {

  internal mutating func depolymorphize() {
    // Nothing to do if the function is generic.
    if !termParameters.isEmpty { return }

    for i in instructions() {
      switch tag(of: i) {
      case IRTypeApply.self:
        depolymorphize(castUnchecked(i, to: IRTypeApply.self))
      default:
        continue
      }
    }
  }

  /// Combines `i` with its user if there is only one.
  private mutating func depolymorphize(_ i: IRTypeApply.ID) {
    let s = at(i)
    _ = s
  }

}
