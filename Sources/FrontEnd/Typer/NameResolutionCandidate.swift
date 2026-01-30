/// A candidate for resolving a name component.
internal struct NameResolutionCandidate {

  /// The way in which the resolved entity is referred to.
  internal let reference: DeclarationReference

  /// The type of the expression referring to the resolved entity.
  internal let type: AnyTypeIdentity

}

extension Program {

  /// Returns `true` iff `lhs` is preferred over `rhs` for overload resolution.
  internal func isPreferred(
    _ lhs: NameResolutionCandidate, other rhs: NameResolutionCandidate,
    in scopeOfUse: ScopeIdentity
  ) -> Bool {
    // No candidate is cheaper to elaborate?
    if lhs.reference.elaborationCost == rhs.reference.elaborationCost {
      switch (lhs.reference, rhs.reference) {
      case (.inherited(_, let a, _), .inherited(_, let b, _)):
        // Members declared in extension are preferred over members inherited by conformance. The
        // rationale is that the former may serve as implementations for the latter.
        if isExtensionMember(a) && !isExtensionMember(b) {
          return true
        } else {
          return compareLexicalDistances(a, b, relativeTo: scopeOfUse) == .ascending
        }

      default:
        return false
      }
    }

    // Return `true` iff `lhs` is cheaper to elaborate.
    else {
      return lhs.reference.elaborationCost < rhs.reference.elaborationCost
    }
  }

}
