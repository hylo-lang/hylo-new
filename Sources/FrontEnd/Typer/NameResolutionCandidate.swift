import Utilities

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
    _ lhs: NameResolutionCandidate, over rhs: NameResolutionCandidate,
    in scopeOfUse: ScopeIdentity
  ) -> ThreeWayComparisonResult {
    let d: ThreeWayComparisonResult = switch (lhs.reference, rhs.reference) {
    case (.inherited(_, let a, _), .inherited(_, let b, _)):
      // Members declared in extension are preferred over members inherited by conformance. The
      // rationale is that the former may serve as implementations for the latter.
      if isExtensionMember(a) && !isExtensionMember(b) {
        .ascending
      } else {
        compareLexicalDistances(a, b, relativeTo: scopeOfUse)
      }

    default:
      if let a = lhs.reference.target, let b = rhs.reference.target {
        compareLexicalDistances(a, b, relativeTo: scopeOfUse)
      } else {
        .equivalent
      }
    }

    return d != .equivalent ? d
      : threeWayComparison(of: \.reference.elaborationCost)(lhs, rhs)
  }

}
