import Utilities

/// When a function should be inlined.
public enum InliningPolicy {

  /// The function should never be inlined, even in optimized builds.
  case never

  /// The function should be inlined if possible, based on the optimizer's heuristics.
  ///
  /// Inlining occurs only in optimized builds and if the following conditions are met:
  ///
  /// * All symbols used in the function are inlineable from the perspective of the caller. In
  ///   other words, n
  ///
  case opportunistic

  /// The function must always be inlined, even in non-optimized builds.
  case always

  /// Creates an instance parsed from the given annotation.
  init?(_ a: Annotation) {
    if a.identifier.value != "inline" { return nil }

    // Is the annotation of the form `@inline`?
    if a.arguments.isEmpty {
      self = .always
    }

    // Is the annotation of the form `@inline(policy)`?
    else if let x = a.arguments.uniqueElement {
      switch x.value {
      case .string("always"):
        self = .always
      case .string("never"):
        self = .never
      default:
        return nil
      }
    }

    // The annotation is not valid.
    else { return nil }
  }

}
