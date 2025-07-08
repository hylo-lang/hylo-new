/// Information identifying an argument of a function or subscript call.
internal enum ParameterBinding: Equatable {

  /// The argument is the n-th expression in the syntax of the call.
  case explicit(Int)

  /// The argument is elided; the callee receive the parameter's default value.
  case defaulted(ExpressionIdentity)

}

/// A collection of parameter bindings.
internal struct ParameterBindings {

  /// The value of each element in the collection.
  internal private(set) var elements: [ParameterBinding]

  /// `true` iff one element is defaulted.
  internal private(set) var hasDefaulted: Bool

  /// Creates an empty instance.
  internal init() {
    self.elements = []
    self.hasDefaulted = false
  }

  /// Adds `b` at the end of `self`.
  internal mutating func append(_ b: ParameterBinding) {
    elements.append(b)
    if case .defaulted = b { hasDefaulted = true }
  }

}
