/// A sequence of values that can be tested sequentially on the RHS of a comparison operator.
///
/// Use this helper to write sequences of comparisons between one value and different RHS operands
/// concisely. For example:
///
///     assert(1 == anyOf(0, 1, 2))
///
/// Note that values stored `ComparisonRHS` are eagerly evaluated, meaning that this type helper
/// should be avoided in situations where the shortcut behavior of logical operators is desired.
public struct ComparisonRHS<T: Sequence> where T.Element: Equatable {

  /// The values in the sequence.
  public let values: T

  /// Returns `true` iff `lhs` is equal to one of the values in `rhs`.
  public static func == (lhs: T.Element, rhs: Self) -> Bool {
    rhs.values.contains(lhs)
  }

}

/// Returns the right-hand-side of an expression comparing an instance of `T` to `values`.
public func anyOf<T>(_ values: T...) -> ComparisonRHS<Array<T>> where T: Equatable {
  .init(values: values)
}
