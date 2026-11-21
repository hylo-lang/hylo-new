/// The result type of a three-way comparison implementing a strict total order.
public enum StrictOrdering: CaseIterable, Hashable {

  /// The LHS is ordered before the RHS.
  case ascending

  /// The LHS is neither ordered before nor ordered after the RHS.
  case equal

  /// The LHS is ordered after the RHS.
  case descending

  /// Creates a description of the direction of change from `a` to `b`.
  public init<T: Comparable>(from a: T, to b: T) {
    self = (a < b) ? .ascending : ((b < a) ? .descending : .equal)
  }

  /// Returns a function describing the direction of change from `f(x)` to `f(y)` for `T` instances
  /// `x` and `y.`
  public static func descriptor<T, U: Comparable>(ofChangeIn f: @escaping (T)->U) -> (T, T) -> StrictOrdering {
    { (a, b) in .init(from: f(a), to: f(b)) }
  }

}
