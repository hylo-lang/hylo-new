/// The result of a three-way comparison implementing a strict total order.
public enum ThreeWayComparisonResult: CaseIterable, Hashable {

  /// The LHS is ordered before the RHS.
  case ascending

  /// The LHS is neither ordered before nor ordered after the RHS.
  case equal

  /// The LHS is ordered after the RHS.
  case descending

}

infix operator <=>: ComparisonPrecedence

extension Comparable {

  /// Returns the direction of change from `a` to `b`.
  public static func <=> (a: Self, b: Self) -> ThreeWayComparisonResult {
    a < b ? .ascending : b < a ? .descending : .equal
  }

}

public typealias ThreeWayComparison<T> = (T, T) -> ThreeWayComparisonResult

/// Returns a function ordering `T` instances `x` and `y` per `f(x) <=> f(y)`.
public func threeWayComparison<T, U: Comparable>(of f: @escaping (T)->U) -> ThreeWayComparison<T> {
  { (x, y) in f(x) <=> f(y) }
}
