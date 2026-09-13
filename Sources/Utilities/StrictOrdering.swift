/// The result type of a three-way comparison implementing a strict total order.
public enum StrictOrdering: CaseIterable, Hashable {

  /// The LHS is ordered before the RHS.
  case ascending

  /// The LHS is neither ordered before nor ordered after the RHS.
  case equal

  /// The LHS is ordered after the RHS.
  case descending

  /// Creates the comparison of `a` with `b`.
  public init<T: Comparable>(between a: T, and b: T) {
    self = (a < b) ? .ascending : ((b < a) ? .descending : .equal)
  }

  /// Returns `self` iff it is not `.equal`; otherwise, returns `other`.
  public func inequalElse(_ other: StrictOrdering) -> StrictOrdering {
    self == .equal ? other : self
  }

  /// Returns a function comparing instances of `T` at `p`.
  public static func comparing<T, U: Comparable>(_ p: KeyPath<T, U>) -> (T, T) -> StrictOrdering {
    { (a, b) in .init(between: a[keyPath: p], and: b[keyPath: p]) }
  }

}

/// The result type of a three-way comparison implementing a strict partial order.
public typealias StrictPartialOrdering = StrictOrdering?
