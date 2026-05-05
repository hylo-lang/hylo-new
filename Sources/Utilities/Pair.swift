/// A pair of elements.
public struct Pair<T, U> {

  /// The first element of the pair.
  public var first: T

  /// The second element of the pair.
  public var second: U

  /// Creates an instance with the given elements.
  public init(_ first: T, _ second: U) {
    self.first = first
    self.second = second
  }

}

extension Pair: Equatable where T: Equatable, U: Equatable {}

extension Pair: Hashable where T: Hashable, U: Hashable {}

extension Pair: Sendable where T: Sendable, U: Sendable {}
