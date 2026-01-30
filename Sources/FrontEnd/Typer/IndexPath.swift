import Utilities

/// A list of indices representing the path to a specific location in a tree.
///
/// A path is relative to a tree that is represented as a nested arrays. Given a path `p`, `p[i]`
/// denotes the index of a child in the tree identified by `p[..<i]`. An empty path denotes the
/// root of the tree.
public struct IndexPath: Hashable, Sendable {

  /// The internal representation of an index path.
  private enum Representation: Hashable, Sendable {

    /// An inline representation of at most 12 components.
    case compact(UInt16, UInt16, UInt16, count: UInt8)

    /// An out-of-line representation.
    case regular(ContiguousArray<Int>)

  }

  /// The internal representation of this path.
  private var representation: Representation

  /// Creates an instance with the given representation.
  private init(_ representation: Representation) {
    self.representation = representation
  }

  /// Creates an empty path.
  public init() {
    self.representation = .compact(0, 0, 0, count: 0)
  }

  /// `true` iff `self` is empty.
  public var isEmpty: Bool {
    count == 0
  }

  /// The number of components in this path.
  public var count: Int {
    switch representation {
    case .compact(_, _, _, let count):
      return Int(count)
    case .regular(let xs):
      return xs.count
    }
  }

  /// Appends `i` at the end of this path.
  public mutating func append(_ i: Int) {
    self = appending(i)
  }

  /// Returns `self` with `i` appended.
  public func appending(_ i: Int) -> IndexPath {
    if UInt(bitPattern: i) > 15 {
      return .init(.regular(ContiguousArray(self) + [i]))
    }

    switch representation {
    case .compact(let x0, let x1, let x2, let count):
      let j = (count & 3) << 2

      switch count >> 2 {
      case 0: return .init(.compact(x0 | UInt16(i << j), x1, x2, count: count + 1))
      case 1: return .init(.compact(x0, x1 | UInt16(i << j), x2, count: count + 1))
      case 2: return .init(.compact(x0, x1, x2 | UInt16(i << j), count: count + 1))
      default:
        var xs = ContiguousArray<Int>()
        xs.reserveCapacity(13)
        xs.append(contentsOf: (0 ..< 4).map({ (j) in Int(x0) >> (j << 2) & 0xf }))
        xs.append(contentsOf: (0 ..< 4).map({ (j) in Int(x1) >> (j << 2) & 0xf }))
        xs.append(contentsOf: (0 ..< 4).map({ (j) in Int(x2) >> (j << 2) & 0xf }))
        xs.append(i)
        return .init(.regular(xs))
      }

    case .regular(var xs):
      xs.append(i)
      return .init(.regular(xs))
    }
  }

  /// Appends the contents of `other` at the end of this path.
  public mutating func append<S: Sequence<Int>>(contentsOf other: S) {
    self = appending(contentsOf: other)
  }

  /// Returns `self` concatenated with `other`.
  public func appending<S: Sequence<Int>>(contentsOf other: S) -> IndexPath {
    var clone = self
    var it = other.makeIterator()

    while let i = it.next() {
      switch clone.representation {
      case .compact:
        clone = clone.appending(i)
      case .regular(var xs):
        xs.append(i)
        xs.append(contentsOf: AnySequence({ it }))
        return .init(.regular(xs))
      }
    }

    return clone
  }

  /// Returns a path identifying the root of an object.
  public static var root: IndexPath { .init() }

}

extension IndexPath: ExpressibleByArrayLiteral {

  public init(arrayLiteral components: Int...) {
    // Can we fit the components in a compact representation?
    if components.count <= 12 {
      var xs: UInt64 = 0
      var j = 0

      for i in components {
        if UInt(bitPattern: i) <= 15 {
          xs = xs | UInt64(i) << j
          j += 4
        } else {
          self.representation = .regular(ContiguousArray(components))
          return
        }
      }

      self.representation = .compact(
        UInt16(truncatingIfNeeded: xs),
        UInt16(truncatingIfNeeded: xs >> 16),
        UInt16(truncatingIfNeeded: xs >> 32),
        count: UInt8(components.count))
    }

    // Default to the regular representation.
    else {
      self.representation = .regular(ContiguousArray(components))
    }
  }

}

extension IndexPath: RandomAccessCollection {

  public typealias Index = Int

  public typealias Element = Int

  public var startIndex: Int {
    0
  }

  public var endIndex: Int {
    count
  }

  public func index(after p: Int) -> Int {
    p + 1
  }

  public func index(before p: Int) -> Int {
    p - 1
  }

  public subscript(p: Int) -> Int {
    switch representation {
    case .compact(let x0, let x1, let x2, let count):
      precondition(UInt(bitPattern: p) < count, "index of out range")
      let j = (p & 3) << 2

      switch p >> 2 {
      case 0: return Int((x0 >> j) & 0xf)
      case 1: return Int((x1 >> j) & 0xf)
      case 2: return Int((x2 >> j) & 0xf)
      default:
        fatalError("index is out of bounds")
      }

    case .regular(let xs):
      return xs[p]
    }
  }

}

extension IndexPath: CustomStringConvertible {

  public var description: String {
    "[\(list: self)]"
  }

}
