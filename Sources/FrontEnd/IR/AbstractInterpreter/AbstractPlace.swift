/// A memory location in an abstract interpreter.
internal enum AbstractPlace: Hashable, Sendable {

  /// A root location.
  case root(IRValue)

  /// A sub-location rooted at an argument or register.
  ///
  /// `path[i]` is the index of a stored property in the abstract layout of the object held in
  /// `.subplace(root: r, path: path.prefix[..<i])`. For example, if `r` is a place of type
  /// `{{A, B}, C}`, then `subplace(root: r, path: [0, 1])` is a place of type `B`.
  ///
  /// Use `appending(contentsOf:)` to create instances of this case.
  indirect case subplace(root: IRValue, path: IndexPath)

  /// Returns a new place created by appending `suffix` to `self`.
  ///
  /// - Requires: `self` is not `.null`.
  internal func appending(contentsOf suffix: IndexPath) -> Self {
    if suffix.isEmpty { return self }

    switch self {
    case .root(let root):
      return .subplace(root: root, path: suffix)
    case .subplace(let root, let prefix):
      return .subplace(root: root, path: prefix.appending(contentsOf: suffix))
    }
  }

  /// Returns `l` merged with `r`.
  internal static func && (l: Self, r: Self) -> Self {
    precondition(l == r, "invalid merge")
    return l
  }

}

//extension AbstractPlace: Comparable {
//
//  /// Returns `true` iff `self` precedes `other` in a lexicographical order.
//  internal static func < (l: Self, r: Self) -> Bool {
//    switch (l, r) {
//    case (.root(let a), .root(let b)):
//      return areInIncreasingOrder(a, b)
//    case (.root(let a), .subplace(let b, _)):
//      return (a == b) || areInIncreasingOrder(a, b)
//    case (.subplace(let a, _), .root(let b)):
//      return areInIncreasingOrder(a, b)
//    case (.subplace(let a, let p), .subplace(let b, let q)):
//      return (a == b) ? p.lexicographicallyPrecedes(q) : areInIncreasingOrder(a, b)
//    }
//  }
//
//  /// Returns `true` iff `l` precedes `r` when computing whether two abstract places are in order.
//  private static func areInIncreasingOrder(_ l: IRValue, _ r: IRValue) -> Bool {
//    switch (l, r) {
//    case (.parameter(let a), .parameter(let b)):
//      return a < b
//    case (.parameter, _):
//      return true
//    case (.register, .parameter):
//      return false
//    case (.register(let a), .register(let b)):
//      return a < b
//    default:
//      fatalError()
//    }
//  }
//
//}

extension AbstractPlace: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .root(let r):
      return "[\(printer.show(r))]"
    case .subplace(let root, let path):
      return "[\(printer.show(root))].\(list: path, joinedBy: ".")"
    }
  }

}
