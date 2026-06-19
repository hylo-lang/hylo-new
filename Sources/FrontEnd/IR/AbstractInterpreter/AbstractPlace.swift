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

  /// A pair (`r`, `p`) where `p` is the path to this place, relative to the root location `r`.
  internal var location: (root: IRValue, path: IndexPath) {
    switch self {
    case .root(let root):
      return (root, .init())
    case .subplace(let root, let path):
      return (root, path)
    }
  }

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
