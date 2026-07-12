import OrderedCollections

/// A set of diagnostics.
public struct DiagnosticSet: Hashable, Sendable, CustomStringConvertible {

  /// The diagnostics in the set.
  public private(set) var elements: OrderedSet<Diagnostic>

  /// `true` iff `self` contains the diagnostic of an error.
  public private(set) var containsError: Bool

  /// Inserts `d` into `self`.
  public mutating func insert(_ d: Diagnostic) {
    if elements.append(d).inserted {
      containsError = containsError || (d.level == .error)
    }
  }

  /// Inserts the contents of `ds` into `self`.
  public mutating func formUnion(_ ds: DiagnosticSet) {
    for d in ds.elements { insert(d) }
  }

  /// Creates an empty instance.
  public init() {
    self.elements = []
    self.containsError = false
  }

  /// Creates an instance with the given diagnostics.
  public init<S: Sequence<Diagnostic>>(_ ds: S) {
    self.init()
    for d in ds { insert(d) }
  }

  public var description: String {
    "\n" + elements.lazy.map(\.description).joined(separator: "\n")
  }

}
