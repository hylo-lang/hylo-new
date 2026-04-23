import Archivist

/// Marks the execution path as unreachable.
public struct IRUnreachable: Terminator {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(anchor: Anchor) {
    self.anchor = anchor
  }

  /// Creates a copy of `other`, substituting its properties with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self = other
  }

}

extension IRUnreachable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "unreachable"
  }

}
