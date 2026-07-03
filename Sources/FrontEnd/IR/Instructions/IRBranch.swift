import Archivist

/// Unconditionally transfers control flow to the start of a basic block.
public struct IRBranch: Terminator {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The basic blocks to which control flow may be transferred.
  public private(set) var successors: [IRBlock.ID]

  /// Creates an instance with the given properties.
  public init(target: IRBlock.ID, anchor: Anchor) {
    self.anchor = anchor
    self.successors = [target]
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.anchor = properties.anchor(other)
    self.successors = [properties[other.target]]
  }

  /// The target of the branch.
  public var target: IRBlock.ID {
    successors[0]
  }

  /// Replaces `old` with `new` and returns `true` iff `old` is successor of `self`.
  @discardableResult
  public mutating func replaceSuccessor(_ old: IRBlock.ID, with new: IRBlock.ID) -> Bool {
    if successors[0] == old {
      successors[0] = new
      return true
    } else {
      return false
    }
  }

}

extension IRBranch: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "br %b\(target.rawValue)"
  }

}

extension IRBranch: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.anchor = try archive.read(Anchor.self, in: &context)
    self.successors = try archive.readArray(of: IRBlock.ID.self, in: &context) { (a, c) in
      try a.read(IRBlock.ID.self, in: &c)
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(anchor, in: &context)
    try archive.write(contentsOf: successors, in: &context) { (x, a, c) in
      try a.write(x, in: &c)
    }
  }

}
