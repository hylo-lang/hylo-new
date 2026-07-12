import Archivist

/// Transfers control flow to the start of one of several basic blocks.
///
///     switch <scrutinee : value>, <t0 : block>, ..., <tn : block>
///
/// `switch` reads the value `i` of `scrutinee`, which is a `Builtin.word`, and transfers control
/// flow to the basic block `ti`. The instruction has undefined behavior if `ti` does not exist.
public struct IRSwitch: Terminator {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The basic blocks to which control flow may be transferred.
  public private(set) var successors: [IRBlock.ID]

  /// Creates an instance with the given properties.
  public init(scrutinee: IRValue, successors: [IRBlock.ID], anchor: Anchor) {
    self.operands = [scrutinee]
    self.successors = successors
    self.anchor = anchor
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.scrutinee]]
    self.anchor = properties.anchor(other)
    self.successors = other.successors.map({ (b) in properties[b] })
  }

  /// A 0-based index identifying the basic-block to which control flow should be transferred.
  public var scrutinee: IRValue {
    operands[0]
  }

  /// Replaces `old` with `new` and returns `true` iff `old` is successor of `self`.
  @discardableResult
  public mutating func replaceSuccessor(_ old: IRBlock.ID, with new: IRBlock.ID) -> Bool {
    var replaced = false
    for i in successors.indices where successors[i] == old {
      successors[i] = new
      replaced = true
    }
    return replaced
  }

}

extension IRSwitch: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let bs = successors.map({ (b) in "%b\(b.rawValue)" })
    return "switch \(printer.show(scrutinee)), \(list: bs)"
  }

}

extension IRSwitch: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.anchor = try archive.read(Anchor.self, in: &context)
    self.operands = [try archive.read(IRValue.self, in: &context)]
    self.successors = try archive.readArray(of: IRBlock.ID.self, in: &context) { (a, c) in
      try a.read(IRBlock.ID.self, in: &c)
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(anchor, in: &context)
    try archive.write(scrutinee, in: &context)
    try archive.write(contentsOf: successors, in: &context) { (x, a, c) in
      try a.write(x, in: &c)
    }
  }

}
