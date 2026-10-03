import Archivist

/// Accesses the captures of a witness table.
@Archivable
public struct IRWitnessTableStash: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the stash being accessed.
  public let stashType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(source: IRValue, stashType: AnyTypeIdentity, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
    self.stashType = stashType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.stashType = other.stashType
  }

  /// The witness table whose stash is being accessed.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(stashType)
  }

}

extension IRWitnessTableStash: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "witness_table_stash \(printer.show(source)) as \(printer.show(stashType))"
  }

}
