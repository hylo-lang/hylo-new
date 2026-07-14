import Archivist

/// Copies the discriminator of an enum.
///
///     enum_tag <source : value>
///
/// `enum_tag` copies the tag identifying the active payload of the initialized enum held in the
/// place `source`, defining a register with the value of that discrminiator as a `Builtin.word`.
/// The instruction has undefined behavior if `source` is uninitialized.
@Archivable
public struct IREnumTag: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the tag.
  public let tag: MachineType.ID

  /// Creates an instance with the given properties.
  public init(source: IRValue, tag: MachineType.ID, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
    self.tag = tag
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.tag = other.tag
  }

  /// The place containing the enum whose tag is being read.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the storage accessed by this instruction.
  public var type: IRType {
    .value(tag.erased)
  }

}

extension IREnumTag: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "enum_tag \(printer.show(source))"
  }

}
