import Archivist
import Utilities

/// Accesses a property stored in an opaque record.
@Archivable
public struct IRProperty: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The declaration of the property being accessed.
  public let part: DeclarationIdentity

  /// The type of the property being accessed.
  public let partType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    whole: IRValue, part: DeclarationIdentity, partType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [whole]
    self.anchor = anchor
    self.part = part
    self.partType = partType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.whole]]
    self.anchor = properties.anchor(other)
    self.part = other.part
    self.partType = other.partType
  }

  /// The place of the whole containing the property being accessed.
  public var whole: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(partType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

  /// Asserts the well-formedness conditions of the instruction.
  public func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool {
    // The record is a place storing a witness table.
    guard
      let t = parent.result(of: whole),
      let (c, _) = program.types.seenAsTraitApplication(t.type)
    else { preconditionFailure("bad operand") }

    // The selected property exists.
    precondition(program.requirements(of: c).index(of: part) != nil)
    return true
  }

}

extension IRProperty: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let n = printer.program.nameOrTag(of: part)
    return "property \"\(n)\" of \(printer.show(whole)) as \(printer.show(partType))"
  }

}
