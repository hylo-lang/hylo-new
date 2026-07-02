import Archivist
import Utilities

/// Returns the address of a property stored in an opaque record.
@Archivable
public struct IRProperty: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The property being accessed.
  public let property: DeclarationIdentity

  /// The type of the property being accessed.
  public let propertyType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    record: IRValue, property: DeclarationIdentity, propertyType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [record]
    self.anchor = anchor
    self.property = property
    self.propertyType = propertyType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.record]]
    self.anchor = properties.anchor(other)
    self.property = other.property
    self.propertyType = other.propertyType
  }

  /// The address of the record containing the property whose getter is returned.
  public var record: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(propertyType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

  /// Asserts the well-formedness conditions of the instruction.
  public func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool {
    // The record is a place storing a witness table.
    guard
      let t = parent.result(of: record),
      let (c, _) = program.types.seenAsTraitApplication(t.type)
    else { preconditionFailure("bad operand") }

    // The selected property exists.
    precondition(program.requirements(of: c).index(of: property) != nil)
    return true
  }

}

extension IRProperty: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "property \"\(printer.program.nameOrTag(of: property))\" of \(printer.show(record))"
  }

}
