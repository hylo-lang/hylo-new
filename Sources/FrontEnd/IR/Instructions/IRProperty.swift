import Archivist
import Utilities

/// Exposes the place of a property stored in an opaque record.
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
    record: IRValue, recordTypeWitness: IRValue?,
    property: DeclarationIdentity, propertyType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = .init(record, prependedTo: Array(unwrapping: recordTypeWitness))
    self.anchor = anchor
    self.property = property
    self.propertyType = propertyType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.property = other.property
    self.propertyType = other.propertyType
  }

  /// The address of the record containing the place being exposed.
  public var record: IRValue {
    operands[0]
  }

  /// A witness of the run-time type of the record containing the place being exposed iff the
  /// layout of that type is not available at compile-time.
  public var recordTypeWitness: IRValue? {
    operands[1...].first
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
    let n = printer.program.nameOrTag(of: property)
    let r = if let w = recordTypeWitness {
      "(\(printer.show(record)) : \(printer.show(w)))"
    } else {
      printer.show(record)
    }
    return "property \"\(n)\" of \(r) as \(printer.show(propertyType))"
  }

}
