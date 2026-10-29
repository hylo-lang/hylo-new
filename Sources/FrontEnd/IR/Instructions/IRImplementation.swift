import Archivist
import Utilities

/// Accesses the implementation of a requirement stored in a witness table.
@Archivable
public struct IRImplementation: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The declaration of the requirement whose implementation is being accessed.
  public let requirement: DeclarationIdentity

  /// The type of the implementation being accessed.
  public let interface: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    table: IRValue, requirement: DeclarationIdentity, interface: AnyTypeIdentity, anchor: Anchor
  ) {
    self.operands = [table]
    self.anchor = anchor
    self.requirement = requirement
    self.interface = interface
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.table]]
    self.anchor = properties.anchor(other)
    self.requirement = other.requirement
    self.interface = other.interface
  }

  /// The place of the table containing the implementation being accessed.
  public var table: IRValue {
    operands[0]
  }

  /// A witness of the run-time type of the whole iff that type has been existentialized.
  public var wholeWitness: IRValue? {
    (operands.count > 1) ? operands[1] : nil
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(interface)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

  /// Asserts the well-formedness conditions of the instruction.
  public func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool {
    // The record is a place storing a witness table.
    guard
      let t = parent.result(of: table),
      let (c, _) = program.types.seenAsTraitApplication(t.type)
    else { preconditionFailure("bad operand") }

    // The selected property exists.
    precondition(program.requirements(of: c).index(of: requirement) != nil)
    return true
  }

}

extension IRImplementation: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let n = printer.program.nameOrTag(of: requirement)
    let t = printer.show(table)
    let i = printer.show(interface)
    return "implementation \"\(n)\" in \(t) as \(i)"
  }

}
