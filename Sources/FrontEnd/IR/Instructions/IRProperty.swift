import Archivist
import Utilities

/// Accesses a part of a record given the declaration of that part.
///
///    property "<part : declaration>" of <whole : value> as <partType : type>
///
/// `property` defines a place of type `partType` representing the part declared by `part` within
/// the place `whole`. The type of `whole` must be a record type containing that part, and
/// `partType` must be the type of the part in that record, with the record's generic arguments
/// substituted. The lifetime of `whole` is extended by that of the resulting place.
///
/// Unlike `subfield`, which identifies a part by its position, `property` identifies it by its
/// declaration and does not require the layout of the record to be visible where the instruction
/// occurs. If that layout is visible and `part` declares a stored property of a struct, `property`
/// behaves like `subfield` at the position of that property: the resulting place is the
/// corresponding part of `whole`, sharing its initialization state. Otherwise, the resulting place
/// is opaque and considered initialized, and `whole` must be initialized.
///
///    property "<part : declaration>" of (<whole : value> : <witness : value>) as <partType : type>
///
/// This form is used when the type of `whole` depends on type parameters, so the offset of the
/// part is not known statically. That offset is read from `witness`, the run-time type witness of
/// `whole`'s type, whose lifetime is also extended by that of the resulting place. This form is
/// emitted during depolymorphization.
@Archivable
public struct IRProperty: IRPart {

  /// The operands of the instruction.
  public private(set) var operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The declaration of the property being accessed.
  public let part: DeclarationIdentity

  /// The type of the property being accessed.
  public let partType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    whole: IRValue, wholeWitness: IRValue?, part: DeclarationIdentity, partType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = Array(whole, prependedTo: Array(unwrapping: wholeWitness))
    self.anchor = anchor
    self.part = part
    self.partType = partType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.part = other.part
    self.partType = other.partType
  }

  /// The place of the whole containing the property being accessed.
  public var whole: IRValue {
    operands[0]
  }

  /// A witness of the run-time type of the whole iff that type has been existentialized.
  public var wholeWitness: IRValue? {
    (operands.count > 1) ? operands[1] : nil
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(partType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

  /// Returns a copy of `self` reading member offsets from the given witness.
  public func existentialized(readingOffsetsWith wholeWitness: IRValue) -> IRProperty {
    precondition(self.wholeWitness == nil, "instruction already existentialized")
    var clone = self
    clone.operands.append(wholeWitness)
    return clone
  }

}

extension IRProperty: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let n = printer.program.nameOrTag(of: part)
    let w: String

    if let t = wholeWitness {
      w = "(\(printer.show(whole)) : \(printer.show(t)))"
    } else {
      w = printer.show(whole)
    }

    return "property \"\(n)\" of \(w) as \(printer.show(partType))"
  }

}
