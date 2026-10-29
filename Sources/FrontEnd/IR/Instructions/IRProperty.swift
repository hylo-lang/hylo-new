import Archivist
import Utilities

/// Accesses a part identified by its declaration in a record.
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
