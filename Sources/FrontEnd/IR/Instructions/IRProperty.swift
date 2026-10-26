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
    whole: IRValue, wholeType: IRValue?, part: DeclarationIdentity, partType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = Array(whole, prependedTo: Array(unwrapping: wholeType))
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

  /// A witness of the run-time type of the whole iff that type has been existentialized.
  public var wholeType: IRValue? {
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

}

extension IRProperty: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let n = printer.program.nameOrTag(of: part)
    let w: String

    if let t = wholeType {
      w = "(\(printer.show(whole)) : \(printer.show(t)))"
    } else {
      w = printer.show(whole)
    }

    return "property \"\(n)\" of \(w) as \(printer.show(partType))"
  }

}
