import Archivist

/// Accesses the captures of a witness table.
@Archivable
public struct IRWitnessTableCapture: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The logical index of the capture being indexed.
  public let index: Int

  /// The type of the capture being accessed.
  public let captureType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(source: IRValue, index: Int, captureType: AnyTypeIdentity, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
    self.index = index
    self.captureType = captureType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.index = other.index
    self.captureType = other.captureType
  }

  /// The witness table whose stash is being accessed.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .place(captureType)
  }

}

extension IRWitnessTableCapture: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "witness_table_capture \(printer.show(source)) at \(index) as \(printer.show(captureType))"
  }

}
