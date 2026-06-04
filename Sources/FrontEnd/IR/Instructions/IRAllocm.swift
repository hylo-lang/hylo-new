/// Allocates storage in auxiliary memory.
///
/// This instruction is similar to `malloc`, except that it allocates memory in a dedicated arena,
/// called the "auxiliary memory", rather than relying on the host's allocator. Hence it can be
/// used in freehosted builds.
///
/// Memory allocated with `allocm` *must* be manually freed with `deallocm`.
public struct IRAllocm: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the allocated storage.
  public let pointer: MachineType.ID

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// Creates an instance denoting storage for values of the type described by `witness`.
  public init(witness: IRValue, pointer: MachineType.ID, alignment: IRAlignment, anchor: Anchor) {
    self.operands = [witness]
    self.anchor = anchor
    self.pointer = pointer
    self.alignment = alignment
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.pointer = other.pointer
    self.alignment = other.alignment
  }

  /// A witness of the run-time type of the allocated storage.
  public var witness: IRValue {
    operands[0]
  }

  /// The compile-time type of the storage being allocated.
  public var type: IRType {
    .value(pointer.erased)
  }

}

extension IRAllocm: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "allocm \(printer.show(witness)), \(printer.show(alignment))"
  }

}
