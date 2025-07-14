/// Returns the getter of a property in an opaque record.
public struct IRGetter: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The property whose getter is returned.
  public let property: DeclarationIdentity

  /// The type of the getter returned by this instruction.
  public let typeOfGetter: FunctionPointer.ID

  /// Creates an instance with the given properties.
  public init(
    property: DeclarationIdentity, receiver: IRValue,
    typeOfGetter: FunctionPointer.ID,
    anchor: Anchor
  ) {
    self.operands = [receiver]
    self.anchor = anchor
    self.property = property
    self.typeOfGetter = typeOfGetter
  }

  /// The address of the record containing the property whose getter is returned.
  public var receiver: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .hylo(typeOfGetter.erased, isAddress: false)
  }

}

extension IRGetter: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "getter \(printer.program.nameOrTag(of: property)) of \(printer.show(receiver))"
  }

}

