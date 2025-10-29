import Utilities

/// Projects a value by invoking the ramp of a subscript.
public struct IRProject: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the projected value.
  public let typeOfProjection: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    callee: IRValue,
    arguments: [IRValue],
    typeOfProjection: AnyTypeIdentity,
    anchor: Anchor
  ) {
    var operands = Array<IRValue>(minimumCapacity: arguments.count + 1)
    operands.append(callee)
    operands.append(contentsOf: arguments)

    self.operands = operands
    self.anchor = anchor
    self.typeOfProjection = typeOfProjection
  }

  /// The subscript being applied.
  public var callee: IRValue {
    operands[0]
  }

  /// The arguments of the call.
  public var arguments: ArraySlice<IRValue> {
    operands[1...]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .lowered(typeOfProjection, isAddress: true)
  }

}

extension IRProject: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "project \(printer.show(callee))[\(printer.show(arguments))]"
  }

}
