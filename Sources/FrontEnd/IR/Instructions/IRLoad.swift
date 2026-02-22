/// Loads a value from memory to register.
///
/// If the source is not a machine type, the operation requires exclusive access to the source,
/// which must be initialized before the operation and is left uninitialized after. For machine
/// types, we always copy the values, so no consume semantics.
///
/// The size of the value being loaded must be known at compile-time.
public struct IRLoad: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(source: IRValue, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
  }

  /// The address of the storage from which the value is read.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .dereferenced(source)
  }

}

extension IRLoad: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "load \(printer.show(source))"
  }

}
