/// Unsafely assumes the initialization state of memory storage.
public struct IRAssumeState: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// `true` if `storage` is assumed initialized or `false` if `storage` is assumed uninitialized.
  public let initialized: Bool

  /// Creates an instance with the given properties.
  public init(storage: IRValue, initialized: Bool, anchor: Anchor) {
    self.operands = [storage]
    self.anchor = anchor
    self.initialized = initialized
  }

  /// The address of the storage whose initialization state is assumed.
  public var storage: IRValue {
    operands[0]
  }

}

extension IRAssumeState: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let s = initialized ? "initialized" : "uninitialized"
    return "assume_state \(printer.show(storage)) \(s)"
  }

}
