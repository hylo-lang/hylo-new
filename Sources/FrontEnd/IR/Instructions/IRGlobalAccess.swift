/// Accesses the storage of a global variable.
///
/// This instruction defines a place representing the contents of a global variable after it has
/// been initialized. The object stored at that place is immutable.
public struct IRGlobalAccess: Instruction {

  /// The global variable being accessed.
  public let source: IRGlobal

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(source: IRGlobal, anchor: Anchor) {
    self.source = source
    self.anchor = anchor
  }

  /// The type of the value loaded by this instruction.
  public var type: IRType {
    .lowered(source.storageType, isAddress: true)
  }

}

extension IRGlobalAccess: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "global_access \(printer.show(source.name))"
  }

}
