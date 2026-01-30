/// Creates an access on a storage.
///
/// Hylo IR uses a capability system to govern storage accesses. To read/write values from/to
/// memory, one must acquire a capability on the storage matching the desired effect. For example,
/// a `set` capability is required to initialize storage. These capabilties can only be formed by
/// executing an `access` instruction and they must be eventually released using `end_access`.
/// During IR analyis, the compiler verifies that the instructions do not violate the rights and
/// duties associated with each acquired capability.
///
/// It is possible to create accesses on "raw addresses" (those result from instructions allocating
/// memory or computing addresses) or on other accesses. For example, it is legal to form a `let`
/// access from an `inout` access.
public struct IRAccess: IRRegionEntry {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The capabilities requested by the access.
  ///
  /// IR lowering cannot always determine the capability required to access storage, since this
  /// information is implicit in Hylo sources and depends on control flow. For example, calling a
  /// bundle may request the `let` or `sink` capability on the arguments depending on their future
  /// uses (or lack thereof). In these cases, IR lowering will emit `access` instructions with the
  /// set capabilities that may be inferred from the syntax. These instructions are expected to be
  /// "reifed" during IR analysis so that only a single capability is requested.
  public let capabilities: AccessEffectSet

  /// Creates an instance with the given properties.
  public init(capabilities: AccessEffectSet, source: IRValue, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
    self.capabilities = capabilities
  }

  /// The address of the storage on which a capability is requested.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the storage accessed by this instruction.
  public var type: IRType {
    .same(as: source)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

}

extension IRAccess: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "access \(capabilities) \(printer.show(source))"
  }

}
