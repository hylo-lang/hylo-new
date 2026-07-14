import Archivist

/// Converts a built-in pointer to a place.
///
///     pointer_to_place <source : value> as <access : effect> <target : type>
///
/// `pointer_to_place` defines a place of type `target` with the value of `source`, which denotes
/// the value of a `Builtin.ptr`, using `access` to determine the memory state of the place. The
/// resulting place unsafely refers to the memory referenced by `source`.
@Archivable
public struct IRPointerToPlace: IRRegionEntry {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The capabilities of the place.
  public let access: AccessEffect

  /// The type of the resulting place.
  public let target: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(source: IRValue, access: AccessEffect, target: AnyTypeIdentity, anchor: Anchor) {
    self.operands = [source]
    self.anchor = anchor
    self.access = access
    self.target = target
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = [properties[other.source]]
    self.anchor = properties.anchor(other)
    self.access = other.access
    self.target = other.target
  }

  /// The pointer being converted to a place.
  public var source: IRValue {
    operands[0]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(target)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

}

extension IRPointerToPlace: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "pointer_to_place \(printer.show(source)) as \(access) \(printer.show(target))"
  }

}
