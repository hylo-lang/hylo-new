import Archivist

/// Projects a value at a different type.
///
///     place_cast <source : value> as <access : effect> <target : type>
///
/// `place_cast` projects the contents of `source`, which is the result an access instruction, as
/// contents of type `target` into a region, using `effect` to determine the memory state of the
/// source before and after that region.
///
/// The conversion is not checked. Accessing the resulting place has undefined behavior unless
/// `target` is layout-compatible with the type of `source`.
@Archivable
public struct IRPlaceCast: IRRegionEntry {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The capabilities of the projection.
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

  /// The place being converted.
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

extension IRPlaceCast: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "place_cast \(printer.show(source)) as \(access) \(printer.show(target))"
  }

}
