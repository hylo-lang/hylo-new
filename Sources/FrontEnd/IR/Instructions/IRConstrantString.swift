import Archivist

/// Creates the internal representation of constant string allocated statically.
///
/// The result is a 64-bit integer corresponding to the byte representation of a string in Hylo.
@Archivable
public struct IRConstantString: Instruction {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the value loaded by this instruction.
  public let type: IRType

  /// The value of the string, encoded in UTF-8.
  public let contents: String

  /// Creates an instance with the given properties.
  public init(contents: String, i64: MachineType.ID, anchor: Anchor) {
    self.contents = contents
    self.type = .value(i64.erased)
    self.anchor = anchor
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.contents = other.contents
    self.type = other.type
    self.anchor = properties.anchor(other)
  }

}

extension IRConstantString: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    return "constant_string \(contents)"
  }

}

//extension Module {
//
//  /// Creates a `constant_string` anchored at `site` that returns a  string with given `value`,
//  /// encoded in UTF8.
//  func makeConstantString(utf8 value: Data, at site: SourceRange) -> ConstantString {
//    .init(value: value, site: site)
//  }
//
//}
