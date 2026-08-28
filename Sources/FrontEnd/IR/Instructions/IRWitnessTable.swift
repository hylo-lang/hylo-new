import Archivist

/// Creates a witness table.
///
///     witness_table
///       ['<' <arguments... : type> '>']
///       ['[' <captures... : value> ']']
///       (<entries... : value>) as <witness : type>
///
/// `witness_table` assembles an object witnessing of the conformance of a type to some trait by
/// gathering `entries`, `aruguments`, and `captures`, which list the implementations the trait's
/// requirements, the type arguments instantiating generic entries, and the values copied into the
/// table's stash, respectively.
@Archivable
public struct IRWitnessTable: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type arguments of the table iff it is generic.
  public let arguments: TypeArguments

  /// The number of entries in the table.
  public let entryCount: Int

  /// The type of the witness represented by the table.
  public let witnessType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    instantiatedWith arguments: TypeArguments,
    aggregating entries: [IRValue], capturing captures: [IRValue],
    as witnessType: AnyTypeIdentity,
    at anchor: Anchor
  ) {
    self.operands = entries + captures
    self.anchor = anchor
    self.arguments = arguments
    self.entryCount = entries.count
    self.witnessType = witnessType
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.arguments = other.arguments
    self.entryCount = other.entryCount
    self.witnessType = other.witnessType
  }

  /// The implementations populating the table.
  public var entries: ArraySlice<IRValue> {
    operands[..<entryCount]
  }

  /// The values captured in the table.
  public var captures: ArraySlice<IRValue> {
    operands[entryCount...]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(witnessType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

}

extension IRWitnessTable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "witness_table "

    // Type arguments, if any.
    if !arguments.isEmpty { result.append("<\(printer.show(arguments.values))>") }
    // Entries.
    result.append("{\(printer.show(entries))}")
    // Captures, if any.
    if !captures.isEmpty { result.append("+[\(printer.show(captures))]") }
    // Type.
    result.append(" as \(printer.show(witnessType))")

    return result
  }

}
