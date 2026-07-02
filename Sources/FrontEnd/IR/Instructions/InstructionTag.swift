import Archivist

/// The type of an IR instruction.
public struct InstructionTag: Sendable {

  /// The underlying value of `self`.
  public let value: any Instruction.Type

  /// Creates an instance with the given underlying value.
  public init(_ value: any Instruction.Type) {
    self.value = value
  }

  /// Returns `true` iff `scrutinee` and `pattern` denote the same instruction type.
  public static func ~= (pattern: any Instruction.Type, scrutinee: Self) -> Bool {
    scrutinee == pattern
  }

  /// Returns `true` iff `l` and `r` denote the same instruction type.
  public static func == (l: Self, r: any Instruction.Type) -> Bool {
    l.value == r
  }

  /// Returns `true` iff `l` and `r` denote the same instruction type.
  public static func == (l: Self, r: (any Instruction.Type)?) -> Bool {
    l.value == r
  }

  static let allValues: [any Instruction.Type] = [
    IRAccess.self,
    IRAccess.End.self,
    IRAlloca.self,
    IRApply.self,
    IRApplyBuiltin.self,
    IRAssumeState.self,
    IRBranch.self,
    IRConditionalBranch.self,
    IRGlobalAccess.self,
    IRLoad.self,
    IRMemoryCopy.self,
    IRMove.self,
    IRPartialApply.self,
    IRPlaceCast.self,
    IRProject.self,
    IRProject.End.self,
    IRProperty.self,
    IRReturn.self,
    IRStore.self,
    IRSubfield.self,
    IRTypeApply.self,
    IRTypeWitness.self,
    IRUnreachable.self,
    IRWitnessTable.self,
    IRYield.self,
  ]

  static let indices = Dictionary(
    uniqueKeysWithValues: allValues.enumerated().map({ (i, k) in (InstructionTag(k), i) }))

}

extension InstructionTag: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.value == r.value
  }

}

extension InstructionTag: Hashable {

  public func hash(into hasher: inout Hasher) {
    hasher.combine(ObjectIdentifier(value))
  }

}

extension InstructionTag: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try .init(Self.allValues[Int(archive.readUnsignedLEB128())])
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    archive.write(unsignedLEB128: Self.indices[self]!)
  }

}

extension InstructionTag: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}
