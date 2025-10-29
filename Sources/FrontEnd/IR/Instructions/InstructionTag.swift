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
    // Instructions.
    IRAccess.End.self,
    IRLoad.self,
    IRStore.self,
    IRProperty.self,

    // Terminators.
    IRReturn.self,
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

extension InstructionTag: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}
