import Archivist

/// The type of a node in an abstract syntax tree.
public struct SyntaxTag: Sendable {

  /// The underlying value of `self`.
  public let value: any Syntax.Type

  /// Creates an instance with the given underlying value.
  public init(_ value: any Syntax.Type) {
    self.value = value
  }

  /// Returns `true` iff `scrutinee` and `pattern` denote the same node type.
  public static func ~= (pattern: any Syntax.Type, scrutinee: Self) -> Bool {
    scrutinee == pattern
  }

  /// Returns `true` iff `l` and `r` denote the same node type.
  public static func == (l: Self, r: any Syntax.Type) -> Bool {
    l.value == r
  }

  /// Returns `true` iff `l` and `r` denote the same node type.
  public static func == (l: Self, r: (any Syntax.Type)?) -> Bool {
    l.value == r
  }

  static let allValues: [any Syntax.Type] = [
    // Declarations
    AssociatedTypeDeclaration.self,
    BindingDeclaration.self,
    ConformanceDeclaration.self,
    EnumCaseDeclaration.self,
    EnumDeclaration.self,
    ExtensionDeclaration.self,
    FunctionBundleDeclaration.self,
    FunctionDeclaration.self,
    GenericParameterDeclaration.self,
    ImportDeclaration.self,
    ParameterDeclaration.self,
    StructDeclaration.self,
    TraitDeclaration.self,
    TypeAliasDeclaration.self,
    VariableDeclaration.self,
    VariantDeclaration.self,

    // Expressions
    ArrowExpression.self,
    BooleanLiteral.self,
    Call.self,
    Conversion.self,
    EqualityWitnessExpression.self,
    If.self,
    ImplicitQualification.self,
    InoutExpression.self,
    IntegerLiteral.self,
    KindExpression.self,
    Lambda.self,
    NameExpression.self,
    New.self,
    PatternMatch.self,
    PatternMatchCase.self,
    RemoteTypeExpression.self,
    StaticCall.self,
    StringLiteral.self,
    SumTypeExpression.self,
    SynthethicExpression.self,
    TupleLiteral.self,
    TupleTypeExpression.self,
    WildcardLiteral.self,

    // Patterns
    BindingPattern.self,
    ExtractorPattern.self,
    TuplePattern.self,

    // Statements
    Assignment.self,
    Block.self,
    Discard.self,
    Return.self,
  ]

  static let indices = Dictionary(
    uniqueKeysWithValues: allValues.enumerated().map({ (i, k) in (SyntaxTag(k), i) }))

}

extension SyntaxTag: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.value == r.value
  }

}

extension SyntaxTag: Hashable {

  public func hash(into hasher: inout Hasher) {
    hasher.combine(ObjectIdentifier(value))
  }

}

extension SyntaxTag: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try .init(Self.allValues[Int(archive.readUnsignedLEB128())])
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    archive.write(unsignedLEB128: Self.indices[self]!)
  }

}

extension SyntaxTag: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}
