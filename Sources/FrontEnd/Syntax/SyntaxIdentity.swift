import Archivist
import Utilities

/// A type denoting the identity of a node in an abstract syntax tree.
public protocol SyntaxIdentity: Comparable, Hashable, Showable, Archivable, Sendable {

  /// The type-erased value of this identity.
  var erased: AnySyntaxIdentity { get }

  /// Creates an identifying the same node as `erased`.
  init(uncheckedFrom erased: AnySyntaxIdentity)

}

extension SyntaxIdentity {

  /// The module offset of the node represented by `self` in its containing collection.
  public var module: Module.ID {
    erased.module
  }

  /// The file offset of the node represented by `self` in its containing collection.
  public var file: SourceFile.ID {
    erased.file
  }

  /// The offset of the node represented by `self` in its containing collection.
  public var offset: Int {
    erased.offset
  }

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func == <T: SyntaxIdentity>(l: Self, r: T) -> Bool {
    l.erased == r.erased
  }

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func ~= <T: SyntaxIdentity>(l: Self, r: T) -> Bool {
    l.erased == r.erased
  }

  /// Returns `true` if `l` is ordered before `r`.
  public static func < (l: Self, r: Self) -> Bool {
    l.erased < r.erased
  }

  public func show(using printer: inout TreePrinter) -> String {
    printer.program[self].show(using: &printer)
  }

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    self.init(uncheckedFrom: try archive.read(AnySyntaxIdentity.self, in: &context))
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(erased, in: &context)
  }

}

/// The type-erased identity of an abstract syntax tree.
///
/// An identity is composed of three offsets stored contiguously within a 64-bit integer in the
/// following order (from least to most significant):
///
/// - `module`: a 16-bit offset identifying the module in which the node is contained.
/// - `file`  : a 16-bit offset identifying the file in which the node is contained.
/// - `node`  : a 32-bit offset identifying the node itself.
///
/// All three offsets are interpreted as unsigned integers. The maximum representable value of the
/// node offset is reserved as a tag.
public struct AnySyntaxIdentity {

  /// The bit representation of `self`.
  public let bits: UInt64

  /// Creates an instance with the given bit representation.
  public init(bits: UInt64) {
    self.bits = bits
  }

  /// Creates an instance identifying the node at offset `n` in file `f`.
  public init(file f: SourceFile.ID, offset n: Int) {
    precondition(n < UInt32.max)
    self.bits = UInt64(f.rawValue) | (UInt64(n) << 32)
  }

  /// Creates an identifying the same node as `other`.
  public init<T: SyntaxIdentity>(_ other: T) {
    self.bits = other.erased.bits
  }

  /// The module offset of the node represented by `self` in its containing collection.
  public var module: Module.ID {
    .init(bits & 0xffff)
  }

  /// The file offset of the node represented by `self` in its containing collection.
  public var file: SourceFile.ID {
    .init(rawValue: UInt32(bits & 0xffff_ffff))
  }

  /// The offset of the node represented by `self` in its containing collection.
  public var offset: Int {
    .init(bits >> 32)
  }

  /// Returns the identity representing the lexical scope of formed by `f`.
  internal static func scope(of f: SourceFile.ID) -> Self {
    .init(bits: UInt64(f.rawValue) | UInt64(UInt32.max) << 32)
  }

}

extension AnySyntaxIdentity: SyntaxIdentity {

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self = erased
  }

  /// The type-erased value of this identity.
  public var erased: AnySyntaxIdentity {
    self
  }

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func == <T: SyntaxIdentity>(l: Self, r: T) -> Bool {
    l.bits == r.erased.bits
  }

  /// Returns `true` if `l` is ordered before `r`.
  public static func < (l: Self, r: Self) -> Bool {
    l.bits < r.bits
  }

}

extension AnySyntaxIdentity: ExpressibleByIntegerLiteral {

  public init(integerLiteral value: UInt64) {
    self.init(bits: value)
  }

}

extension AnySyntaxIdentity: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    let c = context as? Module.SerializationContext ?? fatalError("bad context")
    let b = try archive.read(UInt64.self)
    let m = UInt64(c.modules[Int(b & 0xffff)]!)
    self.bits = b & ~0xffff | m
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    let c = context as? Module.SerializationContext ?? fatalError("bad context")
    let m = UInt64(c.modules[Int(bits & 0xffff)]!)
    try archive.write(bits & ~0xffff | m)
  }

}

extension AnySyntaxIdentity: CustomStringConvertible {

  public var description: String { bits.description }

}

/// The identity of a node in an abstract syntax tree.
public struct ConcreteSyntaxIdentity<T: Syntax>: SyntaxIdentity {

  /// The type-erased value of this identity.
  public let erased: AnySyntaxIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self.erased = erased
  }

}

/// The type-erased identity of an abstract syntax tree denoting a declaration.
public struct DeclarationIdentity: SyntaxIdentity {

  /// The type-erased value of this identity.
  public let erased: AnySyntaxIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self.erased = erased
  }

  /// Creates an instance equal to `other`.
  public init<T: Declaration>(_ other: T.ID) {
    self.erased = other.erased
  }

}

/// The type-erased identitiy of an abstract syntax tree denoting an expression.
public struct ExpressionIdentity: SyntaxIdentity {

  /// The type-erased value of this identity.
  public let erased: AnySyntaxIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self.erased = erased
  }

  /// Creates an instance equal to `other`.
  public init<T: Expression>(_ other: T.ID) {
    self.erased = other.erased
  }

}

/// The type-erased identity of an abstract syntax tree denoting a pattern.
public struct PatternIdentity: SyntaxIdentity {

  /// The type-erased value of this identity.
  public let erased: AnySyntaxIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self.erased = erased
  }

  /// Creates an instance equal to `other`.
  public init<T: Pattern>(_ other: T.ID) {
    self.erased = other.erased
  }

  /// Creates an instance equal to `other`.
  public init(_ other: ExpressionIdentity) {
    self.erased = other.erased
  }

}

/// The type-erased identity of an abstract syntax tree denoting a statement.
public struct StatementIdentity: SyntaxIdentity {

  /// The type-erased value of this identity.
  public let erased: AnySyntaxIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self.erased = erased
  }

  /// Creates an instance equal to `other`.
  public init<T: Statement>(_ other: T.ID) {
    self.erased = other.erased
  }

  /// Creates an instance equal to `other`.
  public init(_ other: DeclarationIdentity) {
    self.erased = other.erased
  }

  /// Creates an instance equal to `other`.
  public init(_ other: ExpressionIdentity) {
    self.erased = other.erased
  }

}

/// The identity of an expression or binding declaration in the conditions of an if-expression,
/// match-expression, or while loop.
public struct ConditionIdentity: SyntaxIdentity {

  /// The type-erased value of this identity.
  public let erased: AnySyntaxIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnySyntaxIdentity) {
    self.erased = erased
  }

  /// Creates an instance equal to `other`.
  public init(_ other: ExpressionIdentity) {
    self.erased = other.erased
  }

  /// Creates an instance equal to `other`.
  public init(_ other: BindingDeclaration.ID) {
    self.erased = other.erased
  }

}
