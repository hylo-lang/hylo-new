import Archivist

/// A table from trait requirement to its implementation.
public struct WitnessTable: Hashable, Sendable {

  /// The trait declaring the requirements occurring as keys in this table.
  public let concept: Trait.ID

  /// The type arguments of the trait.
  public let arguments: TypeArguments

  /// A table from base requirement to its implementation.
  private var bases: [Int: WitnessExpression]

  /// A table from associated type requirement to its implementation.
  private var associatedTypes: [Int: AnyTypeIdentity]

  /// A table from member requirement to its implementation.
  private var members: [Int: DeclarationReference]

  /// Creates an instance with the given properties.
  private init(
    concept: Trait.ID,
    arguments: TypeArguments,
    bases: [Int: WitnessExpression],
    associatedTypes: [Int: AnyTypeIdentity],
    members: [Int: DeclarationReference]
  ) {
    self.concept = concept
    self.arguments = arguments
    self.bases = bases
    self.associatedTypes = associatedTypes
    self.members = members
  }

  /// Creates an empty instance.
  public init(concept: Trait.ID, arguments: TypeArguments) {
    self.init(
      concept: concept, arguments: arguments,
      bases: [:], associatedTypes: [:], members: [:])
  }

  /// `true` iff `self` witnesses a synthetic conformance that does not involve any user code.
  public var isTransitivelySynthetic: Bool {
    !members.isEmpty && members.allSatisfy(\.value.isTransitivelySynthethic)
  }

  /// Assigns `i` to `r`, which is a base trait requirement.
  internal mutating func assign(_ i: WitnessExpression, to r: ConformanceDeclaration.ID) {
    bases[r.offset] = i
  }

  /// Assigns `i` to `r`, which is an associated type requirement.
  internal mutating func assign(_ i: AnyTypeIdentity, to r: AssociatedTypeDeclaration.ID) {
    associatedTypes[r.offset] = i
  }

  /// Assigns `i` to `r`, which is a member requirement.
  internal mutating func assign(_ i: DeclarationReference, to r: DeclarationIdentity) {
    members[r.offset] = i
  }

  /// Returns the member implementing `r`, which is a requirement of `concept`.
  internal func member(implementing r: DeclarationIdentity) -> DeclarationReference? {
    members[r.offset]
  }

}

extension WitnessTable: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    let a = try archive.read(Trait.ID.self, in: &context)
    let b = try archive.read(TypeArguments.self, in: &context)
    let c = try archive.read([Int: WitnessExpression].self, in: &context)
    let d = try archive.read([Int: AnyTypeIdentity].self, in: &context)
    let e = try archive.read([Int: DeclarationReference].self, in: &context)
    self.init(concept: a, arguments: b, bases: c, associatedTypes: d, members: e)
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(concept, in: &context)
    try archive.write(arguments, in: &context)
    try archive.write(bases, in: &context, sortedBy: \.key)
    try archive.write(associatedTypes, in: &context, sortedBy: \.key)
    try archive.write(members, in: &context, sortedBy: \.key)
  }

}
