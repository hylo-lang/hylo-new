import Archivist

/// A table from trait requirement to its implementation.
public struct WitnessTable: Hashable, Sendable {

  /// The trait declaring the requirements occurring as keys in this table.
  public let concept: Trait.ID

  /// The type arguments of the trait.
  public let arguments: TypeArguments

  /// A table from associated conformance requirement to its implementation.
  private var associatedConformances: [Int: WitnessExpression]

  /// A table from associated type requirement to its implementation.
  private var associatedTypes: [Int: AnyTypeIdentity]

  /// A table from member requirement to its implementation.
  private var members: [Int: DeclarationReference]

  /// Creates an empty instance.
  public init(concept: Trait.ID, arguments: TypeArguments) {
    self.concept = concept
    self.arguments = arguments
    self.associatedConformances = [:]
    self.associatedTypes = [:]
    self.members = [:]
  }

  /// `true` iff `self` witnesses a synthetic conformance that does not involve any user code.
  public var isTransitivelySynthetic: Bool {
    !members.isEmpty && members.allSatisfy(\.value.isTransitivelySynthetic)
  }

  /// Assigns `i` to the associated conformance requirement `r`.
  internal mutating func assign(_ i: WitnessExpression, to r: ConformanceDeclaration.ID) {
    associatedConformances[r.offset] = i
  }

  /// Assigns `i` to the associated type requirement `r`.
  internal mutating func assign(_ i: AnyTypeIdentity, to r: AssociatedTypeDeclaration.ID) {
    associatedTypes[r.offset] = i
  }

  /// Assigns `i` to the function or subscript requirement `r`.
  internal mutating func assign(_ i: DeclarationReference, to r: DeclarationIdentity) {
    members[r.offset] = i
  }

  /// Returns the conformance implementating the requirement `r`.
  internal func conformance(implementing r: ConformanceDeclaration.ID) -> WitnessExpression? {
    associatedConformances[r.offset]
  }

  /// Returns the member implementing the function or subscript requirement `r`.
  internal func member(implementing r: DeclarationIdentity) -> DeclarationReference? {
    members[r.offset]
  }

}

extension WitnessTable: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    let a = try archive.read(Trait.ID.self, in: &context)
    let b = try archive.read(TypeArguments.self, in: &context)
    self = .init(concept: a, arguments: b)
    self.associatedConformances = try archive.read([Int: WitnessExpression].self, in: &context)
    self.associatedTypes = try archive.read([Int: AnyTypeIdentity].self, in: &context)
    self.members = try archive.read([Int: DeclarationReference].self, in: &context)
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(concept, in: &context)
    try archive.write(arguments, in: &context)
    try archive.write(associatedConformances, in: &context, sortedBy: \.key)
    try archive.write(associatedTypes, in: &context, sortedBy: \.key)
    try archive.write(members, in: &context, sortedBy: \.key)
  }

}
