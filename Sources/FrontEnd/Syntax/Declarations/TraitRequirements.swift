/// The declarations of the requirements of a trait.
///
/// An instance of this type is an ordered set containing all the requirements defined in a trait.
/// Requirements are ordered first by their types and then by their occurrence in the syntax tree.
/// Associated types come first, followed by associated conformances, followed by function and
/// subscript requirements.
///
/// This order also defines how implementations are laid out in witness tables.
public struct TraitRequirements {

  /// The declarations in this set.
  public let all: [DeclarationIdentity]

  /// The position of the first conformance requirement in `all`.
  private let firstConformanceIndex: Int

  /// The position of the first function or subscript requirement in `all`.
  private let firstMemberIndex: Int

  /// Creates an instance with the given properties.
  public init(
    types: [AssociatedTypeDeclaration.ID],
    conformances: [ConformanceDeclaration.ID],
    members: [DeclarationIdentity]
  ) {
    var all: [DeclarationIdentity] = []
    all.reserveCapacity(types.count + conformances.count + members.count)

    for d in types { all.append(.init(d)) }
    for d in conformances { all.append(.init(d)) }
    all.append(contentsOf: members)

    self.all = all
    self.firstConformanceIndex = types.count
    self.firstMemberIndex = types.count + conformances.count
  }

  /// Associated type requirements.
  public var types: some Collection<AssociatedTypeDeclaration.ID> {
    all[0 ..< firstConformanceIndex].lazy.map { (d) in
      .init(uncheckedFrom: d.erased)
    }
  }

  /// Associated conformance requirements.
  public var conformances: some Collection<ConformanceDeclaration.ID> {
    all[firstConformanceIndex ..< firstMemberIndex].lazy.map { (d) in
      .init(uncheckedFrom: d.erased)
    }
  }

  /// Member function and subscript requirements.
  public var members: ArraySlice<DeclarationIdentity> {
    all[firstMemberIndex...]
  }

}
