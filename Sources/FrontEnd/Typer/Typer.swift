import Algorithms
import OrderedCollections
import Utilities

/// The type inference and checking algorithm of Hylo programs.
public struct Typer {

  /// The module being typed.
  public let module: Program.ModuleIdentity

  /// The program containing the module being typed.
  public internal(set) var program: Program

  /// A memoization cache for various internal operations.
  private var cache: Memos

  /// The set of declarations whose type is being computed.
  private var declarationsOnStack: Set<DeclarationIdentity>

  /// A predicate to determine whether inference steps should be logged.
  private let isLoggingEnabled: ((AnySyntaxIdentity, Program) -> Bool)?

  /// The maximum depth of a derivation during implicit search.
  private let maxImplicitDepth = 10

  /// Creates an instance assigning types to syntax trees in `m`, which is a module in `p`.
  public init(
    typing m: Program.ModuleIdentity, of p: consuming Program,
    loggingInferenceWhere isLoggingEnabled: ((AnySyntaxIdentity, Program) -> Bool)? = nil
  ) {
    self.module = m
    self.program = p
    self.cache = .init(typing: module, in: program)
    self.declarationsOnStack = []
    self.isLoggingEnabled = isLoggingEnabled
  }

  /// Type checks the top-level declarations of `self.module`.
  public mutating func apply() {
    for d in program[module].topLevelDeclarations { check(d) }
  }

  /// Returns the resources held by this instance.
  public consuming func release() -> Program {
    self.program
  }

  // MARK: Caching

  /// A memoization cache for the operations of a `Typer`.
  private struct Memos {

    /// A table mapping identifiers to declarations.
    typealias LookupTable = OrderedDictionary<String, [DeclarationIdentity]>

    /// The cache of `Typer.lookup(_:atTopLevelOf:)`.
    var moduleToIdentifierToDeclaration: [LookupTable?]

    /// The cache of `Typer.givens(atTopLevelOf:)`.
    var moduleToGivens: [[Given]?]

    /// The cache of `Typer.imports(of:in:)`.
    var sourceToImports: [[Program.ModuleIdentity]?]

    /// The cache of `Typer.extensions(visibleAtTopLevelOf:)`.
    var sourceToExtensions: [[ExtensionDeclaration.ID]?]

    /// The cache of `Typer.extensions(lexicallyIn:)`.
    var scopeToExtensions: [ScopeIdentity: [ExtensionDeclaration.ID]]

    /// The cache of `Typer.declarations(lexicallyIn:)`.
    var scopeToLookupTable: [ScopeIdentity: LookupTable]

    /// The cache of `Typer.traits(visibleFrom:)`.
    var scopeToTraits: [ScopeIdentity: [TraitDeclaration.ID]]

    /// The cache of `Typer.givens(lexicallyIn:)`.
    var scopeToGivens: [ScopeIdentity: [Given]]

    /// The cache of `Typer.summon(_:in:)`.
    var scopeToSummoned: [ScopeIdentity: [AnyTypeIdentity: [SummonResult]]]

    /// The cache of `Typer.typeOfSelf(in:)`.
    var scopeToTypeOfSelf: [ScopeIdentity: AnyTypeIdentity?]

    /// The cache of `Typer.aliasesInConformance(seenThrough:)`.
    var witnessToAliases: [WitnessExpression: [AnyTypeIdentity: AnyTypeIdentity]]

    /// The cache of `Typer.declaredType(of:)` for predefined givens.
    var predefinedGivens: [Given: AnyTypeIdentity]

    /// The cache of `Typer.standardLibraryDeclaration(_:)`.
    var standardLibraryDeclarations: [StandardLibraryEntity: DeclarationIdentity]

    /// Creates an instance for typing `m`, which is a module in `p`.
    init(typing m: Program.ModuleIdentity, in p: Program) {
      self.moduleToIdentifierToDeclaration = .init(repeating: nil, count: p.modules.count)
      self.moduleToGivens = .init(repeating: nil, count: p.modules.count)
      self.sourceToImports = .init(repeating: nil, count: p[m].sources.count)
      self.sourceToExtensions = .init(repeating: nil, count: p[m].sources.count)
      self.scopeToExtensions = [:]
      self.scopeToLookupTable = [:]
      self.scopeToTraits = [:]
      self.scopeToGivens = [:]
      self.scopeToSummoned = [:]
      self.scopeToTypeOfSelf = [:]
      self.witnessToAliases = [:]
      self.predefinedGivens = [:]
      self.standardLibraryDeclarations = [:]
    }

  }

  // MARK: Type relations

  /// Returns `true` iff `t` and `u` are equal.
  public mutating func equal(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    // Fast path: types are trivially equal.
    if t == u { return true }

    // Slow path: remove aliases.
    return program.types.dealiased(t) == program.types.dealiased(u)
  }

  /// Returns `true` iff `t` and `u` are equal modulo α-conversion.
  public mutating func unifiable(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    // Fast path: types are trivially equal.
    if t == u { return true }

    // Slow path: unify the types.
    let lhs = program.types.contextAndHead(t)
    let rhs = program.types.contextAndHead(u)

    // Map the type parameters on the RHS to those on the LHS.
    if lhs.context.parameters.count != rhs.context.parameters.count { return false }
    var a: TypeArguments = [:]
    for (p, q) in zip(rhs.context.parameters, lhs.context.parameters) {
      a[p] = .init(q)
    }

    let x = program.types.introduce(usings: lhs.context.usings, into: lhs.body)
    let y = program.types.introduce(usings: rhs.context.usings, into: rhs.body)
    return x == program.types.substitute(a, in: y)
  }

  /// Returns the types of stored parts of `t`.
  private mutating func storage(of t: AnyTypeIdentity) -> [AnyTypeIdentity]? {
    let u = program.types.reduced(t)
    switch program.types.tag(of: u) {
    case Enum.self:
      return storage(of: program.types.castUnchecked(t, to: Enum.self))
    case Struct.self:
      return storage(of: program.types.castUnchecked(t, to: Struct.self))
    case TypeApplication.self:
      return storage(of: program.types.castUnchecked(t, to: TypeApplication.self))
    case Tuple.self:
      return (program.types[t] as! Tuple).elements.map(\.type)
    default:
      return nil
    }
  }

  /// Returns the types of stored parts of `t`.
  private mutating func storage(of t: Enum.ID) -> [AnyTypeIdentity] {
    [underlyingType(of: program.types[t].declaration)]
  }

  /// Returns the types of stored parts of `t`.
  private mutating func storage(of t: Struct.ID) -> [AnyTypeIdentity] {
    program.storedProperties(of: program.types[t].declaration).map { (v) in
      typeOfName(referringTo: .init(v), statically: false)
    }
  }

  /// Returns the types of stored parts of `t`.
  private mutating func storage(of t: TypeApplication.ID) -> [AnyTypeIdentity]? {
    if let ts = storage(of: program.types[t].abstraction) {
      let a = program.types[t].arguments
      return ts.map({ (u) in program.types.substitute(a, in: u) })
    } else {
      return nil
    }
  }

  // MARK: Type checking

  /// Type checks `d`.
  private mutating func check(_ d: DeclarationIdentity) {
    switch program.tag(of: d) {
    case AssociatedTypeDeclaration.self:
      check(castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case BindingDeclaration.self:
      check(castUnchecked(d, to: BindingDeclaration.self))
    case ConformanceDeclaration.self:
      check(castUnchecked(d, to: ConformanceDeclaration.self))
    case EnumCaseDeclaration.self:
      check(castUnchecked(d, to: EnumCaseDeclaration.self))
    case EnumDeclaration.self:
      check(castUnchecked(d, to: EnumDeclaration.self))
    case ExtensionDeclaration.self:
      check(castUnchecked(d, to: ExtensionDeclaration.self))
    case FunctionBundleDeclaration.self:
      check(castUnchecked(d, to: FunctionBundleDeclaration.self))
    case FunctionDeclaration.self:
      check(castUnchecked(d, to: FunctionDeclaration.self))
    case GenericParameterDeclaration.self:
      check(castUnchecked(d, to: GenericParameterDeclaration.self))
    case ParameterDeclaration.self:
      check(castUnchecked(d, to: ParameterDeclaration.self))
    case StructDeclaration.self:
      check(castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      check(castUnchecked(d, to: TraitDeclaration.self))
    case TypeAliasDeclaration.self:
      check(castUnchecked(d, to: TypeAliasDeclaration.self))
    case UsingDeclaration.self:
      check(castUnchecked(d, to: UsingDeclaration.self))
    case VariableDeclaration.self:
      break
    default:
      program.unexpected(d)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: AssociatedTypeDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO: Bounds
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`, which occurs as a condition item iff `conditional` is true.
  ///
  /// If `conditional` is `true`, then `d` occurs in the condition of a 
  private mutating func check(_ d: BindingDeclaration.ID) {
    let t = declaredType(of: d)

    switch program[d].role {
    case .condition:
      if let i = program[d].initializer {
        check(i)
      } else {
        report(.error, "binding declaration requires an initializer", about: d)
      }

    case .given, .unconditional:
      if let i = program[d].initializer {
        check(i, requiring: t)
      }
    }

    program.forEachVariable(introducedBy: d) { (v, _) in
      checkUniqueDeclaration(v, of: program[v].identifier.value)
    }

    if program[d].role == .given, let p = program.parent(containing: d).node {
      switch program.tag(of: p) {
      case ConformanceDeclaration.self, TraitDeclaration.self:
        break
      default:
        report(.error, "givens type definitions are not supported yet", about: d)
      }
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: ConformanceDeclaration.ID) {
    let t = declaredType(of: d)

    check(program[d].staticParameters)

    // Abstract conformance declarations can only occur in traits.
    guard let members = program[d].members else {
      if !program.isRequirement(d) {
        report(.error, "abstract givens can only be declared in a trait", about: d)
      }
      return
    }

    for m in members { check(m) }

    // The type of the declaration has the form `<T...> A... ==> P<B...>` where `P<B...>` is the
    // type of the declared witness and the rest forms a context. Requirements are resolved as
    // members of the type `B` where type parameters occur as skolems.
    let witnessSansContext = program.types.contextAndHead(t).body
    guard let witness = program.types.seenAsTraitApplication(witnessSansContext) else {
      assert(t[.hasError])
      return
    }

    let concept = program.types[witness.concept].declaration
    let conformer = witness.arguments.values[0]
    let qualification = demand(Metatype(inhabitant: conformer)).erased

    // The expected types of implementations satisfying the concept's requirements are computed by
    // substituting the abstract types of the concept by their corresponding assignment.
    var substitutions = Dictionary(
      uniqueKeysWithValues: witness.arguments.elements.map({ (k, v) in (k.erased, v) }))

    let (requirements, associatedTypes) = program[concept].members.partitioned { (r) in
      program.tag(of: r) == AssociatedTypeDeclaration.self
    }

    // Find the implementations of associated types in the conformance declaration itself.
    for r in associatedTypes {
      let a = program.castUnchecked(r, to: AssociatedTypeDeclaration.self)
      let i = self.implementation(of: a, in: d).map({ (i) in declaredType(of: i) }) ?? .error

      if let m = program.types[i] as? Metatype {
        let k0 = declaredType(of: a)
        let k1 = program.types[k0] as! Metatype
        substitutions[k1.inhabitant] = m.inhabitant
      } else {
        return reportMissingImplementation(of: a, in: d)
      }
    }

    // Check that other requirements may be satisfied. We do not need to store the implementations
    // since witness tables are built on demand.
    for r in requirements {
      switch program.tag(of: r) {
      case ConformanceDeclaration.self:
        _ = anonymousImplementation(of: r)

      case FunctionDeclaration.self:
        _ = namedImplementation(of: r)

      case FunctionBundleDeclaration.self:
        let b = program.castUnchecked(r, to: FunctionBundleDeclaration.self)
        for v in program[b].variants {
          _ = namedImplementation(of: .init(v))
        }

      default:
        program.unexpected(r)
      }
    }

    /// Returns the declarations implementing `requirement`.
    func namedImplementation(of requirement: DeclarationIdentity) -> DeclarationReference? {
      let requiredName = program.name(of: requirement)!
      let requiredType = expectedImplementationType(of: requirement)

      var viable: [DeclarationReference] = []

      // Is there a unique implementation in the conformance declaration?
      for c in lookup(requiredName, lexicallyIn: .init(node: d)) {
        let candidateType = declaredType(of: c)
        if unifiable(candidateType, requiredType) { viable.append(.direct(c)) }
      }

      if viable.isEmpty {
        // Is there an implementation that is already member of the conforming type?
        for c in resolve(requiredName, memberOf: qualification, visibleFrom: .init(node: d)) {
          if !unifiable(c.type, requiredType) { continue }

          // If we resolved the requirement, make sure it has a default implementation.
          switch c.reference {
          case .inherited(_, requirement) where !hasDefinition(requirement):
            continue
          default:
            viable.append(c.reference)
          }
        }
      }

      if let pick = viable.uniqueElement {
        return pick
      } else if viable.count > 1 {
        reportAmbiguousImplementation(of: requiredName, in: d)
        return nil
      } else if let pick = syntheticImplementation(of: requirement, in: d, for: conformer) {
        return pick
      } else {
        reportMissingImplementation(of: requiredName, in: d)
        return nil
      }
    }

    /// Returns the declarations implementing `requirement`.
    func anonymousImplementation(of requirement: DeclarationIdentity) -> SummonResult? {
      let requiredType = expectedImplementationType(of: requirement)

      var summonings = summon(requiredType, in: .init(node: d))
      let i = summonings.stablePartition { (c) in
        c.witness.declaration == requirement
      }

      let s = program.spanForDiagnostic(about: d)
      if i == 1 {
        return summonings[0]
      } else if i == 0 {
        report(program.noGivenInstance(of: requiredType, at: s))
        return nil
      } else {
        report(program.multipleGivenInstances(of: requiredType, at: s))
        return nil
      }
    }

    /// Returns the expected type of an implementation of `requirement`.
    func expectedImplementationType(of requirement: DeclarationIdentity) -> AnyTypeIdentity {
      let t = declaredType(of: requirement)
      return program.types.substitute(substitutions, in: t)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: EnumCaseDeclaration.ID) {
    _ = declaredType(of: d)
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: EnumDeclaration.ID) {
    _ = declaredType(of: d)

    if let e = program[d].representation {
      let s = program.spanForDiagnostic(about: e)
      report(.init(.error, "raw representations are not supported yet", at: s))
    }

    for m in program[d].members { check(m) }
    for c in program[d].conformances { check(c) }
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: ExtensionDeclaration.ID) {
    _ = extendeeType(d)
    for m in program[d].members { check(m) }
  }

  /// Type checks `d`.
  private mutating func check(_ d: FunctionBundleDeclaration.ID) {
    _ = declaredType(of: d)

    check(program[d].staticParameters)
    check(program[d].parameters)
    for v in program[d].variants { check(v) }

    // TODO: Redeclarations
  }

  /// Type checks `d`.
  private mutating func check(_ d: FunctionDeclaration.ID) {
    let t = declaredType(of: d)

    // Nothing more to do if the declaration doesn't have an arrow type.
    if let a = program.types[program.types.head(t)] as? Arrow {
      check(program[d].staticParameters)
      check(program[d].parameters)
      check(body: program[d].body, of: .init(d), expectingOutputType: a.output)
    }

    // TODO: Redeclarations
  }

  /// Type checks `d`.
  private mutating func check(_ d: GenericParameterDeclaration.ID) {
    _ = declaredType(of: d)
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `body` as the definition of `d`, which declares a function or susbscript that
  /// outputs an instance of `r`.
  private mutating func check(
    body: [StatementIdentity]?, of d: DeclarationIdentity,
    expectingOutputType r: AnyTypeIdentity
  ) {
    if let b = body {
      // Is the function single-expression bodied?
      if let s = singleReturn(of: b) {
        check(s, requiring: r)
      } else {
        for s in b { check(s) }
      }
    } else if requiresDefinition(d) {
      // Only requirements, FFIs, and external functions can be without a body.
      let s = program.spanForDiagnostic(about: d)
      report(.init(.error, "declaration requires a body", at: s))
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: ParameterDeclaration.ID) {
    let ascription = declaredType(of: d)

    // Bail out if the ascription has an error.
    guard let a = program.types[ascription] as? RemoteType else {
      assert(ascription[.hasError])
      return
    }

    if let v = program[d].defaultValue {
      check(v, requiring: a.projectee)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: StructDeclaration.ID) {
    _ = declaredType(of: d)
    for m in program[d].members { check(m) }
    for c in program[d].conformances { check(c) }
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: TraitDeclaration.ID) {
    _ = declaredType(of: d)
    for m in program[d].members {
      check(m)
      if let a = program.modifiers(m).first(where: { (x) in x.value.isAccessModifier }) {
        report(.init(.error, "cannot apply access modifiers on trait requirements", at: a.site))
      }
    }
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: TypeAliasDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
    checkUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: UsingDeclaration.ID) {
    _ = declaredType(of: d)
  }

  /// Type checks `d`.
  private mutating func check(_ d: VariantDeclaration.ID) {
    let t = declaredType(of: d)

    if let a = program.types[program.types.head(t)] as? Arrow {
      check(body: program[d].body, of: .init(d), expectingOutputType: a.output)
    } else {
      assert(t[.hasError])
    }
  }

  /// Type checks `ps`.
  private mutating func check(_ ps: [ParameterDeclaration.ID]) {
    var siblings: [String: ParameterDeclaration.ID] = .init(minimumCapacity: ps.count)
    for p in ps {
      check(p)

      // Check for duplicate parameters.
      modify(&siblings[program[p].identifier.value]) { (q) in
        if let previous = q {
          let e = program.invalidRedeclaration(
            of: .init(identifier: program[p].identifier.value),
            at: program.spanForDiagnostic(about: p),
            previousDeclarations: [program.spanForDiagnostic(about: previous)])
          report(e)
        } else {
          q = p
        }
      }
    }
  }

  /// Type checks `ps`.
  private mutating func check(_ ps: StaticParameters) {
    for p in ps.explicit { check(p) }
    for p in ps.implicit { check(p) }
  }

  /// Type checks `n`.
  private mutating func check(_ n: ConditionIdentity) {
    if let d = program.cast(n, to: BindingDeclaration.self) {
      check(d)
    } else if let e = program.castToExpression(n) {
      let t = standardLibraryType(.bool)
      check(e, requiring: t)
    } else {
      program.unexpected(n)
    }
  }

  /// Returns `true` iff `d` has a definition.
  private func hasDefinition(_ d: DeclarationIdentity) -> Bool {
    switch program.tag(of: d) {
    case BindingDeclaration.self:
      return program[program.castUnchecked(d, to: BindingDeclaration.self)].initializer != nil
    case FunctionDeclaration.self:
      return program[program.castUnchecked(d, to: FunctionDeclaration.self)].body != nil
    case VariantDeclaration.self:
      return program[program.castUnchecked(d, to: VariantDeclaration.self)].body != nil
    default:
      return false
    }
  }

  /// Returns `true` iff `d` needs a user-defined a definition.
  ///
  /// A declaration requires a definition unless it is a trait requirement, an FFI, an external
  /// function, or a memberwise initializer.
  private func requiresDefinition(_ d: DeclarationIdentity) -> Bool {
    switch program.tag(of: d) {
    case FunctionDeclaration.self:
      let f = program.castUnchecked(d, to: FunctionDeclaration.self)
      return !program.isRequirement(f)
        && !program.isForeign(f) && !program.isExtern(f) && !program[f].isMemberwiseInitializer

    default:
      return !program.isRequirement(d)
    }
  }

  /// Returns the declaration implementing `requirement` in `d`, if any.
  private mutating func implementation(
    of requirement: AssociatedTypeDeclaration.ID, in d: ConformanceDeclaration.ID
  ) -> DeclarationIdentity? {
    let n = Name(identifier: program[requirement].identifier.value)
    return lookup(n, lexicallyIn: .init(node: d)).uniqueElement
  }

  /// Returns an implementation of `requirement` for `conformer` iff one can be synthesized.
  private mutating func syntheticImplementation(
    of requirement: DeclarationIdentity,
    in d: ConformanceDeclaration.ID,
    for conformer: AnyTypeIdentity
  ) -> DeclarationReference? {
    let concept = program.traitRequiring(requirement)!
    if
      isStructurallySynthesizable(conformanceTo: concept),
      structurallyConforms(storageOf: conformer, to: concept, in: .init(node: d))
    {
      return .synthetic(requirement)
    } else if isBuiltin(conformanceOf: conformer, to: concept) {
      return .synthetic(requirement)
    } else {
      return nil
    }
  }

  /// Returns `true` iff the conformance of a whole to `concept` may be synthesized from the
  /// conformances of its parts.
  private mutating func isStructurallySynthesizable(
    conformanceTo concept: TraitDeclaration.ID
  ) -> Bool {
    guard program.containsStandardLibrarySources else { return false }
    switch concept {
    case standardLibraryDeclaration(.deinitializable):
      return true
    case standardLibraryDeclaration(.equatable):
      return true
    case standardLibraryDeclaration(.movable):
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff there exists a buil-in conformance of `conformer` to `concept`.
  private mutating func isBuiltin(
    conformanceOf conformer: AnyTypeIdentity, to concept: TraitDeclaration.ID
  ) -> Bool {
    guard program.containsStandardLibrarySources else { return false }
    switch concept {
    case standardLibraryDeclaration(.expressibleByIntegerLiteral):
      return isStandardLibraryIntegerType(conformer)
    default:
      return false
    }
  }

  /// Returns `true` iff conformances of each stored part of `conformer` to `concept` can be
  /// derived (i.e., resolved or synthesized) in `scopeOfUse`.
  ///
  /// - Requires: conformances to `concept` may be synthesized.
  private mutating func structurallyConforms(
    storageOf conformer: AnyTypeIdentity, to concept: TraitDeclaration.ID,
    in scopeOfUse: ScopeIdentity
  ) -> Bool {
    if let s = storage(of: conformer) {
      return s.allSatisfy({ (t) in isDerivable(conformanceOf: t, to: concept, in: scopeOfUse) })
    } else {
      return false
    }
  }

  /// Returns `true` iff conformances of each stored part of `conformer` to `concept` can be
  /// derived (i.e., resolved or synthesized) in `scopeOfUse`.
  ///
  /// - Requires: conformances to `concept` may be synthesized.
  private mutating func structurallyConforms(
    _ conformer: Sum.ID, to concept: TraitDeclaration.ID,
    in scopeOfUse: ScopeIdentity
  ) -> Bool {
    program.types[conformer].elements.allSatisfy { (e) in
      isDerivable(conformanceOf: e, to: concept, in: scopeOfUse)
    }
  }

  /// Returns `true` iff conformances of each stored part of `conformer` to `concept` can be
  /// derived (i.e., resolved or synthesized) in `scopeOfUse`.
  ///
  /// - Requires: conformances to `concept` may be synthesized.
  private mutating func structurallyConforms(
    _ conformer: Tuple.ID, to concept: TraitDeclaration.ID,
    in scopeOfUse: ScopeIdentity
  ) -> Bool {
    program.types[conformer].elements.allSatisfy { (e) in
      isDerivable(conformanceOf: e.type, to: concept, in: scopeOfUse)
    }
  }

  /// Returns `true` iff a conformance of `conformer` to `concept` can be resolved or synthesized
  /// in `scopeOfUse`.
  private mutating func isDerivable(
    conformanceOf conformer: AnyTypeIdentity, to concept: TraitDeclaration.ID,
    in scopeOfUse: ScopeIdentity
  ) -> Bool {
    assert(isStructurallySynthesizable(conformanceTo: concept))
    if program.types[conformer] is MachineType {
      return true
    }

    let a = typeOfModel(of: conformer, conformingTo: concept, with: []).erased
    if summon(a, in: scopeOfUse).count == 1 {
      return true
    } else if let s = program.types.cast(conformer, to: Sum.self) {
      return structurallyConforms(s, to: concept, in: scopeOfUse)
    } else if let s = program.types.cast(conformer, to: Tuple.self) {
      return structurallyConforms(s, to: concept, in: scopeOfUse)
    } else {
      return false
    }
  }

  /// Reports that `requirement` has no implementation.
  private mutating func reportMissingImplementation(
    of requirement: AssociatedTypeDeclaration.ID,
    in conformance: ConformanceDeclaration.ID
  ) {
    let n = program[requirement].identifier.value
    let m = "no implementation of associated type requirement '\(n)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: conformance)))
  }

  /// Reports that `requirement` has no implementation.
  private mutating func reportMissingImplementation(
    of requirement: Name,
    in conformance: ConformanceDeclaration.ID
  ) {
    let m = "no implementation of '\(requirement)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: conformance)))
  }

  /// Reports that `requirement` has multiple equally valid implementations.
  private mutating func reportAmbiguousImplementation(
    of requirement: Name,
    in conformance: ConformanceDeclaration.ID
  ) {
    let m = "ambiguous implementation of '\(requirement)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: conformance)))
  }

  /// Reports a diagnostic iff `d` is not the first declaration of `identifier` in its scope.
  private mutating func checkUniqueDeclaration<T: Declaration>(_ d: T.ID, of identifier: String) {
    let parent = program.parent(containing: d)
    let ts = if parent.isFile {
      lookup(.init(identifier: identifier), atTopLevelOf: parent.module)
    } else {
      lookup(.init(identifier: identifier), lexicallyIn: parent)
    }

    if (ts.count > 1) && (ts[0].erased != d.erased) && program.occurInOrder(ts[0], d) {
      let e = program.invalidRedeclaration(
        of: .init(identifier: identifier), at: program.spanForDiagnostic(about: d),
        previousDeclarations: [program.spanForDiagnostic(about: ts[0])])
      report(e)
    }
  }

  /// Reports a diagnostic iff `p` is the metatype of a higher-kinded type constructor.
  private mutating func checkProper(_ p: GenericParameter.ID, at site: SourceSpan) {
    if program.types[p].kind != .proper {
      let e = program.invalidTypeArguments(
        toApply: program.show(p), found: 0, expected: program.types.parameters(of: p).count,
        at: site)
      report(e)
    }
  }

  /// Type checks `e` and returns its type, which is expected to be `r` from the context of `e`.
  @discardableResult
  private mutating func check(
    _ e: ExpressionIdentity, inContextExpecting r: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    if let t = program[e.module].type(assignedTo: e) {
      return t
    } else {
      var c = InferenceContext(expectedType: r)
      let t = inferredType(of: e, in: &c)
      let s = discharge(c.obligations, relatedTo: e)
      return program.types.reify(t, applying: s.substitutions)
    }
  }

  /// Type checks `e` and returns its type, reporting an error if it isn't coercible to `r`.
  @discardableResult
  private mutating func check(
    _ e: ExpressionIdentity, requiring r: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    var c = InferenceContext(expectedType: r)
    let t = program[e.module].type(assignedTo: e) ?? inferredType(of: e, in: &c)

    // Make sure `e` can be coerced to the required type unless it is trivially equal or type
    // inference already failed.
    if !equal(t, r) && !c.obligations.isUnsatisfiable {
      c.obligations.assume(CoercionConstraint(on: e, from: t, to: r, at: program[e].site))
    }

    discharge(c.obligations, relatedTo: e)
    return r
  }

  /// Type checks `e`, which occurs as a statement.
  private mutating func checkAsStatement(_ e: ExpressionIdentity) {
    let u = check(e, inContextExpecting: .void)
    if !equal(u, .void) && !u[.hasError] {
      let m = program.format("unused value of type %T", [u])
      report(.init(.error, m, at: program[e].site))
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: StatementIdentity) {
    switch program.tag(of: s) {
    case Assignment.self:
      check(program.castUnchecked(s, to: Assignment.self))
    case Discard.self:
      check(program.castUnchecked(s, to: Discard.self))
    case Return.self:
      check(program.castUnchecked(s, to: Return.self))
    case _ where program.isExpression(s):
      checkAsStatement(ExpressionIdentity(uncheckedFrom: s.erased))
    case _ where program.isDeclaration(s):
      check(DeclarationIdentity(uncheckedFrom: s.erased))
    default:
      program.unexpected(s)
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: Assignment.ID) {
    let l = check(program[s].lhs)
    check(program[s].rhs, requiring: l)
    program[module].setType(.void, for: s)
  }

  /// Type checks `s`.
  private mutating func check(_ s: Discard.ID) {
    check(program[s].value)
    program[module].setType(.void, for: s)
  }

  /// Type checks `s`.
  private mutating func check(_ s: Return.ID) {
    if let u = expectedOutputType(in: program.parent(containing: s)) {
      check(s, requiring: u)
    } else if let v = program[s].value {
      check(v)
      program[module].setType(.void, for: s)
    }
  }

  /// Type checks `s`, expecting that it returns a value of type `u`.
  private mutating func check(_ s: Return.ID, requiring u: AnyTypeIdentity) {
    if let v = program[s].value {
      check(v, requiring: u)
    } else if !equal(u, .void) {
      let m = program.format("expected value of type '%T'", [u])
      let s = program.spanForDiagnostic(about: s)
      report(.init(.error, m, at: s))
    }

    program[module].setType(.void, for: s)
  }

  /// Returns the declared type of `d` without type checking its contents.
  private mutating func declaredType(of d: DeclarationIdentity) -> AnyTypeIdentity {
    switch program.tag(of: d) {
    case AssociatedTypeDeclaration.self:
      return declaredType(of: castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case BindingDeclaration.self:
      return declaredType(of: castUnchecked(d, to: BindingDeclaration.self))
    case ConformanceDeclaration.self:
      return declaredType(of: castUnchecked(d, to: ConformanceDeclaration.self))
    case EnumCaseDeclaration.self:
      return declaredType(of: castUnchecked(d, to: EnumCaseDeclaration.self))
    case EnumDeclaration.self:
      return declaredType(of: castUnchecked(d, to: EnumDeclaration.self))
    case FunctionBundleDeclaration.self:
      return declaredType(of: castUnchecked(d, to: FunctionBundleDeclaration.self))
    case FunctionDeclaration.self:
      return declaredType(of: castUnchecked(d, to: FunctionDeclaration.self))
    case GenericParameterDeclaration.self:
      return declaredType(of: castUnchecked(d, to: GenericParameterDeclaration.self))
    case ParameterDeclaration.self:
      return declaredType(of: castUnchecked(d, to: ParameterDeclaration.self))
    case StructDeclaration.self:
      return declaredType(of: castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      return declaredType(of: castUnchecked(d, to: TraitDeclaration.self))
    case TypeAliasDeclaration.self:
      return declaredType(of: castUnchecked(d, to: TypeAliasDeclaration.self))
    case VariableDeclaration.self:
      return declaredType(of: castUnchecked(d, to: VariableDeclaration.self))
    case UsingDeclaration.self:
      return declaredType(of: castUnchecked(d, to: UsingDeclaration.self))
    case VariantDeclaration.self:
      return declaredType(of: castUnchecked(d, to: VariantDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: AssociatedTypeDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let c = program.parent(containing: d, as: TraitDeclaration.self)!
    let t = typeOfTraitSelf(in: c).erased
    let w = WitnessExpression(value: .abstract, type: t)
    let u = metatype(of: AssociatedType(declaration: d, qualification: w)).erased
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d`, using inference if necessary.
  private mutating func declaredType(of d: BindingDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    // Is it the first time we enter this method for `d`?
    if declarationsOnStack.insert(.init(d)).inserted {
      defer { declarationsOnStack.remove(.init(d)) }

      var c = InferenceContext()
      let p = inferredType(of: d, in: &c)
      let s = discharge(c.obligations, relatedTo: d)
      let u = program.types.reify(p, applying: s.substitutions)

      ascribe(.let, u, to: program[d].pattern)
      program[module].setType(u, for: d)
      return u
    }

    // Cyclic reference detected.
    else {
      let s = program[program[program[d].pattern].pattern].site
      report(.init(.error, "declaration refers to itself", at: s))
      return .error
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: ConformanceDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    // Is it the first time we enter this method for `d`?
    if declarationsOnStack.insert(.init(d)).inserted {
      defer { declarationsOnStack.remove(.init(d)) }

      initializeContext(program[d].staticParameters)
      let t = evaluateTypeAscription(.init(program[d].witness))
      let u = introduce(program[d].staticParameters, into: t)
      program[module].setType(u, for: d)
      return u
    }

    // Cyclic reference detected.
    else {
      let s = program.spanForDiagnostic(about: d)
      report(.init(.error, "declaration refers to itself", at: s))
      return .error
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: EnumCaseDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    // The enclosing scope is an enum declaration.
    let o = typeOfSelf(in: program.parent(containing: d, as: EnumDeclaration.self)!)
    let i = declaredTypes(of: program[d].parameters, defaultConvention: .sink)
    let a = demand(Arrow(effect: .let, environment: .void, inputs: i, output: o)).erased
    program[module].setType(a, for: d)
    return a
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: EnumDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let ps = declaredTypes(of: program[d].staticParameters.explicit)
    if let i = program[d].staticParameters.implicit.first {
      let s = program.spanForDiagnostic(about: i)
      report(.init(.error, "context parameters in type definitions are not supported yet", at: s))
    }

    var s = demand(Enum(declaration: d)).erased
    if !ps.isEmpty {
      let a = TypeArguments(parametersWithValues: ps.map({ (p) in (p, p.erased) }))
      let t = demand(TypeApplication(abstraction: s, arguments: a)).erased
      s = demand(UniversalType(parameters: ps, body: t)).erased
    }

    let t = demand(Metatype(inhabitant: s)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionBundleDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    initializeContext(program[d].staticParameters)
    let variants = AccessEffectSet(program[d].variants.map(program.read(\.effect.value)))
    let inputs = declaredTypes(of: program[d].parameters)
    let shape = declaredArrowType(of: d, taking: inputs)

    let (context, head) = program.types.contextAndHead(shape)
    let bundle = demand(Bundle(shape: head, variants: variants)).erased
    let result = program.types.introduce(context, into: bundle)

    program[module].setType(result, for: d)
    return result
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    initializeContext(program[d].staticParameters)
    var inputs: [Parameter] = []

    // Do we have to synthesize the parameter list of a memberwise initializer?
    if program[d].isMemberwiseInitializer {
      // Memberwise initializers can only appear nested in a struct declaration.
      let s = program.parent(containing: d, as: StructDeclaration.self)!
      let r = typeOfSelf(in: s)
      inputs.append(.init(label: "self", access: .set, type: r))

      // We don't use `program.storedProperties(of:)` because we have to ensure that all stored
      // properties are typed before we can form a corresponding parameter.
      for b in program.collect(BindingDeclaration.self, in: program[s].members) {
        _ = declaredType(of: b)
        program.forEachVariable(introducedBy: b) { (v, _) in
          let t = program[module].type(assignedTo: b) ?? .error
          inputs.append(Parameter(label: program[v].identifier.value, access: .sink, type: t))
        }
      }
    }

    // Otherwise, parameters are in the syntax.
    else {
      inputs = declaredTypes(of: program[d].parameters)
    }

    let result = declaredArrowType(of: d, taking: inputs)
    program[module].setType(result, for: d)
    return result
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: GenericParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let k = declaredKind(of: d)
    let t = metatype(of: GenericParameter.user(d, k)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: ParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = program[d].ascription.map({ (a) in evaluateTypeAscription(.init(a)) }) ?? {
      report(.error, "parameter declaration requires an ascription", about: d)
      return .error
    }()

    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: StructDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let ps = declaredTypes(of: program[d].staticParameters.explicit)
    if let i = program[d].staticParameters.implicit.first {
      let s = program.spanForDiagnostic(about: i)
      report(.init(.error, "context parameters in type definitions are not supported yet", at: s))
    }

    var s = demand(Struct(declaration: d)).erased
    if !ps.isEmpty {
      let a = TypeArguments(parametersWithValues: ps.map({ (p) in (p, p.erased) }))
      let t = demand(TypeApplication(abstraction: s, arguments: a)).erased
      s = demand(UniversalType(parameters: ps, body: t)).erased
    }

    let t = demand(Metatype(inhabitant: s)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TraitDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    var ps = [typeOfSelf(in: d)]
    ps.append(contentsOf: declaredTypes(of: program[d].parameters))

    let a = TypeArguments(parametersWithValues: ps.map({ (p) in (p, p.erased) }))
    let f = demand(Trait(declaration: d)).erased
    let t = demand(TypeApplication(abstraction: f, arguments: a)).erased
    let u = metatype(of: UniversalType(parameters: ps, body: t)).erased
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TypeAliasDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    // Is it the first time we enter this method for `d`?
    if declarationsOnStack.insert(.init(d)).inserted {
      defer { declarationsOnStack.remove(.init(d)) }

      switch evaluateTypeAscription(program[d].aliasee) {
      case .error:
        program[module].setType(.error, for: d)
        return .error
      case let aliasee:
        let t = metatype(of: TypeAlias(declaration: d, aliasee: aliasee)).erased
        program[module].setType(t, for: d)
        return t
      }
    }

    // Cyclic reference detected.
    else {
      let n = program[d].identifier
      report(.init(.error, "definition of '\(n)' refers to itself", at: n.site))
      return .error
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: VariableDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    // Variable declarations outside of a binding declaration are typed through their containing
    // pattern, which is visited before any reference to the variable can be formed.
    let b = program.bindingDeclaration(containing: d) ?? unreachable("pattern is not typed")
    _ = declaredType(of: b)
    return program[module].type(assignedTo: d) ?? .error
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: UsingDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = evaluateTypeAscription(program[d].witness)
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: VariantDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let parent = program.castToDeclaration(program.parent(containing: d).node!)!
    let bundle = declaredType(of: parent)
    let (context, head) = program.types.contextAndHead(bundle)

    let shape = program.types.select(head, \Bundle.shape) ?? .error
    switch program.types.tag(of: shape) {
    case Arrow.self:
      let t = Arrow.ID(uncheckedFrom: shape)
      let u = program.types.variant(program[d].effect.value, of: t).erased
      program[module].setType(u, for: d)
      return program.types.introduce(context, into: u)

    default:
      assert(bundle[.hasError])
      program[module].setType(.error, for: d)
      return .error
    }
  }

  /// Returns the declared properties of the parameters in `ds` without checking.
  private mutating func declaredTypes(
    of ps: [ParameterDeclaration.ID], defaultConvention k: AccessEffect = .let
  ) -> [Parameter] {
    var result: [Parameter] = []
    for p in ps {
      let t = declaredType(of: p)

      let access: AccessEffect
      let projectee: AnyTypeIdentity
      if let u = program.types[t] as? RemoteType {
        access = u.access
        projectee = u.projectee
      } else {
        access = k
        projectee = .error
      }

      result.append(
        Parameter(
          label: program[p].label?.value, access: access, type: projectee,
          defaultValue: program[p].defaultValue))
    }
    return result
  }

  /// Returns the declared types of `ps` without checking.
  private mutating func declaredTypes(
    of ps: [GenericParameterDeclaration.ID]
  ) -> [GenericParameter.ID] {
    ps.compactMap { (p) in
      let t = declaredType(of: p)
      return program.types.select(t, \Metatype.inhabitant, as: GenericParameter.self)
    }
  }

  /// Returns the declared type of `d`, which introduces a function that accepts `inputs`.
  private mutating func declaredArrowType<T: RoutineDeclaration>(
    of d: T.ID, taking inputs: [Parameter],
  ) -> AnyTypeIdentity {
    let o = program[d].output.map({ (a) in evaluateTypeAscription(a) }) ?? .void
    let a = demand(
      Arrow(effect: program[d].effect.value, environment: .void, inputs: inputs, output: o))
    return introduce(program[d].staticParameters, into: a.erased)
  }

  /// Returns the declared type of `g` without checking.
  private mutating func declaredType(of g: Given) -> AnyTypeIdentity {
    if let predefined = cache.predefinedGivens[g] { return predefined }

    let result: AnyTypeIdentity
    switch g {
    case .user(let d):
      return declaredType(of: d)

    case .nested(let p, let d):
      let c = contextOfSelf(in: p)
      let t = declaredType(of: d)
      let u = program.types.introduce(c, into: t)
      return u

    case .abstract(let t):
      return t

    case .assumed(_, let t):
      return t

    case .coercion(.reflexivity):
      // <T> T ~ T
      let t0 = demand(GenericParameter.nth(0, .proper))
      let x0 = demand(EqualityWitness(lhs: t0.erased, rhs: t0.erased)).erased
      result = demand(UniversalType(parameters: [t0], body: x0)).erased

    case .coercion(.symmetry):
      // <T0, T1> T0 ~ T1 ==> T1 ~ T0
      let t0 = demand(GenericParameter.nth(0, .proper))
      let t1 = demand(GenericParameter.nth(1, .proper))
      let x0 = demand(EqualityWitness(lhs: t0.erased, rhs: t1.erased)).erased
      let x1 = demand(EqualityWitness(lhs: t1.erased, rhs: t0.erased)).erased
      let x2 = demand(Implication(context: [x0], head: x1)).erased
      result = demand(UniversalType(parameters: [t0, t1], body: x2)).erased

    case .coercion(.transitivity):
      // <T0, T1, T2> T0 ~ T1, T1 ~ T2 ==> T0 ~ T2
      let t0 = demand(GenericParameter.nth(0, .proper))
      let t1 = demand(GenericParameter.nth(1, .proper))
      let t2 = demand(GenericParameter.nth(2, .proper))
      let x0 = demand(EqualityWitness(lhs: t0.erased, rhs: t1.erased)).erased
      let x1 = demand(EqualityWitness(lhs: t1.erased, rhs: t2.erased)).erased
      let x2 = demand(EqualityWitness(lhs: t0.erased, rhs: t2.erased)).erased
      let x3 = demand(Implication(context: [x0, x1], head: x2)).erased
      result = demand(UniversalType(parameters: [t0, t1, t2], body: x3)).erased
    }

    cache.predefinedGivens[g] = result
    return result
  }

  /// Returns the type of `requirement` seen through a conformance witnessed by `witness`.
  private mutating func declaredType(
    of requirement: DeclarationIdentity, seenThrough witness: WitnessExpression
  ) -> AnyTypeIdentity {
    let substitutions = aliasesInConformance(seenThrough: witness)
    let member = declaredType(of: requirement)
    let memberSansContext = program.types.head(member)
    return program.types.substitute(substitutions, in: memberSansContext)
  }

  /// Returns a table mapping abstract types to their implementations in the conformance witnessed
  /// by `witness`.
  private mutating func aliasesInConformance(
    seenThrough witness: WitnessExpression
  ) -> [AnyTypeIdentity: AnyTypeIdentity] {
    if let memoized = cache.witnessToAliases[witness] { return memoized }

    let w = program.types.seenAsTraitApplication(witness.type)!
    var substitutions = Dictionary(
      uniqueKeysWithValues: w.arguments.elements.map({ (k, v) in (k.erased, v) }))

    for r in program[program.types[w.concept].declaration].members {
      if let a = program.cast(r, to: AssociatedTypeDeclaration.self) {
        let i = typeOfImplementation(satisfying: a, in: witness)
        if let m = program.types[i] as? Metatype {
          let k0 = declaredType(of: r)
          let k1 = program.types[k0] as! Metatype
          substitutions[k1.inhabitant] = m.inhabitant
        }
      }
    }

    assert(!witness.hasVariable)
    cache.witnessToAliases[witness] = substitutions
    return substitutions
  }

  /// Returns the declared kind of `d`.
  private mutating func declaredKind(of d: GenericParameterDeclaration.ID) -> Kind {
    if let a = program[d].ascription {
      let k = evaluateKindAscription(a)
      return program.types[k].inhabitant
    } else {
      // Generic parameters are proper-kinded by default.
      return .proper
    }
  }

  /// Returns the type that `d` extends.
  private mutating func extendeeType(_ d: ExtensionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    initializeContext(program[d].staticParameters)
    let t = ignoring(d, { (me) in me.evaluateTypeAscription(me.program[d].extendee) })
    let u = introduce(program[d].staticParameters, into: t)
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the type used to represent instances of the given enumeration.
  internal mutating func underlyingType(of d: EnumDeclaration.ID) -> AnyTypeIdentity {
    if let e = program[d].representation {
      return check(e)
    } else {
      var elements: [AnyTypeIdentity] = []
      for m in program[d].members {
        guard let c = program.cast(m, to: EnumCaseDeclaration.self) else { continue }
        elements.append(underlyingType(of: c).erased)
      }
      return demand(Sum(elements: elements)).erased
    }
  }

  /// Returns the type used to represent an instance of the given case.
  private mutating func underlyingType(of d: EnumCaseDeclaration.ID) -> Tuple.ID {
    let elements = program[d].parameters.map { (p) -> Tuple.Element in
      let t = declaredType(of: p)
      let u = (program.types[t] as? RemoteType)?.projectee ?? .error
      return .init(label: program[p].identifier.value, type: u)
    }
    return demand(Tuple(elements: elements))
  }

  /// Computes the types of the given context parameters, introducing them in order.
  private mutating func initializeContext(_ parameters: StaticParameters) {
    declarationsOnStack.formUnion(parameters.implicit)
    for p in parameters.implicit {
      _ = declaredType(of: p)
      let q = declarationsOnStack.remove(p)
      assert(q != nil)
    }
  }

  /// Returns `t` as the head of a universal type and/or implication introducing `parameters`.
  private mutating func introduce(
    _ parameters: StaticParameters, into t: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    if parameters.isEmpty { return t }

    let ps = declaredTypes(of: parameters.explicit)
    let us = parameters.implicit.map({ (p) in declaredType(of: p) })
    return program.types.introduce(.init(parameters: ps, usings: us), into: t)
  }

  /// Configures `p` as a pattern of type `t` introducing variables with capability `k` or reports
  /// an error if `t` doesn't match `p`'s shape.
  ///
  /// A variable declaration is considered "open" iff it does not occur as a child of a binding
  /// pattern whose `p` is an ancestor. Bound variables are given a remote type whose capability
  /// corresponds to the their introducer.
  private mutating func ascribe(_ k: AccessEffect, _ t: AnyTypeIdentity, to p: PatternIdentity) {
    switch program.tag(of: p) {
    case BindingPattern.self:
      ascribe(k, t, to: program.castUnchecked(p, to: BindingPattern.self))
    case ExtractorPattern.self:
      ascribe(k, t, to: program.castUnchecked(p, to: ExtractorPattern.self))
    case TuplePattern.self:
      ascribe(k, t, to: program.castUnchecked(p, to: TuplePattern.self))
    case VariableDeclaration.self:
      ascribe(k, t, to: program.castUnchecked(p, to: VariableDeclaration.self))
    case WildcardLiteral.self:
      ascribe(k, t, to: program.castUnchecked(p, to: WildcardLiteral.self))
    default:
      check(program.castToExpression(p)!, requiring: t)
    }
  }

  /// Implements `ascribe(_:_:to:)` for binding patterns.
  private mutating func ascribe(
    _ k: AccessEffect, _ t: AnyTypeIdentity, to p: BindingPattern.ID
  ) {
    program[module].setType(t, for: p)
    ascribe(.init(program[p].introducer.value), t, to: program[p].pattern)
  }

  /// Configures `p` as a pattern of type `t` introducing open variables with capability `k` or
  /// reports an error if `t` doesn't match `p`'s shape.
  private mutating func ascribe(
    _ k: AccessEffect, _ t: AnyTypeIdentity, to p: ExtractorPattern.ID
  ) {
    let m = demand(Metatype(inhabitant: t)).erased
    guard let (_, ps) = extractor(referredToBy: p, matching: m) else {
      program[module].setType(.error, for: p)
      return
    }

    // Are the labels of the pattern compatible with those of the extractor?
    guard labelsCompatible(p, ps) else {
      let lhs = program[p].elements.map(\.label?.value)
      let rhs = ps.map(\.label)
      report(
        program.incompatibleLabels(
          found: lhs, expected: rhs, at: program.spanForDiagnostic(about: p)))
      return
    }

    for (lhs, rhs) in zip(program[p].elements, ps) {
      ascribe(k, rhs.type, to: lhs.value)
    }

    program[module].setType(t, for: p)
  }

  /// Implements `ascribe(_:_:to:)` for tuple patterns.
  private mutating func ascribe(
    _ k: AccessEffect, _ t: AnyTypeIdentity, to p: TuplePattern.ID
  ) {
    guard let u = program.types[t] as? Tuple else {
      let m = program.format("tuple pattern cannot match values of type '%T'", [t])
      report(.init(.error, m, at: program[p].site))
      program[module].setType(.error, for: p)
      return
    }

    guard u.labelsEqual(program[p].elements, \.label?.value) else {
      let d: Diagnostic = program.incompatibleLabels(
        found: program[p].elements.map(\.label?.value), expected: u.labels,
        at: program[p].site)
      report(d)
      program[module].setType(.error, for: p)
      return
    }

    program[module].setType(t, for: p)
    for i in 0 ..< u.elements.count {
      ascribe(k, u.elements[i].type, to: program[p].elements[i].value)
    }
  }

  /// Implements `ascribe(_:_:to:)` for variable declarations patterns.
  private mutating func ascribe(
    _ k: AccessEffect, _ t: AnyTypeIdentity, to p: VariableDeclaration.ID
  ) {
    let u = demand(RemoteType(projectee: t, access: k)).erased
    program[module].setType(u, for: p)
  }

  /// Implements `ascribe(_:_:to:)` for wildcard literals.
  private mutating func ascribe(
    _ k: AccessEffect, _ t: AnyTypeIdentity, to p: WildcardLiteral.ID
  ) {
    program[module].setType(t, for: p)
  }

  /// Returns `true` iff the argument labels occuring in `p` are compatible with those of `d`.
  private func labelsCompatible(_ lhs: ExtractorPattern.ID, _ rhs: [Parameter]) -> Bool {
    program[lhs].elements.elementsEqual(rhs) { (l, r) in
      (l.label == nil) || (l.label?.value == r.label)
    }
  }

  // MARK: Type inference

  /// The context in which the type of a syntax tree is being inferred.
  private struct InferenceContext {

    /// The way in which the tree is used.
    let role: SyntaxRole

    /// The type expected to be inferred given the context.
    let expectedType: AnyTypeIdentity?

    /// A set of formulae about the type being inferred.
    var obligations: Obligations

    /// Creates a context with the given properties.
    init(expectedType: AnyTypeIdentity? = nil, role: SyntaxRole = .unspecified) {
      self.expectedType = expectedType
      self.role = role
      self.obligations = .init()
    }

    /// Calls `action` with an inference context having the given properties and extending the
    /// obligations of `self`.
    mutating func withSubcontext<T>(
      expectedType: AnyTypeIdentity? = nil, role: SyntaxRole = .unspecified,
      do action: (inout Self) -> T
    ) -> T {
      var s = InferenceContext(expectedType: expectedType, role: role)
      swap(&self.obligations, &s.obligations)
      defer { swap(&self.obligations, &s.obligations) }
      return action(&s)
    }

  }

  /// Returns the inferred type of `e`, which occurs in `context`.
  private mutating func inferredType(
    of e: ExpressionIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch program.tag(of: e) {
    case BooleanLiteral.self:
      return inferredType(of: castUnchecked(e, to: BooleanLiteral.self), in: &context)
    case Call.self:
      return inferredType(of: castUnchecked(e, to: Call.self), in: &context)
    case Conversion.self:
      return inferredType(of: castUnchecked(e, to: Conversion.self), in: &context)
    case EqualityWitnessExpression.self:
      return inferredType(of: castUnchecked(e, to: EqualityWitnessExpression.self), in: &context)
    case If.self:
      return inferredType(of: castUnchecked(e, to: If.self), in: &context)
    case ImplicitQualification.self:
      return inferredType(of: castUnchecked(e, to: ImplicitQualification.self), in: &context)
    case InoutExpression.self:
      return inferredType(of: castUnchecked(e, to: InoutExpression.self), in: &context)
    case IntegerLiteral.self:
      return inferredType(of: castUnchecked(e, to: IntegerLiteral.self), in: &context)
    case NameExpression.self:
      return inferredType(of: castUnchecked(e, to: NameExpression.self), in: &context)
    case New.self:
      return inferredType(of: castUnchecked(e, to: New.self), in: &context)
    case PatternMatch.self:
      return inferredType(of: castUnchecked(e, to: PatternMatch.self), in: &context)
    case RemoteTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: RemoteTypeExpression.self), in: &context)
    case StaticCall.self:
      return inferredType(of: castUnchecked(e, to: StaticCall.self), in: &context)
    case SumTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: SumTypeExpression.self), in: &context)
    case TupleLiteral.self:
      return inferredType(of: castUnchecked(e, to: TupleLiteral.self), in: &context)
    case TupleTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: TupleTypeExpression.self), in: &context)
    case WildcardLiteral.self:
      return inferredType(of: castUnchecked(e, to: WildcardLiteral.self), in: &context)
    default:
      program.unexpected(e)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: BooleanLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = standardLibraryType(.bool)
    return context.obligations.assume(e, hasType: t, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: Call.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    guard let f = inferredType(calleeOf: e, in: &context).unlessError else {
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }

    if let t = program.types.cast(f, to: Metatype.self) {
      return inferredType(typeOperatorCall: e, on: t, in: &context)
    }

    var i: [CallConstraint.Argument] = []
    for a in program[e].arguments {
      let t = context.withSubcontext { (ctx) in inferredType(of: a.value, in: &ctx) }
      i.append(.init(label: a.label?.value, type: t))
    }

    // We cannot use the expected type to constrain the result of the callee. It would make the
    // solver to commit prematurely in the presence of overloads.
    let o = fresh().erased
    let k = CallConstraint(callee: f, arguments: i, output: o, origin: e, site: program[e].site)

    context.obligations.assume(k)
    return context.obligations.assume(e, hasType: o, at: program[e].site)
  }

  /// Returns the inferred type of `e`, which is the application of a type operator on `t`.
  private mutating func inferredType(
    typeOperatorCall e: Call.ID, on t: Metatype.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    // Are we looking at `Int[i]`?
    if program[e].style == .bracketed {
      if let a = program[e].arguments.uniqueElement, a.label == nil {
        check(a.value, requiring: standardLibraryType(.int))
        switch integerConstant(a.value) {
        case .some(let i) where i >= 0:
          let x = Tuple.Element(label: nil, type: program.types[t].inhabitant)
          let u = metatype(of: Tuple(elements: Array(repeating: x, count: i))).erased
          return context.obligations.assume(e, hasType: u, at: program[e].site)
        case .some:
          report(.error, "expression must have a positive value", about: a.value)
        case .none:
          report(.error, "expression must have a constant value", about: a.value)
        }
      } else {
        // TODO: Array expressions
        report(.error, "buffer type expression requires a single unlabeled argument", about: e)
      }
    }

    // Expression is not a sugar.
    else { report(program.doesNotDenoteType(.init(e))) }

    // Error already diagnosed.
    return context.obligations.assume(e, hasType: .error, at: program[e].site)
  }

  /// Returns the inferred type of `e`'s callee.
  ///
  /// If the expression of `e`'s callee starts with implicit qualification, its left-most symbol
  /// is resolved as a member of the expected type in `context`. For example, if the callee is
  /// expressed as `.foo().bar()` and the expected type is `T`, it is resolved as `T.foo().bar`.
  private mutating func inferredType(
    calleeOf e: Call.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let callee = program[e].callee

    // Set the type of the left-most symbol's qualification if it is implicit using the call's
    // expected type so that `f` in a call of the form `.f(x)` can be resolved as a member of the
    // call's expected type. The callee itself has no expected type; only its qualification.
    if
      let q = program.rootQualification(of: callee),
      let t = context.expectedType,
      program.tag(of: q) == ImplicitQualification.self
    {
      _ = context.withSubcontext(expectedType: t) { (ctx) in inferredType(of: q, in: &ctx) }
    }

    let r = SyntaxRole(program[e].style, labels: program[e].labels)
    let f = context.withSubcontext(role: r) { (ctx) in
      inferredType(of: callee, in: &ctx)
    }

    // Is the callee referring to a sugared constructor?
    if (program[e].style == .parenthesized) && isTypeDeclarationReference(callee) {
      let site = program[callee].site
      let n = program[module].insert(
        NameExpression(qualification: callee, name: .init("new", at: site), site: site),
        in: program.parent(containing: e))
      program[module].replace(.init(e), for: program[e].replacing(callee: .init(n)))
      return context.withSubcontext(role: r) { (ctx) in
        inferredType(of: n, in: &ctx)
      }
    }

    // Otherwise, returns the inferred type as-is.
    else { return f }

    /// Returns `true` iff `e` is a type declaration reference.
    ///
    /// `e` is a type declaration reference if it is a name expression bound to a metatype or if it
    /// is the static application of a type declaration reference.
    ///
    /// - Requires: The types of `e` and its children have been assigned in `context`.
    func isTypeDeclarationReference(_ e: ExpressionIdentity) -> Bool {
      if program.tag(of: e) == NameExpression.self {
        return program.types.tag(of: context.obligations.syntaxToType[e.erased]!) == Metatype.self
      } else if let n = program.cast(e, to: StaticCall.self) {
        return isTypeDeclarationReference(program[n].callee)
      } else {
        return false
      }
    }
  }

  /// Returns the inferred type of `e`'s callee.
  private mutating func inferredType(
    of e: Conversion.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let h = context.expectedType.map({ (m) in demand(Metatype(inhabitant: m)).erased })
    let target = context.withSubcontext(expectedType: h, role: .ascription) { (ctx) in
      inferredType(of: program[e].target, in: &ctx)
    }

    // The right-hand side denotes a type?
    if let rhs = (program.types[target] as? Metatype)?.inhabitant {
      // The right-hand side injects an expected type for the left-hand side.
      let lhs = context.withSubcontext(expectedType: rhs) { (ctx) in
        inferredType(of: program[e].source, in: &ctx)
      }

      switch program[e].semantics {
      case .up:
        let s = program.spanForDiagnostic(about: program[e].source)
        context.obligations.assume(WideningConstraint(lhs: lhs, rhs: rhs, site: s))
      case .down:
        let s = program.spanForDiagnostic(about: program[e].target)
        context.obligations.assume(WideningConstraint(lhs: rhs, rhs: lhs, site: s))
      case .pointer:
        if program.types.tag(of: rhs) != RemoteType.self {
          fatalError()
        }
      }

      return context.obligations.assume(e, hasType: rhs, at: program[e].site)
    }

    // Inference failed on the right-hand side.
    else if target == .error {
      // Error already reported.
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    } else {
      report(program.doesNotDenoteType(program[e].target))
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: EqualityWitnessExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let l = evaluateTypeAscription(program[e].lhs)
    let r = evaluateTypeAscription(program[e].rhs)

    // Was there an error?
    if (l == .error) || (r == .error) {
      return .error
    }

    // All is well.
    else {
      return metatype(of: EqualityWitness(lhs: l, rhs: r)).erased
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: If.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    for n in program[e].conditions { check(n) }

    // Are both branches single-bodied expressions?
    if
      let e0 = singleExpression(of: program[e].success),
      let e1 = singleExpression(of: program[e].failure)
    {
      let t0 = inferredType(of: program[e].success, in: &context)
      let t1 = inferredType(of: program[e].failure, in: &context)

      // Did we inferred the same type for both branches?
      if t0 == t1 {
        return context.obligations.assume(e, hasType: t0, at: program[e].site)
      }

      // Is the expected type `Void`?
      else if context.expectedType == .void {
        return context.obligations.assume(e, hasType: .void, at: program[e].site)
      }

      // Slow path: we may need coercions.
      let t = fresh().erased
      context.obligations.assume(CoercionConstraint(on: e0, from: t0, to: t, at: program[e0].site))
      context.obligations.assume(CoercionConstraint(on: e1, from: t1, to: t, at: program[e1].site))
      return context.obligations.assume(e, hasType: t, at: program[e].site)
    }

    // The branches are not single-bodied expressions; assume `e` produces `Void`.
    else {
      context.withSubcontext { (ctx) in
        _ = inferredType(of: program[e].success, in: &ctx)
        _ = inferredType(of: program[e].failure, in: &ctx)
      }
      return context.obligations.assume(e, hasType: .void, at: program[e].site)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: ImplicitQualification.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if let t = context.expectedType {
      context.obligations.assume(e, hasType: t, at: program[e].site)
      return t
    }

    // We may have already inferred the type of this tree if it occurs in the expression of some
    // callee (see `inferredType(calleeOf:in:)`). In that case, we must reuse what was inferred.
    else if let t = context.obligations.syntaxToType[e.erased] {
      return t
    } else {
      report(.init(.error, "no context to resolve implicit qualification", at: program[e].site))
      return .error
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: InoutExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = inferredType(of: program[e].lvalue, in: &context)
    return context.obligations.assume(e, hasType: t, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: IntegerLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    // Did we already elaborate this expression?
    if let t = program[e.module].type(assignedTo: e) {
      return context.obligations.assume(e, hasType: t, at: program[e].site)
    }

    // Otherwise, elaborate to `.new(integer_literal: e)`.
    else {
      let s = SourceSpan.empty(at: program[e].site.start)
      let p = program.parent(containing: e)

      let literal = program[e.module].insert(program[e], in: p)
      let integer = demand(LiteralType.integer).erased
      program[e.module].setType(integer, for: literal)

      let q = program[e.module].insert(
        ImplicitQualification(site: s), in: p)
      let n = program[e.module].insert(
        NameExpression(qualification: nil, name: .init("init", at: s), site: s), in: p)
      let m = program[e.module].insert(
        New(qualification: .init(q), target: n, site: s), in: p)
      let c = program[e.module].replace(
        .init(e),
        for: Call(
          callee: .init(m),
          arguments: [.init(label: Parsed("integer_literal", at: s), value: .init(literal))],
          style: .parenthesized,
          site: program[e].site))

      let qualification = context.expectedType ?? standardLibraryType(.int)
      return context.withSubcontext(expectedType: qualification) { (ctx) in
        inferredType(of: c, in: &ctx)
      }
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let s = program.spanForDiagnostic(about: e)

    // Is `e` a constructor reference?
    if program.isConstructorReference(e) {
      let n = program[module].insert(
        NameExpression(qualification: nil, name: .init("init", at: s), site: s),
        in: program.parent(containing: e))
      let m = program[module].replace(
        .init(e),
        for: New(qualification: program[e].qualification!, target: n, site: program[e].site))
      return inferredType(of: m, in: &context)
    }

    // Otherwise, proceed as usual.
    else {
      let t = resolve(e, in: &context)
      return context.obligations.assume(e, hasType: t, at: s)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: New.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let site = program.spanForDiagnostic(about: e)

    // If the expression is used as a callee, account for the label of the elided `self` parameter
    // of the underlying initializer.
    let role: SyntaxRole
    if case .function(let ls) = context.role {
      role = .function(labels: ["self" as Optional] + ls)
    } else {
      role = .unspecified
    }

    let s = resolveQualification(of: e, in: &context)
    let t = demand(Metatype(inhabitant: s)).erased
    let u = fresh().erased

    context.obligations.assume(
      MemberConstraint(
        member: program[e].target, role: role, qualification: t, type: u, site: site))
    context.obligations.assume(program[e].target, hasType: u, at: site)

    let v = fresh().erased
    context.obligations.assume(ConstructorConversionConstraint(lhs: u, rhs: v, site: site))
    return context.obligations.assume(e, hasType: v, at: site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: PatternMatch.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let scrutinee = check(program[e].scrutinee)
    let site = program.spanForDiagnostic(about: e)

    if program[e].branches.isEmpty {
      report(.init(.error, "pattern matching expression must have at least one case", at: site))
      return context.obligations.assume(e, hasType: .error, at: program.spanForDiagnostic(about: e))
    }

    // The type of the expression is `Void` if any of the cases isn't single-expression bodied.
    let isExpression = isSingleExpressionBodied(e)
    let expectedType = isExpression ? context.expectedType : .void

    var first: AnyTypeIdentity? = nil
    for b in program[e].branches {
      ascribe(.auto, scrutinee, to: program[b].pattern)
      context.withSubcontext(expectedType: expectedType) { (ctx) in
        let branch = inferredType(of: b, requiring: first, in: &ctx)
        if isExpression && (first == nil) {
          first = branch
        }
      }
    }

    let all = first ?? .void
    return context.obligations.assume(e, hasType: all, at: program.spanForDiagnostic(about: e))
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: PatternMatchCase.ID, requiring r: AnyTypeIdentity?,
    in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    assert(program[e.module].type(assignedTo: program[e].pattern) != nil, "pattern is not typed")
    let site = program.spanForDiagnostic(about: e)

    // Is the case single-expression bodied?
    if let b = singleExpression(of: program[e].body) {
      let t = inferredType(of: b, in: &context)
      if let u = r {
        context.obligations.assume(CoercionConstraint(on: b, from: t, to: u, at: program[b].site))
      }
      return context.obligations.assume(e, hasType: t, at: site)
    }

    // Otherwise, type check each statement.
    else {
      assert(r == nil)
      for s in program[e].body { check(s) }
      return context.obligations.assume(e, hasType: .void, at: site)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: RemoteTypeExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = evaluateTypeAscription(program[e].projectee)
    let u = metatype(of: RemoteType(projectee: t, access: program[e].access.value)).erased
    return context.obligations.assume(e, hasType: u, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: StaticCall.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if let computed =  context.obligations.syntaxToType[e.erased] { return computed }

    // Abstraction is inferred in the same inference context.
    guard let abstraction = inferredType(of: program[e].callee, in: &context).unlessError else {
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }

    let o = context.expectedType ?? fresh().erased
    let i = program[e].arguments.map { (a) in
      evaluatePartialTypeAscription(a, in: &context).result
    }

    // If the callee's referring to a type declaration, it will have type `Metatype<T>` and the
    // type arguments should be applied to `T`, "under" the metatype.
    if let m = program.types[abstraction] as? Metatype {
      assumeApplicable(m.inhabitant)
      let t = demand(Metatype(inhabitant: o)).erased
      return context.obligations.assume(e, hasType: t, at: program[e].site)
    } else {
      assumeApplicable(abstraction)
      return context.obligations.assume(e, hasType: o, at: program[e].site)
    }

    func assumeApplicable(_ f: AnyTypeIdentity) {
      let k = StaticCallConstraint(
        callee: f, arguments: i, output: o, origin: e, site: program[e].site)
      context.obligations.assume(k)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: SumTypeExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let es = program[e].elements.map({ (e) in evaluateTypeAscription(e) })
    let t = metatype(of: Sum(elements: es)).erased
    return context.obligations.assume(e, hasType: t, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: TupleLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    /// Returns the inferred type of `e`, possibly expected to have type `h`.
    func type(of e: LabeledExpression, expecting h: AnyTypeIdentity?) -> Tuple.Element {
      let u = context.withSubcontext(expectedType: h) { (ctx) in
        inferredType(of: e.value, in: &ctx)
      }
      return .init(label: e.label?.value, type: u)
    }

    let es = program[e].elements
    var ts: [Tuple.Element] = []

    // If the expected type is a tuple compatible with the shape of the expression, propagate that
    // information down the expression tree.
    if
      let h = context.expectedType.flatMap({ (t) in program.types[t] as? Tuple }),
      h.labelsEqual(es, \.label?.value)
    {
      for (e, t) in zip(es, h.elements) { ts.append(type(of: e, expecting: t.type)) }
    }

    // Otherwise, infer the type of the expression from the leaves and use type constraints to
    // detect potential mismatch.
    else {
      for e in es { ts.append(type(of: e, expecting: nil)) }
    }

    let r = demand(Tuple(elements: ts)).erased
    return context.obligations.assume(e, hasType: r, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: TupleTypeExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let es = program[e].elements.map { (e) in
      Tuple.Element(label: e.label?.value, type: evaluateTypeAscription(e.value))
    }

    let t = metatype(of: Tuple(elements: es)).erased
    return context.obligations.assume(e, hasType: t, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: WildcardLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch context.role {
    case .ascription:
      if let t = context.expectedType, program.types.tag(of: t) == Metatype.self {
        return context.obligations.assume(e, hasType: t, at: program[e].site)
      } else {
        let t = fresh().erased
        let u = demand(Metatype(inhabitant: t)).erased
        return context.obligations.assume(e, hasType: u, at: program[e].site)
      }

    default:
      let t = context.expectedType ?? fresh().erased
      return context.obligations.assume(e, hasType: t, at: program[e].site)
    }
  }

  /// Returns the inferred type of `p`, which occurs in `context`.
  private mutating func inferredType(
    of p: PatternIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch program.tag(of: p) {
    case BindingPattern.self:
      unreachable()
    case VariableDeclaration.self:
      return inferredType(of: castUnchecked(p, to: VariableDeclaration.self), in: &context)

    default:
      // Other patterns are expressions.
      let e = program.castToExpression(p) ?? unreachable()
      return inferredType(of: e, in: &context)
    }
  }

  /// Returns the inferred type of `d`, which occurs in `context`.
  private mutating func inferredType(
    of d: BindingDeclaration.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    // Fast path: if the pattern has no ascription, the type type is inferred from the initializer.
    guard let a = program[program[d].pattern].ascription else {
      if let i = program[d].initializer {
        let t = inferredType(of: i, in: &context)
        return context.obligations.assume(d, hasType: t, at: program[d].site)
      } else {
        report(.error, "binding declaration requires an ascription", about: d)
        return context.obligations.assume(d, hasType: .error, at: program[d].site)
      }
    }

    // Slow path: infer a type from the ascription and (if necessary) the initializer.
    let (p, isPartial) = evaluatePartialTypeAscription(a, in: &context)
    if isPartial, let i = program[d].initializer {
      let v = context.withSubcontext(expectedType: p, do: { (s) in inferredType(of: i, in: &s) })
      if v != .error {
        context.obligations.assume(CoercionConstraint(on: i, from: v, to: p, at: program[i].site))
      }
    }

    return context.obligations.assume(d, hasType: p, at: program[d].site)
  }

  /// Returns the inferred type of `d`, which occurs in `context`.
  private mutating func inferredType(
    of d: VariableDeclaration.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = fresh().erased
    return context.obligations.assume(d, hasType: t, at: program[d].site)
  }

  /// Returns the inferred type of `b`, which occurs in `context`.
  private mutating func inferredType(
    of b: Block.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if let e = singleExpression(of: b) {
      let t = inferredType(of: e, in: &context)
      return context.obligations.assume(b, hasType: t, at: program[b].site)
    } else {
      for s in program[b].statements { check(s) }
      return context.obligations.assume(b, hasType: .void, at: program[b].site)
    }
  }

  /// Returns the inferred type of `b`, which occurs in `context`.
  private mutating func inferredType(
    of b: If.ElseIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if let e = program.cast(b, to: If.self) {
      return inferredType(of: e, in: &context)
    } else if let s = program.cast(b, to: Block.self) {
      return inferredType(of: s, in: &context)
    } else {
      program.unexpected(b)
    }
  }

  /// Either binds `n` to declarations in `candidates` suitable for the given `role` and returns
  /// the inferred type of `n`, or returns a diagnostic reported at `site` if there isn't any
  /// viable candidate.
  ///
  /// If binding succeeds, `o` is extended with either a assignment mapping `n` to a declaration
  /// reference or an overload constrain mapping `n` to one of the viable candidates. If binding
  /// failed, `o` is left unchanged and a diagnostic is returned.
  ///
  /// - Requires: `candidates` is not empty.
  internal mutating func assume(
    _ n: NameExpression.ID, boundTo candidates: consuming [NameResolutionCandidate],
    for role: SyntaxRole, at site: SourceSpan, in o: inout Obligations
  ) -> Either<AnyTypeIdentity, Diagnostic> {
    assert(!candidates.isEmpty)

    // No candidate survived filtering?
    if let diagnostic = filterInPlace(&candidates, for: role, at: site) {
      return .right(diagnostic)
    }

    // There is only one candidate left?
    else if candidates.count == 1 {
      o.assume(n, boundTo: candidates[0].reference)
      return .left(candidates[0].type)
    }

    // Otherwise, create an overload set.
    else {
      let t = fresh().erased
      o.assume(OverloadConstraint(name: n, type: t, candidates: candidates, site: site))
      return .left(t)
    }
  }

  /// Narrows the overloaded candidates in `cs` to keep those suitable for the given `role`,
  /// returning a diagnostic iff no candidate survived.
  ///
  /// - Note: No filtering is applied if `cs` contains less than two elements.
  private func filterInPlace(
    _ cs: inout [NameResolutionCandidate], for role: SyntaxRole, at site: SourceSpan
  ) -> Diagnostic? {
    switch role {
    case _ where cs.count <= 1:
      return nil
    case .ascription, .unspecified:
      return nil
    case .function(let labels):
      return filterInPlace(&cs, callable: .parenthesized, withLabels: labels, at: site)
    case .subscript(let labels):
      return filterInPlace(&cs, callable: .bracketed, withLabels: labels, at: site)
    }
  }

  /// Narrows the overloaded candidates in `cs` to keep those that can be applied with the given
  /// style and argument labels, returning a diagnostic iff no candidate survived.
  ///
  /// - Requires: `cs` is not empty.
  private func filterInPlace(
    _ cs: inout [NameResolutionCandidate],
    callable style: Call.Style, withLabels labels: [String?], at site: SourceSpan
  ) -> Diagnostic? {
    // Non-viable candidates moved at the end.
    let i = cs.stablePartition { (c) in
      !program.types.isCallable(c.type, style, withLabels: labels)
    }
    defer { cs.removeSubrange(i...) }

    // Are there viable candidates left?
    if i != 0 { return nil }

    // Only candidates having a declaration in source are added to the notes. Other candidates are
    // not overloadable and so we can assume that another error will be diagnosed.
    let notes = cs.compactMap { (c) -> Diagnostic? in
      guard let d = c.reference.target else { return nil }
      let s = program.spanForDiagnostic(about: d)
      let h = program.types.head(c.type)

      if let w = program.types.seenAsCallableAbstraction(h), w.style == style {
        return program.incompatibleLabels(found: w.labels, expected: labels, at: s, as: .note)
      } else {
        return .init(.note, "candidate not viable", at: s)
      }
    }
    return .init(.error, "no candidate matches the argument list", at: site, notes: notes)
  }

  /// Proves the obligations `o`, which relate to the well-typedness of `n`, returning the best
  /// assignment of universally quantified variables.
  @discardableResult
  private mutating func discharge<T: SyntaxIdentity>(
    _ o: Obligations, relatedTo n: T
  ) -> Solution {
    if o.constraints.isEmpty {
      let s = Solution(bindings: o.bindings)
      commit(s, to: o)
      return s
    } else {
      var solver = Solver(o, withLoggingEnabled: isLoggingEnabled?(n.erased, program) ?? false)
      let s = solver.solution(using: &self)
      commit(s, to: o)
      return s
    }
  }

  /// Stores the assignments made in `s` to solve `o` into the program.
  private mutating func commit(_ s: Solution, to o: Obligations) {
    // Failures to assign unification variables are diagnosed only once and only if no other
    // diagnostic was reported by the solver.
    var inferenceFailureDiagnosed = s.diagnostics.containsError

    for d in s.diagnostics.elements { report(d) }

    for (n, t) in o.syntaxToType {
      var u = program.types.reify(t, applying: s.substitutions, withVariables: .kept)
      if u[.hasVariable] && !inferenceFailureDiagnosed {
        report(program.notEnoughContext(n))
        inferenceFailureDiagnosed = true
      }
      u = program.types.substituteVariableForError(in: u)
      program[n.module].setType(u, for: n)
    }

    for (n, r) in s.bindings {
      program[n.module].bind(n, to: r)
    }

    for (n, e) in s.elaborations {
      var w = program.types.reify(e, applying: s.substitutions, withVariables: .kept)
      if w.hasVariable && !inferenceFailureDiagnosed {
        report(program.notEnoughContext(n.erased))
        inferenceFailureDiagnosed = true
      }

      let m = program[n.module].clone(n)
      if program.isScope(m) {
        program.reassignScopes(childrenOf: m)
      }
      w = w.substituting(n, for: m)

      program[n.module].replace(
        n, for: SynthethicExpression(value: .witness(w), site: program[n].site))
      let u = program.types.substituteVariableForError(in: w.type)
      program[n.module].updateType(u, for: n)
    }

    for (n, e) in s.argumentElaborations {
      let arguments = e.elements.map({ (b) in elaborate(b, in: n) })
      program[n.module].replace(.init(n), for: program[n].replacing(arguments: arguments))
    }
  }

  /// Returns the elaboration of `b` which describes an argument in `n`.
  ///
  /// The elaboration of default arguments does preserve labels.
  private mutating func elaborate(_ b: ParameterBinding, in n: Call.ID) -> LabeledExpression {
    switch b {
    case .explicit(let i):
      return program[n].arguments[i]

    case .defaulted(let e):
      let t = program[n.module].type(assignedTo: e) ?? .error
      let n = program[n.module].insert(
        SynthethicExpression(value: .defaultArgument(e), site: program[n].site),
        in: program.parent(containing: n))
      program[n.module].setType(t, for: n)
      return .init(label: nil, value: e)
    }
  }

  /// Returns the type of a name expression referring to `target`, which was resolved as a bound
  /// member if `selectionIsStatic` is `false`.
  private mutating func typeOfName(
    referringTo target: DeclarationIdentity, statically selectionIsStatic: Bool
  ) -> AnyTypeIdentity {
    var t = declaredType(of: target)

    // Strip the remoteness of the entity's type.
    if let u = program.types[t] as? RemoteType {
      t = u.projectee
    }

    if !selectionIsStatic {
      return typeOfBoundMember(referringTo: target, withUnboundType: t)
    } else {
      return t
    }
  }

  /// Returns `unbound` modified as the type of a bound member iff `target` declares a non-static
  /// member. Otherwise, returns `unbound` unchanged.
  private mutating func typeOfBoundMember(
    referringTo target: DeclarationIdentity, withUnboundType unbound: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    if program.isMemberFunction(target) {
      return program.types.asBoundMemberFunction(unbound)!
    } else {
      return unbound
    }
  }

  /// Returns the type of an instance of `Self` in `s`, or `nil` if `s` isn't notionally in the
  /// scope of a type declaration.
  private mutating func typeOfSelf(in s: ScopeIdentity) -> AnyTypeIdentity? {
    if let memoized = cache.scopeToTypeOfSelf[s] { return memoized }

    guard let n = s.node else { return nil }
    let result: AnyTypeIdentity?

    switch program.tag(of: n) {
    case ConformanceDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: ConformanceDeclaration.self))
    case EnumDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: EnumDeclaration.self))
    case ExtensionDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: ExtensionDeclaration.self))
    case StructDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: StructDeclaration.self))
    case TraitDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: TraitDeclaration.self)).erased
    default:
      result = typeOfSelf(in: program.parent(containing: n))
    }

    cache.scopeToTypeOfSelf[s] = .some(result)
    return result
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: ConformanceDeclaration.ID) -> AnyTypeIdentity {
    if program[d].isAdjunct {
      // `Self` refers to the struct to which `d` is adjunct.
      return typeOfSelf(in: program.parent(containing: d))!
    } else {
      let t = declaredType(of: d)
      let w = program.types.seenAsTraitApplication(program.types.head(t))
      return w?.arguments.values[0] ?? .error
    }
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: EnumDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    return program.types.head(program.types.select(t, \Metatype.inhabitant) ?? .error)
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: ExtensionDeclaration.ID) -> AnyTypeIdentity {
    let t = extendeeType(d)
    return program.types.head(t)
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: StructDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    return program.types.head(program.types.select(t, \Metatype.inhabitant) ?? .error)
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: TraitDeclaration.ID) -> GenericParameter.ID {
    demand(GenericParameter.conformer(d, .proper))
  }

  /// Returns the type of `P.self` in `d`, which declares a trait `P`.
  private mutating func typeOfTraitSelf(in d: TraitDeclaration.ID) -> TypeApplication.ID {
    let f = demand(Trait(declaration: d)).erased
    let s = typeOfSelf(in: d)

    var a: TypeArguments = [s: s.erased]
    for p in program[d].parameters {
      let t = declaredType(of: p)
      let u = program.types.select(t, \Metatype.inhabitant, as: GenericParameter.self)!
      a[u] = t
    }

    return demand(TypeApplication(abstraction: f, arguments: a))
  }

  /// Returns the type of a model witnessing the conformance of `conformer` to `concept` with the
  /// given `arguments`.
  private mutating func typeOfModel(
    of conformer: AnyTypeIdentity, conformingTo concept: TraitDeclaration.ID,
    with arguments: [AnyTypeIdentity]
  ) -> TypeApplication.ID {
    assert(arguments.count == program[concept].parameters.count, "not enough arguments")
    let f = demand(Trait(declaration: concept)).erased
    let s = typeOfSelf(in: concept)

    var a: TypeArguments = [s: conformer]
    for (p, v) in zip(program[concept].parameters, arguments) {
      let t = declaredType(of: p)
      let u = program.types.select(t, \Metatype.inhabitant, as: GenericParameter.self)!
      a[u] = v
    }

    return demand(TypeApplication(abstraction: f, arguments: a))
  }

  /// Returns the type of the implementation satisfying `requirement` in the result of `witness`.
  ///
  /// - Parameters:
  ///   - requirement: The declaration of a concept requirement.
  ///   - witness: A model witnessing a conformance to the concept defining `requirement`.
  private mutating func typeOfImplementation(
    satisfying requirement: DeclarationIdentity, in witness: WitnessExpression
  ) -> AnyTypeIdentity {
    if let d = program.cast(requirement, to: AssociatedTypeDeclaration.self) {
      return typeOfImplementation(satisfying: d, in: witness)
    } else {
      return declaredType(of: requirement, seenThrough: witness)
    }
  }

  /// Returns the type of the implementation satisfying `requirement` in the result of `witness`.
  private mutating func typeOfImplementation(
    satisfying requirement: AssociatedTypeDeclaration.ID, in witness: WitnessExpression
  ) -> AnyTypeIdentity {
    assert(program.types.seenAsTraitApplication(witness.type) != nil)

    // The witness is the result of a coercion?
    if let (_, b) = asCoercionApplication(witness) {
      return typeOfImplementation(satisfying: requirement, in: b)
    }

    // The witness refers to a given declaration?
    else if let d = witness.declaration, let c = program.cast(d, to: ConformanceDeclaration.self) {
      // Read the associated type definition.
      if let i = implementation(of: requirement, in: c) {
        return declaredType(of: i)
      } else {
        return .error
      }
    }

    // Otherwise, the value of the witness is opaque.
    else {
      return metatype(of: AssociatedType(declaration: requirement, qualification: witness)).erased
    }
  }

  /// Returns the context parameters of the type of an instance of `Self` in `s`.
  private mutating func contextOfSelf(in s: TraitDeclaration.ID) -> ContextClause {
    let w = typeOfTraitSelf(in: s)
    return .init(parameters: .init(program.types[w].arguments.parameters), usings: [w.erased])
  }

  // MARK: Compile-time evaluation

  /// Returns the value of `e` evaluated as a type ascription.
  private mutating func evaluateTypeAscription(_ e: ExpressionIdentity) -> AnyTypeIdentity {
    var c = InferenceContext()
    let (t, _) = evaluatePartialTypeAscription(e, in: &c)
    let s = discharge(c.obligations, relatedTo: e)
    return program.types.reify(t, applying: s.substitutions)
  }

  /// Returns the value of `e` evaluated as a (possibly partial) type ascription.
  private mutating func evaluatePartialTypeAscription(
    _ e: ExpressionIdentity, in context: inout InferenceContext
  ) -> (result: AnyTypeIdentity, isPartial: Bool) {
    let t = context.withSubcontext(role: .ascription) { (ctx) in
      inferredType(of: e, in: &ctx)
    }

    if let u = program.types.select(t, \Metatype.inhabitant) {
      if let p = program.types.cast(u, to: GenericParameter.self) {
        checkProper(p, at: program.spanForDiagnostic(about: e))
      }
      return (result: u, isPartial: u[.hasVariable])
    } else if t == .error {
      // Error already reported.
      return (result: .error, isPartial: false)
    } else {
      report(program.doesNotDenoteType(e))
      return (result: .error, isPartial: false)
    }
  }

  /// Returns the value of `e` evaluated as a kind ascription.
  private mutating func evaluateKindAscription(_ e: KindExpression.ID) -> Metakind.ID {
    if let k = program[e.module].type(assignedTo: e) { return program.types.castUnchecked(k) }
    assert(e.module == module, "dependency is not typed")

    switch program[e].value {
    case .proper:
      let k = demand(Metakind(inhabitant: .proper))
      program[module].setType(k.erased, for: e)
      return k

    case .arrow(let a, let b):
      let l = evaluateKindAscription(a)
      let r = evaluateKindAscription(b)
      let k = demand(
        Metakind(inhabitant: .arrow(program.types[l].inhabitant, program.types[r].inhabitant)))
      program[module].setType(k.erased, for: e)
      return k
    }
  }

  /// Returns a denotation of `e` iff `e` represents an immutable value.
  ///
  /// - Requires: `e` has been type checked.
  private func stableDenotation(_ e: ExpressionIdentity) -> Denotation? {
    assert(program[e.module].type(assignedTo: e) != nil, "expression is not type checked")
    switch program.tag(of: e) {
    case NameExpression.self:
      return stableDenotation(program.castUnchecked(e, to: NameExpression.self))
    default:
      return nil
    }
  }

  /// Returns a denotation of `e` iff `e` represents an immutable value.
  ///
  /// - Requires: `e` has been type checked.
  private func stableDenotation(_ e: NameExpression.ID) -> Denotation? {
    guard
      let t = program[e.module].type(assignedTo: e),
      let r = program[e.module].declaration(referredToBy: e)
    else { return nil }

    if let d = r.target {
      if !isStable(d) { return nil }
      if let q = program[e].qualification {
        return stableDenotation(q).flatMap({ (a) in .reference(a, r, t) })
      } else {
        return .reference(nil, r, t)
      }
    }

    return nil
  }

  /// Returns `true` iff `d` introduces an immutable entity.
  ///
  /// - Requires: `d` has been type checked.
  private func isStable(_ d: DeclarationIdentity) -> Bool {
    switch program.tag(of: d) {
    case ParameterDeclaration.self, VariableDeclaration.self:
      let t = program[d.module].type(assignedTo: d)!
      return (program.types[t] as? RemoteType)?.access == .let

    default:
      return false
    }
  }

  /// Returns the value evaluated by `e` iff it is a constant integer literal.
  ///
  /// - Requires: `e` has been type checked.
  private mutating func integerConstant(_ e: ExpressionIdentity) -> Int? {
    // The expression must be a call and have type `Int`.
    guard
      let c = program.cast(e, to: Call.self),
      program[e.module].type(assignedTo: c) == standardLibraryType(.int)
    else { return nil }

    // Are we looking at `.new(integer_literal: i)`?
    if let n = program.cast(program[c].callee, to: New.self) {
      let r = program[e.module].declaration(referredToBy: program[n].target)
      let d = standardLibraryDeclaration(.expressibyByIntegerLiteralInit)
      if case .inherited(_, d) = r {
        let i = program.castUnchecked(program[c].arguments[0].value, to: IntegerLiteral.self)
        return Int(program[i].value)
      }
    }

    return nil
  }

  // MARK: Implicit search

  /// A witness resolved by implicit resolution.
  internal struct SummonResult {

    /// The expression of the witness.
    internal let witness: WitnessExpression

    /// A table assigning the open variables of the witness's type.
    internal let substitutions: SubstitutionTable

  }

  /// The process of elaborating a the value of a witness satisfying having some given type.
  ///
  /// An instance represents a possibly non-terminating thread of execution modeling the steps of a
  /// witness' resolution. Taking a step yields either a witness (when resolution completes) or a
  /// set of other threads representing all possible conclusions.
  private struct ResolutionThread {

    /// The result of taking a step in a resolution thread.
    enum Advanced {

      /// The thread has completed execution.
      case done(SummonResult)

      /// The thread has taken a step and suspended, spawning zero or threads to resume.
      case next([ResolutionThread])

    }

    /// A part of a thread continuation.
    enum ContinuationItem {

      /// Either the result of a thread or an operand to a thread continuation.
      case done(SummonResult)

      /// A continuation substituting assumed witnesses of the given type by a summoned witness.
      case substitute(Int)

    }

    /// The environment of a thread, representing open variable assignments and assumed givens.
    struct Environment {

      /// A table from open variable to its assignment.
      let substitutions: SubstitutionTable

      /// The set of assumed givens.
      let givens: [Given]

      /// The identifier of the next assumed given.
      let nextGivenIdentifier: Int

      /// Returns a copy of `self` in which `ts` are assumed given.
      func assuming(givens ts: [AnyTypeIdentity]) -> Environment {
        let gs = ts.enumerated().map({ (i, t) in Given.assumed(nextGivenIdentifier + i, t) })
        let e = Environment(
          substitutions: substitutions, givens: givens + gs,
          nextGivenIdentifier: nextGivenIdentifier + gs.count)
        return e
      }

      func assuming(given t: AnyTypeIdentity) -> (Environment, WitnessExpression) {
        let i = nextGivenIdentifier
        let g = Given.assumed(i, t)
        let e = Environment(
          substitutions: substitutions, givens: givens + [g], nextGivenIdentifier: i + 1)
        return (e, .init(value: .assumed(i), type: t))
      }

      /// An empty environment.
      static var empty: Environment {
        .init(substitutions: .init(), givens: [], nextGivenIdentifier: 0)
      }

    }

    /// The witness being resolved, whose value is matched against some queried type.
    let witness: WitnessExpression

    /// The type of the witness to resolve.
    let queried: AnyTypeIdentity

    /// The environment in which matching takes place.
    let environment: Environment

    /// The thread's continuation.
    ///
    /// A continuation is represented as a stack of operands and operators, encoding an operation
    /// in a tack-based DSL.
    let tail: [ContinuationItem]

    /// Extra weight added to the resolution of the witness.
    ///
    /// - Invariant: This property is greater than or equal to 0.
    let delay: Int

    /// Creates an instance with the given properties.
    init(
      matching witness: WitnessExpression, to queried: AnyTypeIdentity,
      in environment: Environment,
      then tail: [ContinuationItem] = [],
      delayedBy delay: Int
    ) {
      assert(delay >= 0)
      self.witness = witness
      self.queried = queried
      self.environment = environment
      self.tail = tail
      self.delay = delay
    }

    /// Returns a copy of `self` with the given properties reassigned.
    consuming func copy(
      matching witness: WitnessExpression, to queried: AnyTypeIdentity,
      in environment: Environment
    ) -> Self {
      .init(matching: witness, to: queried, in: environment, then: tail, delayedBy: delay)
    }

    /// Returns a copy of `self` with one less penalty.
    consuming func removingPenalty() -> Self {
      .init(matching: witness, to: queried, in: environment, then: tail, delayedBy: delay - 1)
    }

  }

  /// Returns witnesses of values of type `t` derivable from the implicit store in `scopeOfUse`.
  internal mutating func summon(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity
  ) -> [SummonResult] {
    // Did we already compute the result?
    if let table = cache.scopeToSummoned[scopeOfUse], let result = table[t] {
      return result
    }

    let result: [SummonResult]

    // If there aren't any givens in `scopeOfUse`, just summon in the parent scope.
    if givens(lexicallyIn: scopeOfUse).isEmpty, let p = program.parent(containing: scopeOfUse) {
      result = summon(t, in: p)
    }

    // Otherwise, we can't just extend the set of candidates summoned in the outer scope as the
    // introduction of a new given may change the result of implicit resolution. Instead, we must
    // consider all visible givens at once.
    else {
      let threads = summon(t, in: scopeOfUse, where: .empty, then: [])
      result = takeSummonResults(from: threads, in: scopeOfUse)
    }

    // Do not memoize the result if it has been computed while givens were on stack.
    if !t[.hasVariable] && !declarationsOnStack.contains(where: program.isGiven) {
      cache.scopeToSummoned[scopeOfUse, default: [:]][t] = result
    }

    return result
  }

  /// Returns the result of `continuation` applied to witnesses of values of type `t` derivable
  /// from the implicit store in `scopeOfUse`.
  ///
  /// - Parameters:
  ///   - t: The type whose instance is summoned.
  ///   - scopeOfUse: The scope in which the witnesses are resolve.
  ///   - environment: An assignment of unification variables in `t` and a set of assumed givens.
  ///   - continuation: The work to be done with the summoned results.
  private mutating func summon(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity,
    where environment: ResolutionThread.Environment,
    then continuation: [ResolutionThread.ContinuationItem]
  ) -> [ResolutionThread] {
    // Assumed givens.
    var gs: [[Given]] = []

    // Assumed givens.
    if !environment.givens.isEmpty {
      gs.append(environment.givens)
    }

    // Givens visible from `scopeOfUse`.
    for s in program.scopes(from: scopeOfUse) {
      gs.append(givens(lexicallyIn: s).filter(notOnStack(_:)))
    }
    for f in program[scopeOfUse.module].sourceFileIdentities where f != scopeOfUse.file {
      gs.append(givens(lexicallyIn: .init(file: f)).filter(notOnStack(_:)))
    }
    for i in imports(of: scopeOfUse.file) {
      gs.append(givens(atTopLevelOf: i).filter(notOnStack(_:)))
    }

    // Built-in givens.
    gs.append([
      .coercion(.reflexivity),
      .coercion(.symmetry),
      .coercion(.transitivity),
    ])

    let u = program.types.reify(t, applying: environment.substitutions, withVariables: .kept)
    return gs.enumerated().reduce(into: []) { (result, grouping) in
      for g in grouping.element {
        let w = expression(referringTo: g)
        let r = formThread(
          matching: w, to: u, in: environment, then: continuation, delayedBy: grouping.offset)
        result.append(r)
      }
    }
  }

  /// Returns a resolution thread for matching `witness` to `queried`.
  ///
  /// - Parameters:
  ///   - environment: Assignments of open variables and assumed givens.
  ///   - tail: The operations to perform after matching succeeds.
  ///   - delay: Extra weight added to the result of this thread.
  private mutating func formThread(
    matching witness: WitnessExpression, to queried: AnyTypeIdentity,
    in environment: ResolutionThread.Environment,
    then tail: [ResolutionThread.ContinuationItem] = [],
    delayedBy delay: Int
  ) -> ResolutionThread {
    var witness = witness
    var queried = queried
    var environment = environment

    while true {
      // Weak-head normal forms.
      witness = program.types.reify(
        witness, applying: environment.substitutions, withVariables: .kept)
      queried = program.types.reify(
        queried, applying: environment.substitutions, withVariables: .kept)

      // The witness has a universal type?
      if let u = program.types[witness.type] as? UniversalType {
        let a = TypeArguments(mapping: u.parameters, to: { _ in fresh().erased })
        witness = WitnessExpression(
          value: .typeApplication(witness, a),
          type: program.types.substitute(a, in: u.body))
        continue
      }

      // The witness is an implication?
      if let i = program.types[witness.type] as? Implication {
        // Assume that the implication has a non-empty context.
        let h = i.usings.first!
        let (e, v) = environment.assuming(given: h)
        witness = WitnessExpression(
          value: .termApplication(witness, v),
          type: program.types.dropFirstRequirement(.init(uncheckedFrom: witness.type)))
        environment = e
        continue
      }

      // The witness already has a simple type.
      return .init(matching: witness, to: queried, in: environment, then: tail, delayedBy: delay)
    }
  }

  /// Returns the result of taking a step in `thread`, which resolves a witness in `scopeOfUse`.
  ///
  /// `thread` should be the result of `formThread`, which introduces the necessary assumptions in
  /// the thread's environment to ensure that its witness has a simple type.
  ///
  /// - Requires: `thread.witness` is has no context (i.e., it's a simple type).
  private mutating func match(
    _ thread: ResolutionThread, in scopeOfUse: ScopeIdentity
  ) -> ResolutionThread.Advanced {
    if thread.delay > 0 {
      return .next([thread.removingPenalty()])
    }

    assert(!program.types.hasContext(thread.witness.type))
    let (a, b) = (thread.witness.type, thread.queried)

    // The witness has a simple type; attempt a match.
    var substitutions = SubstitutionTable()
    var coercions: [(AnyTypeIdentity, AnyTypeIdentity)] = []
    _ = program.types.unifiable(a, b, extending: &substitutions) { (x, y) in
      coercions.append((x, y))
      return true
    }

    // No coercion required?
    if coercions.isEmpty {
      let s = thread.environment.substitutions.union(substitutions)
      let w = program.types.reify(thread.witness, applying: s, withVariables: .kept)
      if w.type[.hasError] { return .next([]) }

      let r = SummonResult(witness: w, substitutions: s)
      return threadContinuation(appending: r, to: thread, in: scopeOfUse)
    }

    // Resolution failed if nothing matches structurally.
    else if let (x, y) = coercions.uniqueElement, (x == a), (y == b) {
      return .next([])
    }

    // Properties of equality are encoded as axioms so there is no need to assume non-syntactic
    // equalities between parts of equality witnesses.
    else if program.types.isEquality(a) || program.types.isEquality(b) {
      return .next([])
    }

    // Otherwise, assume non-syntactic equalities between pairwise parts.
    let e = thread.environment.assuming(
      givens: coercions.map({ (c) in demand(EqualityWitness(lhs: c.0, rhs: c.1)).erased }))
    let t = demand(EqualityWitness(lhs: a, rhs: b)).erased
    let w = WitnessExpression(
      value: .termApplication(.init(builtin: .coercion, type: t), thread.witness),
      type: b)
    return .next([thread.copy(matching: w, to: b, in: e)])
  }

  /// Returns the continuation of `thread` after having resolved `operand` in `scopeOfUse`.
  private mutating func threadContinuation(
    appending operand: SummonResult, to thread: ResolutionThread, in scopeOfUse: ScopeIdentity
  ) -> ResolutionThread.Advanced {
    // Are there assumptions to discharge?
    if case .assumed(let i, let assumed) = thread.environment.givens.last {
      let e = ResolutionThread.Environment(
        substitutions: operand.substitutions, givens: thread.environment.givens.dropLast(),
        nextGivenIdentifier: thread.environment.nextGivenIdentifier)
      var t = thread.tail
      t.append(.done(operand))
      t.append(.substitute(i))
      return .next(summon(assumed, in: scopeOfUse, where: e, then: t))
    }

    // We're done; apply the continuation.
    else {
      assert(thread.environment.givens.isEmpty)
      return .done(applyContinuation(thread.tail[...], to: operand))
    }
  }

  /// Returns the result of  `continuation` applied to `operand`.
  private mutating func applyContinuation(
    _ continuation: ArraySlice<ResolutionThread.ContinuationItem>, to operand: SummonResult
  ) -> SummonResult {
    switch continuation.last {
    case .some(.substitute(let i)):
      let r = executeContinuation(continuation.dropLast())
      let x = r.witness.substituting(assumed: i, for: operand.witness.value)
      let e = operand.substitutions.union(r.substitutions)
      return .init(
        witness: program.types.reify(x, applying: e, withVariables: .kept), substitutions: e)

    case .some(.done):
      unreachable("ill-formed continuation")

    case .none:
      let w = program.types.reify(
        operand.witness, applying: operand.substitutions, withVariables: .kept)
      return .init(witness: w, substitutions: operand.substitutions)
    }
  }

  /// Returns the result of the given thread continuation.
  private mutating func executeContinuation(
    _ continuation: ArraySlice<ResolutionThread.ContinuationItem>
  ) -> SummonResult {
    if case .some(.done(let a)) = continuation.last {
      applyContinuation(continuation.dropLast(), to: a)
    } else {
      unreachable("ill-formed continuation")
    }
  }

  /// Returns the results of `threads`, which are defined in `scopeOfUse`.
  ///
  /// - Requires: The types of the witnesses in `threads` have no context.
  private mutating func takeSummonResults(
    from threads: [ResolutionThread], in scopeOfUse: ScopeIdentity
  ) -> [SummonResult] {
    var work = threads
    var done: [SummonResult] = []
    var depth = 0

    while done.isEmpty && !work.isEmpty && (depth < maxImplicitDepth) {
      var next: [ResolutionThread] = []
      for item in work {
        switch match(item, in: scopeOfUse) {
        case .done(let r): done.append(r)
        case .next(let s): next.append(contentsOf: s)
        }
      }
      depth += 1
      swap(&next, &work)
    }

    return done
  }

  /// Returns the givens whose definitions are at the top-level of `m`.
  private mutating func givens(atTopLevelOf m: Program.ModuleIdentity) -> [Given] {
    if let memoized = cache.moduleToGivens[m] { return memoized }

    var gs: [Given] = []
    appendGivens(in: program[m].topLevelDeclarations, to: &gs)

    cache.moduleToGivens[m] = gs
    return gs
  }

  /// Returns the givens whose definitions are directly contained in `s`.
  private mutating func givens(lexicallyIn s: ScopeIdentity) -> [Given] {
    if let memoized = cache.scopeToGivens[s] { return memoized }

    var gs: [Given] = []
    appendGivens(in: program.declarations(lexicallyIn: s), to: &gs)

    if let d = s.node, let c = program.cast(d, to: TraitDeclaration.self) {
      gs.append(.abstract(typeOfTraitSelf(in: c).erased))
    }

    cache.scopeToGivens[s] = gs
    return gs
  }

  /// Appends the declarations of compile-time givens in `ds` to `gs`.
  private mutating func appendGivens<S: Sequence<DeclarationIdentity>>(
    in ds: S, to gs: inout [Given]
  ) {
    for d in ds {
      if program.isGiven(d) {
        gs.append(.user(d))
      }

      // Collect given definitions nested in traits and adjunct conformances.
      else if let t = program.cast(d, to: TraitDeclaration.self) {
        for n in givens(lexicallyIn: .init(node: t)) where !n.isAbstract {
          gs.append(.nested(t, n))
        }
      } else if let t = program.cast(d, to: StructDeclaration.self) {
        for d in program[t].conformances {
          gs.append(.user(.init(d)))
        }
      } else if let t = program.cast(d, to: EnumDeclaration.self) {
        for d in program[t].conformances {
          gs.append(.user(.init(d)))
        }
      }
    }
  }

  /// Returns the expression of a witness referring directly to `g`.
  private mutating func expression(referringTo g: Given) -> WitnessExpression {
    let t = declaredType(of: g)
    switch g {
    case .coercion:
      return .init(value: .reference(.builtin(.coercion)), type: t)
    case .abstract:
      return .init(value: .abstract, type: t)
    case .assumed(let i, _):
      return .init(value: .assumed(i), type: t)
    case .user(let d):
      return .init(value: .reference(.direct(d)), type: t)
    case .nested(_, let h):
      return .init(value: .nested(expression(referringTo: h)), type: t)
    }
  }

  /// Returns the possible ways to elaborate `e`, which has type `a`, as an expression of type `b`.
  internal mutating func coerced(
    _ e: ExpressionIdentity, withType a: AnyTypeIdentity, toMatch b: AnyTypeIdentity
  ) -> [SummonResult] {
    // Fast path: types are unifiable without any coercion.
    if !b.isVariable, let subs = program.types.unifiable(a, b) {
      return [SummonResult(witness: .init(value: .identity(e), type: a), substitutions: subs)]
    }

    // Slow path: compute an elaboration.
    let sansCoercion = formThread(
      matching: .init(value: .identity(e), type: a), to: b, in: .empty, delayedBy: 0)

    // Either the type of the elaborated witness is unifiable with the queried type or we need to
    // assume a coercion. Implicit resolution will figure out the "cheapest" alternative.
    let (environment, coercion) = sansCoercion.environment.assuming(
      given: demand(EqualityWitness(lhs: sansCoercion.witness.type, rhs: b)).erased)
    let w = WitnessExpression(value: .termApplication(coercion, sansCoercion.witness), type: b)
    let withCoercion = sansCoercion.copy(matching: w, to: b, in: environment)

    let scopeOfUse = program.parent(containing: e)
    return takeSummonResults(from: [sansCoercion, withCoercion], in: scopeOfUse)
  }

  // MARK: Name resolution

  /// Resolves the declaration to which `e` refers and returns the type of `e`.
  private mutating func resolve(
    _ e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let scopeOfUse = program.parent(containing: e)
    let site = program.spanForDiagnostic(about: e)
    let candidates: [NameResolutionCandidate]

    // Qualified case.
    if let m = program[e].qualification {
      let q = inferredType(of: m, in: &context)

      // Is the qualification a unification variable?
      if q.isVariable || program.types.isMetatype(q, of: \.isVariable) {
        let t = fresh().erased
        let k = MemberConstraint(
          member: e, role: context.role, qualification: q, type: t, site: site)
        context.obligations.assume(k)
        return context.obligations.assume(e, hasType: t, at: site)
      }

      // Is the qualification ill-typed?
      else if q == .error {
        return context.obligations.assume(e, hasType: .error, at: site)
      }

      // Is the qualification referring to an outer trait?
      else if let d = enclosingTraitDeclaration(referredToBy: m, in: context) {
        let n = program[e].name.value
        if n.isSimple && n.identifier == "Self" {
          let t = typeOfSelf(in: d).erased
          let u = demand(Metatype(inhabitant: t)).erased
          candidates = [.init(reference: .builtin(.alias), type: u)]
        } else {
          report(.error, "enclosing trait can only be used to refer to 'Self'", about: m)
          return context.obligations.assume(e, hasType: .error, at: site)
        }
      }

      // Qualification can be used to resolve the identifier.
      else {
        candidates = resolve(program[e].name.value, memberOf: q, visibleFrom: scopeOfUse)
        if candidates.isEmpty {
          report(program.undefinedSymbol(program[e].name, memberOf: q))
          return context.obligations.assume(e, hasType: .error, at: site)
        }
      }
    }

    // Unqualified case.
    else {
      candidates = resolve(program[e].name.value, unqualifiedIn: scopeOfUse)
      if candidates.isEmpty {
        report(program.undefinedSymbol(program[e].name))
        return context.obligations.assume(e, hasType: .error, at: site)
      }
    }

    switch assume(e, boundTo: candidates, for: context.role, at: site, in: &context.obligations) {
    case .left(let t):
      return t
    case .right(let d):
      report(d)
      return .error
    }
  }

  /// Resolves and returns the qualification of `e`, which occurs in `context`.
  private mutating func resolveQualification(
    of e: New.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if let q = program.cast(program[e].qualification, to: ImplicitQualification.self) {
      return inferredType(of: q, in: &context)
    } else {
      return evaluatePartialTypeAscription(program[e].qualification, in: &context).result
    }
  }

  /// Returns the type in which qualified name lookup is performed to select a member of a value
  /// having type `t` along with a Boolean indicating whether static members should be resolved.
  ///
  /// If this method returns `(s, true)`, then selections on a term of type `s` denote non-static
  /// and unbound members of `s`.
  private mutating func qualificationForSelection(
    on t: AnyTypeIdentity
  ) -> (type: AnyTypeIdentity, isStatic: Bool) {
    // If the qualification has a remote type, name resolution proceeds with the projectee.
    if let u = program.types[t] as? RemoteType {
      return (u.projectee, false)
    }

    // If the qualification has a metatype, name resolution proceeds with the inhabitant so that
    // expressions of the form `T.m` can denote entities introduced as members of `T` (rather
    // than `Metatype<T>`). The context clause of the qualification is preserved to support member
    // selection on unapplied type constructors (e.g., `Array.new`).
    let (context, head) = program.types.contextAndHead(t)
    if let m = program.types[head] as? Metatype {
      let u = program.types.introduce(context, into: m.inhabitant)
      return (u, true)
    } else {
      return (t, false)
    }
  }

  /// Returns the innermost trait declaration that contains `e`, if any.
  private mutating func enclosingTraitDeclaration(
    referredToBy e: ExpressionIdentity, in context: InferenceContext
  ) -> TraitDeclaration.ID? {
    if
      let n = program.cast(e, to: NameExpression.self),
      case .some(.direct(let d)) = context.obligations.bindings[n]
    {
      return program.cast(d, to: TraitDeclaration.self)
    } else {
      return nil
    }
  }

  /// Returns candidates for resolving `n` without qualification in `scopeOfUse`.
  private mutating func resolve(
    _ n: Name, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    var candidates: [NameResolutionCandidate] = []

    for d in lookup(n, unqualifiedIn: scopeOfUse) {
      let t = typeOfName(referringTo: d, statically: true)
      candidates.append(.init(reference: .direct(d), type: t))
    }

    // Predefined names are resolved iff no other candidate has been found.
    if candidates.isEmpty {
      return resolve(predefined: n, unqualifiedIn: scopeOfUse)
    } else {
      return candidates
    }
  }

  /// Returns candidates for resolving `n` without qualification in `scopeOfUse`.
  ///
  /// This method implements the same functionality as `resolve(_:unqualifiedIn:)` but it also
  /// supports unqualified member selection. Because this feature appears to slows down name
  /// resolution significantly, the former method should be used for the time being.
  private mutating func _resolveWithUnqualifiedMemberSelection(
    _ n: Name, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    var candidates: [NameResolutionCandidate] = []

    // Are we in a non-static member declaration?
    if let member = program.innermostMemberScope(from: scopeOfUse) {
      var ds = lookup(n, unqualifiedIn: scopeOfUse, containedIn: member)

      if ds.isEmpty {
        let q = typeOfSelf(in: member)!
        let implicitlyQualified = resolve(n, memberOf: q, visibleFrom: scopeOfUse)

        if !implicitlyQualified.isEmpty {
          return implicitlyQualified
        } else {
          ds.append(contentsOf: lookup(n, unqualifiedIn: program.parent(containing: member)!))
        }
      }

      for d in ds {
        let t = typeOfName(referringTo: d, statically: true)
        candidates.append(.init(reference: .direct(d), type: t))
      }
    }

    // No implicit member qualification.
    else {
      for d in lookup(n, unqualifiedIn: scopeOfUse) {
        let t = typeOfName(referringTo: d, statically: true)
        candidates.append(.init(reference: .direct(d), type: t))
      }
    }

    // Predefined names are resolved iff no other candidate has been found.
    if candidates.isEmpty {
      return resolve(predefined: n, unqualifiedIn: scopeOfUse)
    } else {
      return candidates
    }
  }

  /// Resolves `n` as a predefined name unqualified in `scopeOfUse`.
  private mutating func resolve(
    predefined n: Name, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    // Predefed names names have no argument labels, operator notation, or introducer.
    if !n.isSimple { return [] }

    switch n.identifier {
    case "Self":
      if let t = typeOfSelf(in: scopeOfUse) {
        let u = demand(Metatype(inhabitant: t)).erased
        return [.init(reference: .builtin(.alias), type: u)]
      } else {
        return []
      }

    case "Never":
      let t = demand(Metatype(inhabitant: .never)).erased
      return [.init(reference: .builtin(.alias), type: t)]

    case "Void":
      let t = demand(Metatype(inhabitant: .void)).erased
      return [.init(reference: .builtin(.alias), type: t)]

    case "Builtin":
      let t = demand(Namespace(identifier: .builtin)).erased
      return [.init(reference: .builtin(.alias), type: t)]

    default:
      return []
    }
  }

  /// Resolves `n` as a member of the built-in module.
  private mutating func resolve(builtin n: Name) -> [NameResolutionCandidate] {
    // Built-in names have no argument labels, operator notation, or introducer.
    if !n.isSimple { return [] }

    // Are we selecting a machine type?
    else if let m = MachineType(n.identifier) {
      return [.init(reference: .builtin(.alias), type: metatype(of: m).erased)]
    }

    // Are we selecting a literal type?
    else if let m = LiteralType(n.identifier) {
      return [.init(reference: .builtin(.alias), type: metatype(of: m).erased)]
    }

    // Are we selecting a built-in function?
    else if let f = BuiltinFunction(n.identifier, uniquingTypesWith: &program.types) {
      let t = f.type(uniquingTypesWith: &program.types)
      return [.init(reference: .builtin(.function(f)), type: t.erased)]
    }

    // Nothing that we know.
    else { return [] }
  }

  /// Returns candidates for resolving `n` as a member of `q` in `scopeOfUse`.
  ///
  /// - Requires: `q.type` is not a unification variable.
  internal mutating func resolve(
    _ n: Name, memberOf q: AnyTypeIdentity, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    // Is `q` a namespace?
    if let s = program.types.cast(q, to: Namespace.self) {
      return resolve(n, memberOf: s, visibleFrom: scopeOfUse)
    }

    var candidates: [NameResolutionCandidate] = []
    let (type: r, isStatic: s) = qualificationForSelection(on: q)

    candidates.append(
      contentsOf: resolve(n, nativeMemberOf: r, statically: s))
    candidates.append(
      contentsOf: resolve(n, memberInExtensionOf: r, visibleFrom: scopeOfUse, statically: s))
    candidates.append(
      contentsOf: resolve(n, inheritedMemberOf: r, visibleFrom: scopeOfUse, statically: s))

    return candidates
  }

  /// Returns candidates for resolving `n` as a member of `q` in `scopeOfUse`.
  private mutating func resolve(
    _ n: Name, memberOf q: Namespace.ID, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    switch program.types[q].identifier {
    case .builtin:
      return resolve(builtin: n)

    case .module(let m):
      var candidates: [NameResolutionCandidate] = []
      for s in program[m].sourceFileIdentities {
        candidates.append(contentsOf: resolve(n, unqualifiedIn: .init(file: s)))
      }
      return candidates
    }
  }

  /// Returns candidates for resolving `n` as a member declared in the primary declaration of the
  /// type identified by `q`, selected statically iff `selectionIsStatic` is `true`.
  ///
  /// Non-static members are resolved as unbound members if `selectionIsStatic` is `true` and as
  /// bound members if `selectionIsStatic` is `false`.
  ///
  /// - Requires: `q.type` is not a unification variable.
  private mutating func resolve(
    _ n: Name, nativeMemberOf q: AnyTypeIdentity, statically selectionIsStatic: Bool
  ) -> [NameResolutionCandidate] {
    assert(!q.isVariable)
    let (context, receiver) = program.types.contextAndHead(q)
    var candidates: [NameResolutionCandidate] = []

    var ds = declarations(nativeMembersOf: q)[n.identifier] ?? []
    refineLookupResults(&ds, matching: n)

    for m in ds {
      if !resolvableWithQualification(m) { continue }
      var member = typeOfName(referringTo: m, statically: selectionIsStatic)
      if let a = program.types[receiver] as? TypeApplication {
        member = program.types.substitute(a.arguments, in: member)
      }
      member = program.types.introduce(context, into: member)
      candidates.append(
        .init(reference: selectionIsStatic ? .direct(m) : .member(m), type: member))
    }

    return candidates
  }

  /// Returns candidates for resolving `n` as a member in an extension of `q` in `scopeOfUse`,
  /// selected statically iff `selectionIsStatic` is `true`.
  ///
  /// Non-static members are resolved as unbound members if `selectionIsStatic` is `true` and as
  /// bound members if `selectionIsStatic` is `false`.
  private mutating func resolve(
    _ n: Name, memberInExtensionOf q: AnyTypeIdentity, visibleFrom scopeOfUse: ScopeIdentity,
    statically selectionIsStatic: Bool
  ) -> [NameResolutionCandidate] {
    // Are we in the scope of a syntax tree?
    if let p = program.parent(containing: scopeOfUse) {
      let es = extensions(lexicallyIn: scopeOfUse)
      let xs = resolve(n, memberInExtensionOf: q, visibleFrom: p, statically: selectionIsStatic)
      let ys = resolve(
        n, declaredIn: es, applyingTo: q, in: scopeOfUse, statically: selectionIsStatic)
      return xs + ys
    }

    // We are at the top-level.
    else {
      let es = extensions(visibleAtTopLevelOf: scopeOfUse.file)
      return resolve(
        n, declaredIn: es, applyingTo: q, in: scopeOfUse, statically: selectionIsStatic)
    }
  }

  /// For each declaration in `es` that applies to `q`, adds to `result` the members of that
  /// declaration that are named `n`.
  private mutating func resolve<S: Sequence<ExtensionDeclaration.ID>>(
    _ n: Name,
    declaredIn extensions: S, applyingTo q: AnyTypeIdentity, in scopeOfUse: ScopeIdentity,
    statically selectionIsStatic: Bool,
  ) -> [NameResolutionCandidate] {
    var candidates: [NameResolutionCandidate] = []
    for e in extensions where !declarationsOnStack.contains(.init(e)) {
      if let a = applies(e, to: q, in: scopeOfUse) {
        let w = program.types.reify(
          a.witness, applying: a.substitutions, withVariables: .substitutedByError)

        for m in declarations(lexicallyIn: .init(node: e))[n.identifier] ?? [] {
          if !resolvableWithQualification(m) { continue }
          var member = typeOfName(referringTo: m, statically: selectionIsStatic)

          // Strip the context defined by the extension, apply type arguments from the matching
          // witness, and substitute the extendee for the receiver.
          if let arguments = w.typeArguments(appliedTo: e) {
            member = program.types.substitute(arguments, in: member)
          }
          candidates.append(.init(reference: .inherited(w, m), type: member))
        }
      }
    }
    return candidates
  }

  /// Returns candidates for resolving `name` as a member of `q` via conformance in `scopeOfUse`,
  /// selected statically iff `selectionIsStatic` is `true`.
  ///
  /// Non-static members are resolved as unbound members if `selectionIsStatic` is `true` and as
  /// bound members if `selectionIsStatic` is `false`.
  private mutating func resolve(
    _ name: Name, inheritedMemberOf q: AnyTypeIdentity, visibleFrom scopeOfUse: ScopeIdentity,
    statically selectionIsStatic: Bool
  ) -> [NameResolutionCandidate] {
    var candidates: [NameResolutionCandidate] = []

    for (concept, ms) in lookup(name, memberOfTraitVisibleFrom: scopeOfUse) {
      let vs = program[concept].parameters.map({ _ in fresh().erased })
      let model = typeOfModel(of: q, conformingTo: concept, with: vs)
      for a in summon(model.erased, in: scopeOfUse) {
        for m in ms {
          let w = program.types.reify(
            a.witness, applying: a.substitutions, withVariables: .substitutedByError)
          var member = typeOfImplementation(satisfying: m, in: w)
          if !selectionIsStatic {
            member = typeOfBoundMember(referringTo: m, withUnboundType: member)
          }
          candidates.append(.init(reference: .inherited(w, m), type: member))
        }
      }
    }

    return candidates
  }

  /// Returns the declarations that introduce `name` without qualification in `scopeOfUse` and that
  /// are contained in `bound` (unless it is `nil`).
  ///
  /// If `bound` is not `nil`, it is a scope equal to or ancestor of `scopeOfUse`.
  private mutating func lookup(
    _ name: Name, unqualifiedIn scopeOfUse: ScopeIdentity, containedIn bound: ScopeIdentity? = nil
  ) -> [DeclarationIdentity] {
    var result: [DeclarationIdentity] = []

    /// Adds the contents of `ds` to `result` if either `result` is empty or all elements in `ds`
    /// are overloadable, and returns whether declarations from outer scopes are shadowed.
    func append(_ ds: [DeclarationIdentity]) -> Bool {
      if ds.allSatisfy(program.isOverloadable(_:)) {
        result.append(contentsOf: ds)
        return false
      } else if result.isEmpty {
        result.append(contentsOf: ds)
        return true
      } else {
        return true
      }
    }

    // Look for declarations in `scopeOfUse` and its ancestors.
    for s in program.scopes(from: scopeOfUse) {
      if append(lookup(name, lexicallyIn: s)) || (s == bound) {
        return result
      }
    }

    // Look for top-level declarations in other source files.
    let f = scopeOfUse.file
    for s in program[f.module].sourceFileIdentities where s != f {
      if append(lookup(name, lexicallyIn: .init(file: s))) {
        return result
      }
    }

    // Look for imports.
    for n in imports(of: f) {
      result.append(contentsOf: lookup(name, atTopLevelOf: n))
    }
    return result
  }

  /// Returns the top-level declarations of `m` introducing `name`.
  private mutating func lookup(
    _ name: Name, atTopLevelOf m: Program.ModuleIdentity
  ) -> [DeclarationIdentity] {
    var ds: [DeclarationIdentity] = []

    if let table = cache.moduleToIdentifierToDeclaration[m] {
      ds = table[name.identifier] ?? []
    } else {
      var table = Memos.LookupTable()
      extendLookupTable(&table, with: program[m].topLevelDeclarations)
      cache.moduleToIdentifierToDeclaration[m] = table
      ds = table[name.identifier] ?? []
    }

    refineLookupResults(&ds, matching: name)
    return ds
  }

  /// Returns the declarations introducing `name` in `s`.
  private mutating func lookup(
    _ name: Name, lexicallyIn s: ScopeIdentity
  ) -> [DeclarationIdentity] {
    var ds = declarations(lexicallyIn: s)[name.identifier] ?? []
    refineLookupResults(&ds, matching: name)
    return ds
  }

  /// Returns the declarations introducing `name` as a member of a trait visible from `scopeOfUse`.
  private mutating func lookup(
    _ name: Name, memberOfTraitVisibleFrom scopeOfUse: ScopeIdentity
  ) -> [(concept: TraitDeclaration.ID, members: [DeclarationIdentity])] {
    var result: [(concept: TraitDeclaration.ID, members: [DeclarationIdentity])] = []
    for d in traits(visibleFrom: scopeOfUse) {
      let ms = lookup(name, lexicallyIn: .init(node: d)).filter(resolvableWithQualification(_:))
      if !ms.isEmpty {
        result.append((concept: d, members: ms))
      }
    }
    return result
  }

  /// Removes from `results` the declarations whose names do not match `name`, substituting bundle
  /// declarations by the variant corresponding to `name.introducer` if it is defined.
  private mutating func refineLookupResults(
    _ results: inout [DeclarationIdentity], matching name: Name
  ) {
    // There's nothing to do if the name is simple.
    if name.isSimple || results.isEmpty { return }

    // Otherwise, remove results whose names do no match or select variants in bundles.
    results.compactMapInPlace { (d) in
      if name ~= program.name(of: d) {
        return d
      } else if let k = name.introducer, let v = program.variant(k, of: d) {
        return .init(v)
      } else {
        return nil
      }
    }
  }

  /// Returns `true` if `m` can be resolved with a qualified name expression.
  private func resolvableWithQualification(_ m: DeclarationIdentity) -> Bool {
    switch program.tag(of: m) {
    case GenericParameterDeclaration.self, UsingDeclaration.self:
      return false
    default:
      return true
    }
  }

  /// Returns the declarations lexically contained in the declaration of `t`.
  private mutating func declarations(nativeMembersOf t: AnyTypeIdentity) -> Memos.LookupTable {
    switch program.types[program.types.head(t)] {
    case let u as Enum:
      return declarations(lexicallyIn: .init(node: u.declaration))
    case let u as Struct:
      return declarations(lexicallyIn: .init(node: u.declaration))
    case let u as TypeAlias:
      return declarations(nativeMembersOf: u.aliasee)
    case let u as TypeApplication:
      return declarations(nativeMembersOf: u.abstraction)
    default:
      return .init()
    }
  }

  /// Returns the declarations directly contained in `s`.
  private mutating func declarations(lexicallyIn s: ScopeIdentity) -> Memos.LookupTable {
    if let table = cache.scopeToLookupTable[s] {
      return table
    } else {
      var table = Memos.LookupTable()
      extendLookupTable(&table, with: program.declarations(lexicallyIn: s))
      cache.scopeToLookupTable[s] = table
      return table
    }
  }

  /// Returns the extensions that are directly contained in `s`.
  private mutating func extensions(lexicallyIn s: ScopeIdentity) -> [ExtensionDeclaration.ID] {
    if let ds = cache.scopeToExtensions[s] {
      return ds
    } else {
      let ds = Array(program.declarations(of: ExtensionDeclaration.self, lexicallyIn: s))
      cache.scopeToExtensions[s] = ds
      return ds
    }
  }

  /// Returns the extensions that are at the top level of `f` or its imports.
  private mutating func extensions(
    visibleAtTopLevelOf f: Program.SourceFileIdentity
  ) -> [ExtensionDeclaration.ID] {
    if let ds = cache.sourceToExtensions[f.offset] {
      return ds
    } else {
      var ds = Array(program.collectTopLevel(ExtensionDeclaration.self, of: f.module))
      for m in imports(of: f) {
        ds.append(contentsOf: program.collectTopLevel(ExtensionDeclaration.self, of: m))
      }
      cache.sourceToExtensions[f.offset] = ds
      return ds
    }
  }

  /// Returns how to match a value of type `t` to apply the members of `d` in `s`.
  ///
  /// - Requires: The context clause of `t`, if present, has no usings.
  private mutating func applies(
    _ d: ExtensionDeclaration.ID, to t: AnyTypeIdentity, in s: ScopeIdentity
  ) -> SummonResult? {
    let u = extendeeType(d)
    let w = WitnessExpression(value: .reference(.direct(.init(d))), type: u)

    // Fast path: types are trivially equal.
    if t == u { return .init(witness: w, substitutions: .init()) }

    // Slow path: use the match judgement of implicit resolution to create a witness describing
    // "how" the type matches the extension.
    let (context, head) = program.types.contextAndHead(t)
    assert(context.usings.isEmpty)
    let thread = formThread(matching: w, to: head, in: .empty, delayedBy: 0)
    return takeSummonResults(from: [thread], in: s).uniqueElement
  }

  /// Returns the modules that are imported by `f`, which is in the module being typed.
  private mutating func imports(
    of f: Program.SourceFileIdentity
  ) -> [Program.ModuleIdentity] {
    if let table = cache.sourceToImports[f.offset] {
      return table
    } else {
      var table: [Program.ModuleIdentity] = []

      // Standard library is imported implicitly.
      if program[f.module].dependencies.contains(.standardLibrary) {
        let m = program.identity(module: .standardLibrary)
        assert(m != nil, "standard library is not loaded")
        table.append(m!)
      }

      for d in program[f].topLevelDeclarations {
        // Imports precede all other declarations.
        guard let i = program.cast(d, to: ImportDeclaration.self) else { break }
        // Ignore invalid imports.
        if let m = program.identity(module: .init(program[i].identifier.value)) { table.append(m) }
      }

      cache.sourceToImports[f.offset] = table
      return table
    }
  }

  /// Extends `m` so that it maps identifiers declared in `ds` to their declarations.
  private func extendLookupTable<T: Sequence<DeclarationIdentity>>(
    _ m: inout Memos.LookupTable, with ds: T
  ) {
    for d in ds {
      if let n = program.name(of: d) {
        m[n.identifier, default: []].append(d)
      }
    }
  }

  /// Returns the type defining the nominal scope that includes `s`, if any.
  private mutating func nominalScope(including s: ScopeIdentity) -> AnyTypeIdentity? {
    // Exit early if `s` is a file.
    guard let n = s.node else { return nil }

    // Only types have nominal scopes.
    switch program.tag(of: n) {
    case StructDeclaration.self:
      return demand(Struct(declaration: castUnchecked(n))).erased
    case TraitDeclaration.self:
      return demand(Trait(declaration: castUnchecked(n))).erased
    default:
      return nil
    }
  }

  /// Returns the declarations of the traits that are visible from `scopeOfUse`.
  private mutating func traits(
    visibleFrom scopeOfUse: ScopeIdentity
  ) -> [TraitDeclaration.ID] {
    if let ts = cache.scopeToTraits[scopeOfUse] {
      return ts
    }

    // Are we in the scope of a syntax tree?
    else if let p = program.parent(containing: scopeOfUse) {
      let ds = program.declarations(lexicallyIn: scopeOfUse)
      var ts = traits(visibleFrom: p)
      ts.append(contentsOf: program.collect(TraitDeclaration.self, in: ds))
      cache.scopeToTraits[scopeOfUse] = ts
      return ts
    }

    // We are at the top-level.
    else {
      let ds = program[scopeOfUse.file.module].topLevelDeclarations
      var ts = Array(program.collect(TraitDeclaration.self, in: ds))
      for m in imports(of: scopeOfUse.file) {
        ts.append(contentsOf: program.collectTopLevel(TraitDeclaration.self, of: m))
      }
      cache.scopeToTraits[scopeOfUse] = ts
      return ts
    }
  }

  /// If `p` refers to an extractor used to on a scrutinee of type `s`, returns a pair `(d, ps)`
  /// where `d` is the declaration of that extractor and `ps` contain its parameters. Otherwise,
  /// reports a diagnostic and returns `nil`.
  private mutating func extractor(
    referredToBy p: ExtractorPattern.ID, matching s: AnyTypeIdentity
  ) -> (DeclarationIdentity, [Parameter])? {
    let t = check(program[p].extractor, inContextExpecting: s)

    // Is `p` referring to a valid extractor?
    guard
      let n = program.cast(program[p].extractor, to: NameExpression.self),
      let d = program[p.module].declaration(referredToBy: n)?.target
    else {
      return nil
    }

    switch program.tag(of: d) {
    case EnumCaseDeclaration.self:
      return (d, (program.types[t] as? Arrow)?.inputs ?? [])

    default:
      report(.error, "'\(program.nameOrTag(of: d))' is not a valid extractor", about: p)
      return nil
    }
  }

  // MARK: Standard library

  /// The value identifying an entity from the standard library.
  private enum StandardLibraryEntity: String, Hashable {

    /// `Hylo.Bool`.
    case bool = "Bool"

    /// `Hylo.Int`.
    case int = "Int"

    /// `Hylo.Int64`.
    case int64 = "Int64"

    /// `Hylo.Deinitializable`.
    case deinitializable = "Deinitializable"

    /// `Hylo.Equatable`.
    case equatable = "Equatable"

    /// `Hylo.Movable`.
    case movable = "Movable"

    /// `Hylo.ExpressibleByIntegerLiteral`.
    case expressibleByIntegerLiteral = "ExpressibleByIntegerLiteral"

    /// `Hylo.ExpressibleByIntegerLiteral.init(integer_literal:)`.
    case expressibyByIntegerLiteralInit = "ExpressibleByIntegerLiteral.init"

    /// Returns a selector for the declaration corresponding to `self`.
    var filter: SyntaxFilter {
      .symbol(rawValue)
    }

  }

  /// Returns `true` iff `t` is a standard library integer type (e.g., `Hylo.Int`).
  private mutating func isStandardLibraryIntegerType(_ t: AnyTypeIdentity) -> Bool {
    guard program.containsStandardLibrarySources else { return false }
    switch program.types.dealiased(t) {
    case standardLibraryType(.int):
      return true
    case standardLibraryType(.int64):
      return true
    default:
      return false
    }
  }

  /// Returns the type of the given standard library entity.
  ///
  /// The module containing the sources of the standard library must be present in the program but
  /// it does not have to be already type checked.
  private mutating func standardLibraryType(_ n: StandardLibraryEntity) -> AnyTypeIdentity {
    let d = standardLibraryDeclaration(n)
    let t = declaredType(of: d)
    let m = (program.types[t] as? Metatype) ?? fatalError("missing corrupt standard library")
    return m.inhabitant
  }

  /// Returns the declaration of the given standard library entity.
  ///
  /// The module containing the sources of the standard library must be present in the program but
  /// it does not have to be already type checked.
  private mutating func standardLibraryDeclaration(
    _ n: StandardLibraryEntity
  ) -> DeclarationIdentity {
    if let d = cache.standardLibraryDeclarations[n] { return d }

    guard
      let a = program.identity(module: .standardLibrary),
      let b = program.select(from: a, n.filter).uniqueElement,
      let d = program.castToDeclaration(b)
    else { fatalError("missing or corrupt standard library") }

    cache.standardLibraryDeclarations[n] = d
    return d
  }

  /// Returns `standardLibraryDeclaration(n)` cast as a `T`.
  private mutating func standardLibraryDeclaration<T: Declaration>(
    _ n: StandardLibraryEntity, as: T.Type
  ) -> T.ID {
    let d = standardLibraryDeclaration(n)
    return castUnchecked(d, to: T.self)
  }

  // MARK: Helpers

  /// Returns the unique identity of a type tree representing the metatype of `t`.
  private mutating func metatype<T: TypeTree>(of t: T) -> Metatype.ID {
    let n = demand(t).erased
    return demand(Metatype(inhabitant: n))
  }

  /// Returns the type of values expected to be returned or projected in `s`, or `nil` if `s` is
  /// not in the body of a function or subscript.
  private mutating func expectedOutputType(in s: ScopeIdentity) -> AnyTypeIdentity? {
    for t in program.scopes(from: s) {
      guard let n = t.node else { break }
      switch program.tag(of: n) {
      case FunctionDeclaration.self:
        return expectedOutputType(in: program.castUnchecked(n, to: FunctionDeclaration.self))
      default:
        continue
      }
    }
    return nil
  }

  /// Returns the type of values expected to be returned from `d`.
  private mutating func expectedOutputType(in d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    if let a = program.types[program.types.head(t)] as? Arrow {
      return a.output
    } else {
      return .error
    }
  }

  /// Returns the abstraction and argument of `w` if it is a coercion. Otherwise, returns `nil`.
  private func asCoercionApplication(
    _ w: WitnessExpression
  ) -> (coercion: WitnessExpression, argument: WitnessExpression)? {
    if case .termApplication(let a, let b) = w.value, program.types[a.type] is EqualityWitness {
      return (a, b)
    } else {
      return nil
    }
  }

  /// If `b`, which is the body of a routine, contains exactly one return statement, return that
  /// statemenr. Otherwise, returns `nil`.
  private func singleReturn(of b: [StatementIdentity]) -> Return.ID? {
    b.uniqueElement.flatMap({ (s) in program.cast(s, to: Return.self) })
  }

  /// If `b` contains exactly one statement that is an expression, returns that expression.
  /// Otherwise, returns `nil`.
  private func singleExpression(of b: [StatementIdentity]) -> ExpressionIdentity? {
    b.uniqueElement.flatMap(program.castToExpression(_:))
  }

  /// If `b` contains exactly one statement that is an expression, returns that expression.
  /// Otherwise, returns `nil`.
  private func singleExpression(of b: Block.ID) -> ExpressionIdentity? {
    singleExpression(of: program[b].statements)
  }

  /// Returns `b` if it is an if-expression or `singleExpression(of: b)` if it is a block.
  private func singleExpression(of b: If.ElseIdentity) -> ExpressionIdentity? {
    if let e = program.cast(b, to: If.self) {
      return .init(e)
    } else if let s = program.cast(b, to: Block.self) {
      return singleExpression(of: s)
    } else {
      program.unexpected(b)
    }
  }

  /// Returns `true` iff `e` has at least one case and all its cases are single-expression bodied.
  private func isSingleExpressionBodied(_ e: PatternMatch.ID) -> Bool {
    program[e].branches.allSatisfy({ (b) in program[b].body.count == 1 })
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// Reports a diagnostic related to `n` with the given level and message.
  private mutating func report<T: SyntaxIdentity>(_ l: Diagnostic.Level, _ m: String, about n: T) {
    report(.init(l, m, at: program.spanForDiagnostic(about: n)))
  }

  /// Returns the identity of a fresh type variable.
  private mutating func fresh() -> TypeVariable.ID {
    program.types.fresh()
  }

  /// Returns the unique identity of a tree that is equal to `t`.
  private mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    program.types.demand(t)
  }

  /// Returns `n` assuming it identifies a node of type `U`.
  private func castUnchecked<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type = U.self) -> U.ID {
    program.castUnchecked(n, to: U.self)
  }

  /// Returns the result of `action` called with a projection of `self` in which `d` is in the set
  /// of extensions to ignore during name resolution.
  private mutating func ignoring<T>(
    _ d: ExtensionDeclaration.ID, _ action: (inout Self) -> T
  ) -> T {
    declarationsOnStack.insert(.init(d))
    defer { declarationsOnStack.remove(.init(d)) }
    return action(&self)
  }

  /// Returns `true` iff the type of `g`'s declaration is not being computed.
  private func notOnStack(_ g: Given) -> Bool {
    switch g {
    case .user(let d):
      return !declarationsOnStack.contains(d)
    case .nested(_, let h):
      return notOnStack(h)
    default:
      return true
    }
  }

}
