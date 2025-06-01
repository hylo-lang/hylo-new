import StableCollections
import Utilities

/// A collection of types.
public struct TypeStore: Sendable {

  /// The index of a type in a store.
  public typealias Index = Int

  /// A policy for substituting variables during reification.
  public enum SubstitutionPolicy {

    /// Free variables are substituted by errors.
    case substitutedByError

    /// Free variables are kept.
    case kept

  }

  /// The types contained in this store.
  private var types: StableSet<AnyTypeTree>

  /// The identifier of the next fresh variable.
  private var nextFreshIdentifier: Int

  /// Creates an empty instance.
  public init() {
    self.types = []
    self.nextFreshIdentifier = 0
  }

  /// Returns the identity of a fresh type variable.
  public mutating func fresh() -> TypeVariable.ID {
    defer { nextFreshIdentifier += 1 }
    return .init(uncheckedFrom: AnyTypeIdentity(variable: nextFreshIdentifier))
  }

  /// Returns the identity of `Hylo.Never`, which is equivalent to `<T> T`.
  public mutating func never() -> UniversalType.ID {
    let p = demand(GenericParameter.nth(0, .proper))
    let t = demand(UniversalType(parameters: [p], body: p.erased))
    return t
  }

  /// Inserts `t` in `self` it isn't already present and returns the identity of an equal tree.
  public mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    .init(uncheckedFrom: demand(any: t))
  }

  /// Inserts `t` in `self` it isn't already present and returns the identity of an equal tree.
  internal mutating func demand(any t: any TypeTree) -> AnyTypeIdentity {
    switch t {
    case is ErrorType:
      return AnyTypeIdentity.error
    case let u as Tuple where u.elements.isEmpty:
      return AnyTypeIdentity.void
    case let u as TypeVariable:
      return AnyTypeIdentity(variable: u.identifier)
    default:
      let i = types.insert(.init(t)).position
      assert(i < (1 << 55), "too many types")  // 8 bits are reserved for the properties.
      return .init(offset: i, properties: t.properties)
    }
  }

  /// Returns the tag of `n`.
  public func tag<T: TypeIdentity>(of n: T) -> TypeTag {
    .init(type(of: self[n]))
  }

  /// Returns `true` iff `n` identifies the type of an equality witness.
  public func isEquality<T: TypeIdentity>(_ n: T) -> Bool {
    tag(of: n) == EqualityWitness.self
  }

  /// Returns `true` iff `n` identifies a non-nominal type (e.g., a tuple).
  public func isStructural<T: TypeIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
    case Sum.self, Tuple.self:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `n` identifies a metatype whose inhabitant satifies `predicate`.
  public func isMetatype<T: TypeIdentity>(
    _ n: T, of predicate: (AnyTypeIdentity) -> Bool
  ) -> Bool {
    if let m = self[n] as? Metatype {
      return predicate(m.inhabitant)
    } else {
      return false
    }
  }

  /// Returns `true` iff `n` is the type of an entity callable with the given style.
  public func isCallable<T: TypeIdentity>(_ n: T, _ style: Call.Style) -> Bool {
    if let w = seenAsCallableAbstraction(n) {
      return w.style == style
    } else {
      return false
    }
  }

  /// Returns `true` iff `n` is the type of an entity callable with the given style and labels.
  public func isCallable<T: TypeIdentity, S: Collection<String?>>(
    _ n: T, _ style: Call.Style, withLabels labels: S
  ) -> Bool {
    if let w = seenAsCallableAbstraction(n) {
      return (w.style == style) && w.labelsCompatible(with: labels)
    } else {
      return false
    }
  }

  /// Returns `true` iff `n` is a universal type or an implication.
  public func hasContext<T: TypeIdentity>(_ n: T) -> Bool {
    (tag(of: n) == UniversalType.self) || (tag(of: n) == Implication.self)
  }

  /// Returns `n` sans context clause.
  public func head<T: TypeIdentity>(_ n: T) -> AnyTypeIdentity {
    var h = n.erased
    while true {
      switch self[h] {
      case let t as UniversalType:
        h = t.body
      case let t as Implication:
        h = t.body
      default:
        return h
      }
    }
  }

  /// Returns the head and context clause of `n`.
  public func contextAndHead(
    _ n: AnyTypeIdentity
  ) -> (context: ContextClause, body: AnyTypeIdentity) {
    var p: [GenericParameter.ID] = []
    var u: [AnyTypeIdentity] = []
    var h = n

    while true {
      switch self[h] {
      case let t as UniversalType:
        p.append(contentsOf: t.parameters)
        h = t.body
      case let t as Implication:
        u.append(contentsOf: t.usings)
        h = t.body
      default:
        return (.init(parameters: p, usings: u), h)
      }
    }
  }

  /// Returns the implicit parameters and head of `n` opened for unification.
  public mutating func open(
    _ n: AnyTypeIdentity
  ) -> (usings: [AnyTypeIdentity], head: AnyTypeIdentity) {
    var u: [AnyTypeIdentity] = []
    var h = n

    while true {
      switch self[h] {
      case let t as UniversalType:
        let a = open(t.parameters)
        h = substitute(a, in: t.body)
      case let t as Implication:
        u.append(contentsOf: t.usings)
        h = t.body
      default:
        return (u, h)
      }
    }
  }

  /// Returns a table mapping each parameter in `ps` to a fresh unification variable.
  public mutating func open(_ ps: [GenericParameter.ID]) -> TypeArguments {
    .init(parametersWithValues: ps.map({ (p) in (p, fresh().erased) }))
  }

  /// Returns `body` as the head of a universal type and/or implication introducing `c`.
  public mutating func introduce(
    _ c: ContextClause, into body: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    let t = introduce(usings: c.usings, into: body)
    let u = introduce(parameters: c.parameters, into: t)
    return u
  }

  /// Returns `body` as the head of an implication having `lhs` on the left-hand side.
  public mutating func introduce(
    usings lhs: [AnyTypeIdentity], into body: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    lhs.isEmpty ? body : demand(Implication(context: lhs, head: body)).erased
  }

  /// Returns `body` as the head of a universal type introducing `ps`.
  public mutating func introduce(
    parameters ps: [GenericParameter.ID], into body: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    ps.isEmpty ? body : demand(UniversalType(parameters: ps, body: body)).erased
  }

  /// Returns `n` without its first requirement.
  public mutating func dropFirstRequirement(_ n: Implication.ID) -> AnyTypeIdentity {
    let i = self[n]
    if i.usings.count == 1 {
      return i.body
    } else {
      return demand(Implication(context: .init(i.usings.dropFirst()), head: i.body)).erased
    }
  }

  /// Returns the type parameters of `p`.
  public mutating func parameters(of p: GenericParameter.ID) -> [GenericParameter.ID] {
    var k = self[p].kind
    var p: [GenericParameter.ID] = []
    while let (a, b) = k.arrow {
      p.append(demand(GenericParameter.nth(p.count, a)))
      k = b
    }
    return p
  }

  /// Returns `n` if it identifies a tree of type `U`; otherwise, returns `nil`.
  public func cast<T: TypeIdentity, U: TypeTree>(_ n: T, to: U.Type) -> U.ID? {
    if type(of: self[n]) == U.self {
      return .init(uncheckedFrom: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` assuming it identifies a tree of type `U`.
  public func castUnchecked<T: TypeIdentity, U: TypeTree>(_ n: T, to: U.Type = U.self) -> U.ID {
    assert(type(of: self[n]) == U.self)
    return .init(uncheckedFrom: n.erased)
  }

  /// Returns properties of `n` iff it identifies the type of a callable abstraction.
  public func seenAsCallableAbstraction<T: TypeIdentity>(
    _ n: T
  ) -> Callable? {
    switch self[head(n)] {
    case let t as Arrow:
      return .init(style: .parenthesized, environment: t.environment, inputs: t.inputs)
    case let t as Bundle:
      return seenAsCallableAbstraction(t.shape)
    default:
      return nil
    }
  }

  /// Returns `(P, [A...])` iff `n` has the form `P<A...>`.
  public func seenAsTraitApplication<T: TypeIdentity>(
    _ n: T
  ) -> (concept: Trait.ID, arguments: TypeArguments)? {
    if
      let t = cast(n, to: TypeApplication.self),
      let u = cast(self[t].abstraction, to: Trait.self),
      !self[t].arguments.isEmpty
    {
      return (concept: u, arguments: self[t].arguments)
    } else {
      return nil
    }
  }

  /// Returns `[Void](A...) -> T)` iff `n` has the form `[Void](self: set T, A...) -> Void`.
  public mutating func asConstructor(_ n: AnyTypeIdentity) -> AnyTypeIdentity? {
    let (c, h) = contextAndHead(n.erased)
    guard
      let f = self[h] as? Arrow,
      let s = f.inputs.first,
      (f.environment == .void) && (f.output == .void) && (s.access == .set) && (s.label == "self")
    else { return nil }

    let adapted = Arrow(
      inputs: Array(f.inputs[1...]),
      output: s.type)

    let t = demand(adapted).erased
    return introduce(c, into: t).erased
  }

  /// Returns `[{self: k T}](A...) k -> B` iff `n` has the form `[Void](self: k T, A...) x -> B`.
  public mutating func asBoundMemberFunction(_ n: AnyTypeIdentity) -> AnyTypeIdentity? {
    let (c, h) = contextAndHead(n.erased)

    // `n` identifies a function?
    if let a = cast(h, to: Arrow.self) {
      if let adapted = asBoundMemberFunction(a) {
        return introduce(c, into: adapted.erased)
      } else {
        return nil
      }
    }

    // `n` identifies a function bundle?
    else if let b = cast(h, to: Bundle.self) {
      if let a = cast(self[b].shape, to: Arrow.self), let shape = asBoundMemberFunction(a) {
        let adapted = demand(Bundle(shape: shape.erased, variants: self[b].variants))
        return introduce(c, into: adapted.erased)
      } else {
        return nil
      }
    }

    // `n` is not a member function.
    else { return nil }
  }

  /// Returns `[{self: k T}](A...) k -> B` iff `n` has the form `[Void](self: k T, A...) x -> B`.
  private mutating func asBoundMemberFunction(_ n: Arrow.ID) -> Arrow.ID? {
    let f = self[n]
    guard let s = f.inputs.first, (f.environment == .void) && (s.label == "self") else {
      return nil
    }

    let capture = demand(RemoteType(projectee: s.type, access: s.access)).erased
    let environment = demand(Tuple(elements: [.init(label: "self", type: capture)])).erased
    let adapted = Arrow(
      effect: f.effect,
      environment: environment,
      inputs: Array(f.inputs[1...]),
      output: f.output)

    return demand(adapted)
  }

  /// Returns the type of the result of applying an instance of `callable`, with a mutable callee
  /// and/or arguments iff `isAppliedMutably` is `true`.
  public mutating func resultOfApplying(
    _ callable: AnyTypeIdentity, mutably isAppliedMutably: Bool
  ) -> AnyTypeIdentity? {
    switch self[callable] {
    case let t as Arrow:
      return t.output

    case let t as Bundle:
      // Are we looking for the result of applying a non-mutating variant of a function bundle?
      if !isAppliedMutably, let u = cast(t.shape, to: Arrow.self) {
        if let k = t.variants.intersection(.functional).first {
          let adapted = variant(k, of: u)
          return self[adapted].output
        } else {
          return nil
        }
      }

      // Otherwise, the result is the same as that of the underlying shape.
      else if !t.variants.intersection(.inplace).isEmpty {
        return resultOfApplying(t.shape, mutably: isAppliedMutably)
      } else {
        return nil
      }

    default:
      return nil
    }
  }

  /// Returns the type of the variant `k` of a bundle of type `n`.
  ///
  /// This method returns a copy of `n` in which occurrences of the `auto` effect are substituted
  /// for `k` and, iff `k` is non-mutating, the return type is the original return type along with
  /// the types of the values notionally modified by the bundle.
  ///
  /// For example, given a type `[{x: auto A}](y: auto B) auto -> C`, this method returns
  /// - `[{x: let A}](y: let B) let -> {A, B, C}` with `k == .let`; and
  /// - `[{x: set A}](y: set B) set -> C` with `k == .set`.
  ///
  /// - Requires: `n` is the type of a function bundle.
  public mutating func variant(_ k: AccessEffect, of n: Arrow.ID) -> Arrow.ID {
    assert(k != .auto, "invalid variant effect")
    assert(self[n].effect == .auto, "not a bundle")

    /// The types of the adapted inputs.
    var inputs: [Parameter] = []
    /// The type of the adapted environment.
    var environment: AnyTypeIdentity = .void
    /// The types of the values that appear in the return type of a non-mutating variant.
    var updates: [Tuple.Element] = []

    if let x = self[self[n].environment] as? Tuple {
      var es: [Tuple.Element] = []
      for e in x.elements {
        if let t = self[e.type] as? RemoteType, t.access == .auto {
          let u = demand(RemoteType(projectee: t.projectee, access: k)).erased
          es.append(.init(label: e.label, type: u))
          if k.isNonMutating { updates.append(.init(label: nil, type: t.projectee)) }
        } else {
          es.append(e)
        }
      }
      environment = demand(Tuple(elements: es)).erased
    } else {
      environment = self[n].environment
    }

    for p in self[n].inputs {
      if p.access == .auto {
        inputs.append(.init(label: p.label, access: k, type: p.type, defaultValue: p.defaultValue))
        if k.isNonMutating { updates.append(.init(label: nil, type: p.type)) }
      } else {
        inputs.append(p)
      }
    }

    let output = if k.isMutating {
      self[n].output
    } else {
      demand(Tuple(elements: updates + [.init(label: nil, type: self[n].output)])).erased
    }

    return demand(Arrow(effect: k, environment: environment, inputs: inputs, output: output))
  }

  /// Returns the value at `p` on the type identified by `n` if that type is an instance of `T`.
  /// Otherwise, returns `nil`.
  public func select<T: TypeTree, U>(_ n: AnyTypeIdentity, _ p: KeyPath<T, U>) -> U? {
    if let t = self[n] as? T {
      return t[keyPath: p]
    } else {
      return nil
    }
  }

  /// Returns the value at `p` on the type identified by `n` if that type is an instance of `T` and
  /// the value at `p` identifies an instance of `U`. Otherwise, returns `nil`.
  public func select<T: TypeTree, U: TypeTree>(
    _ n: AnyTypeIdentity, _ p: KeyPath<T, AnyTypeIdentity>, as: U.Type
  ) -> U.ID? {
    if let child = select(n, p) {
      return cast(child, to: U.self)
    } else {
      return nil
    }
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeIdentity>(n: T) -> any TypeTree {
    _read { yield self[n.erased] }
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeTree>(n: T.ID) -> T {
    self[n.erased] as! T
  }

  /// Projects the type identified by `n`.
  internal subscript(n: AnyTypeIdentity) -> any TypeTree {
    _read {
      switch n.offset {
      case AnyTypeIdentity.error.offset:
        yield ErrorType()
      case AnyTypeIdentity.void.offset:
        yield Tuple(elements: [])
      case let i where n.isVariable:
        yield TypeVariable(identifier: Int(UInt64(i) & ((1 << 54) - 1)))
      case let i:
        yield types[i].wrapped
      }
    }
  }

  /// Returns `n` transformed by `transform(_:_:)`.
  public mutating func map(
    _ n: AnyTypeIdentity,
    _ transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AnyTypeIdentity {
    switch transform(&self, n) {
    case .stepInto(let m):
      return modified(m, by: transform)
    case .stepOver(let m):
      return m
    }
  }

  /// Returns `r` transformed by `transform(_:_:)`.
  public mutating func map(
    _ r: DeclarationReference,
    _ transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> DeclarationReference {
    switch r {
    case .builtin, .direct, .member, .synthetic:
      return r
    case .inherited(let w, let d):
      return .inherited(self.map(w, transform), d)
    }
  }

  /// Returns `w` transformed by `transform(_:_:)`.
  public mutating func map(
    _ w: WitnessExpression,
    _ transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> WitnessExpression {
    let t = self.map(w.type, transform)

    switch w.value {
    case .identity(let e):
      return .init(value: .identity(e), type: t)

    case .abstract:
      return .init(value: .abstract, type: t)

    case .assumed(let i):
      return .init(value: .assumed(i), type: t)

    case .reference(let r):
      let u = self.map(r, transform)
      return .init(value: .reference(u), type: t)

    case .termApplication(let a, let b):
      let u = self.map(a, transform)
      let v = self.map(b, transform)
      return .init(value: .termApplication(u, v), type: t)

    case .typeApplication(let a, let b):
      let u = self.map(a, transform)
      let v = b.mapValues({ (n) in self.map(n, transform) })
      return .init(value: .typeApplication(u, v), type: t)

    case .nested(let a):
      let u = self.map(a, transform)
      return .init(value: .nested(u), type: t)
    }
  }

  /// Returns `n` with its parts transformed by `transform(_:_:)`.
  ///
  /// This operation is endomorphic: the result is an instance with the same type as `n`.
  public mutating func modified(
    _ n: AnyTypeIdentity,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AnyTypeIdentity {
    let t = self[n].modified(in: &self, by: transform)
    return demand(any: t)
  }

  /// Returns `n` without any type alias.
  public mutating func dealiased(_ n: AnyTypeIdentity) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if let a = s[t] as? TypeAlias {
        return .stepInto(a.aliasee)
      } else if t[.hasAliases] {
        return .stepInto(t)
      } else {
        return .stepOver(t)
      }
    }
  }

  /// Returns `n` with occurrences of applications of universal types β-reduced.
  public mutating func reduced(_ n: AnyTypeIdentity) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if let a = s[t] as? TypeApplication, let u = s[a.abstraction] as? UniversalType {
        assert(a.arguments.count == u.parameters.count)
        let ss = TypeArguments(mapping: u.parameters, to: a.arguments.values)
        return .stepInto(s.substitute(ss, in: u.body))
      } else {
        return .stepInto(t)
      }
    }
  }

  /// Returns `n` with each open variable substituted by either its corresponding value in
  /// `substitutions` or the application of `substitutionPolicy` if no such substitution exists.
  public mutating func reify(
    _ n: AnyTypeIdentity,
    applying substitutions: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy = .substitutedByError
  ) -> AnyTypeIdentity {
    let reified = self.map(n) { (s, t) in
      let u = substitutions[t]
      if !u.isVariable || substitutionPolicy == .kept {
        return u[.hasVariable] ? .stepInto(u) : .stepOver(u)
      } else {
        return .stepOver(.error)
      }
    }
    return reified == n ? n : reduced(reified)
  }

  /// Returns `r` with its open variables reified by `substitutions` and `substitutionPolicy`.
  public mutating func reify(
    _ r: DeclarationReference,
    applying substitutions: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy
  ) -> DeclarationReference {
    self.map(r) { (s, t) in
      .stepOver(s.reify(t, applying: substitutions, withVariables: substitutionPolicy))
    }
  }

  /// Returns `w` with its open variables reified by `substitutions` and `substitutionPolicy`.
  public mutating func reify(
    _ w: WitnessExpression,
    applying substitutions: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy
  ) -> WitnessExpression {
    self.map(w) { (s, t) in
      .stepOver(s.reify(t, applying: substitutions, withVariables: substitutionPolicy))
    }
  }

  /// Returns `n` with the keys in `substitutions` substituted for their corresponding values.
  public mutating func substitute(
    _ substitutions: [AnyTypeIdentity: AnyTypeIdentity], in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if let u = substitutions[t] { .stepOver(u) } else { .stepInto(t) }
    }
  }

  /// Returns `n` with the keys in `substitutions` substituted for their corresponding values.
  public mutating func substitute(
    _ substitutions: TypeArguments, in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      // The uncheked cast is okay because type of an identity is irrelevant to `Hashable`.
      if let u = substitutions[.init(uncheckedFrom: t)] { .stepOver(u) } else { .stepInto(t) }
    }
  }

  /// Returns `n` with unification variables substituted for an error.
  public mutating func substituteVariableForError(in n: AnyTypeIdentity) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if t.isVariable {
        return .stepOver(.error)
      } else {
        return t[.hasVariable] ? .stepInto(t) : .stepOver(t)
      }
    }
  }

  /// Returns a substitution table that makes `lhs` and `rhs` equal modulo substitution of their
  /// open variables.
  public func unifiable(_ lhs: AnyTypeIdentity, _ rhs: AnyTypeIdentity) -> SubstitutionTable? {
    var s = SubstitutionTable()
    if unifiable(lhs, rhs, extending: &s, handlingCoercionsWith: { (_, _) in false }) {
      return s
    } else {
      return nil
    }
  }

  /// Returns `true` if `lhs` and `rhs` can be made equal, recording substitutions of unification
  /// variables in `ss` and calling `areCoercible` to resolve non-syntactically equalities.
  public func unifiable(
    _ lhs: AnyTypeIdentity, _ rhs: AnyTypeIdentity, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    let a = ss[lhs]
    let b = ss[rhs]

    // The two types are trivially equal?
    if a == b { return true }

    // There are type variables?
    else if a.isVariable {
      ss.assign(b, to: .init(uncheckedFrom: a))
      return true
    } else if b.isVariable {
      ss.assign(a, to: .init(uncheckedFrom: b))
      return true
    }

    /// There are aliases?
    else if let t = self[a] as? TypeAlias {
      return unifiable(t.aliasee, b, extending: &ss, handlingCoercionsWith: areCoercible)
    } else if let u = self[b] as? TypeAlias {
      return unifiable(a, u.aliasee, extending: &ss, handlingCoercionsWith: areCoercible)
    }

    // The two types have the same shape?
    let result: Bool
    switch (self[a], self[b]) {
    case (let t as Arrow, let u as Arrow):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (_ as AssociatedType, _ as AssociatedType):
      result = false
    case (let t as Bundle, let u as Bundle):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (let t as EqualityWitness, let u as EqualityWitness):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (_ as ErrorType, _ as ErrorType):
      result = false
    case (let t as EqualityWitness, let u as EqualityWitness):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (_ as GenericParameter, _ as GenericParameter):
      result = false
    case (let t as Implication, let u as Implication):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (_ as MachineType, _ as MachineType):
      result = false
    case (_ as Metakind, _ as Metakind):
      result = false
    case (let t as Metatype, let u as Metatype):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (_ as Namespace, _ as Namespace):
      result = false
    case (let t as OpaqueType, let u as OpaqueType):
      result = false
    case (let t as RemoteType, let u as RemoteType):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (_ as Struct, _ as Struct):
      result = false
    case (_ as Trait, _ as Trait):
      result = false
    case (let t as Sum, let u as Sum):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (let t as Tuple, let u as Tuple):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (let t as TypeApplication, let u as TypeApplication):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    case (let t as UniversalType, let u as UniversalType):
      result = unifiable(t, u, extending: &ss, handlingCoercionsWith: areCoercible)
    default:
      assert(tag(of: a) != tag(of: b))
      result = false
    }

    return result || areCoercible(a, b)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Arrow, _ rhs: Arrow, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.effect == rhs.effect)
      && lhs.labels.elementsEqual(rhs.labels)
      && unifiable(
        lhs.environment, rhs.environment, extending: &ss, handlingCoercionsWith: areCoercible)
      && unifiable(
        lhs.inputs, rhs.inputs, extending: &ss,
        by: { (a, b, s) in unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible) })
      && unifiable(
        lhs.output, rhs.output, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Bundle, _ rhs: Bundle, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.variants == rhs.variants)
      && unifiable(lhs.shape, rhs.shape, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: EqualityWitness, _ rhs: EqualityWitness, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.lhs, rhs.lhs, extending: &ss, handlingCoercionsWith: areCoercible)
      && unifiable(lhs.rhs, rhs.rhs, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Implication, _ rhs: Implication, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.usings, rhs.usings, extending: &ss, handlingCoercionsWith: areCoercible)
      && unifiable(lhs.body, rhs.body, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Metatype, _ rhs: Metatype, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(
      lhs.inhabitant, rhs.inhabitant, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: RemoteType, _ rhs: RemoteType, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.access == rhs.access)
      && unifiable(
        lhs.projectee, rhs.projectee, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Tuple, _ rhs: Tuple, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.elements, rhs.elements, extending: &ss) { (a, b, s) in
      unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible)
    }
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Parameter, _ rhs: Parameter, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.label == rhs.label)
      && (lhs.access == rhs.access)
      && unifiable(lhs.type, rhs.type, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Sum, _ rhs: Sum, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.elements, rhs.elements, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: TypeApplication, _ rhs: TypeApplication, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(
      lhs.abstraction, rhs.abstraction, extending: &ss, handlingCoercionsWith: areCoercible)
      && unifiable(
        lhs.arguments.values, rhs.arguments.values, extending: &ss,
        by: { (a, b, s) in unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible) })
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: UniversalType, _ rhs: UniversalType, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    lhs.parameters.elementsEqual(rhs.parameters)
      && unifiable(lhs.body, rhs.body, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Tuple.Element, _ rhs: Tuple.Element, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.label == rhs.label)
      && unifiable(lhs.type, rhs.type, extending: &ss, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if the the pairwise elements of `lhs` and `rhs` are unifiable.
  private func unifiable<T: Sequence<AnyTypeIdentity>>(
    _ lhs: T, _ rhs: T, extending ss: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs, rhs, extending: &ss) { (a, b, s) in
      unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible)
    }
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable<T: Sequence>(
    _ lhs: T, _ rhs: T, extending ss: inout SubstitutionTable,
    by unify: (T.Element, T.Element, inout SubstitutionTable) -> Bool
  ) -> Bool {
    var i = lhs.makeIterator()
    var j = rhs.makeIterator()
    while let a = i.next() {
      guard let b = j.next(), unify(a, b, &ss) else { return false }
    }
    return j.next() == nil
  }

}

/// The result of a call to a closure passed to `TypeStore.transform(_:)`.
public enum TypeTransformAction {

  case stepInto(AnyTypeIdentity)

  case stepOver(AnyTypeIdentity)

}

/// A closure returning `true` if its first argument can be coerced to the second.
public typealias CoercionHandler = (
  _ lhs: AnyTypeIdentity,
  _ rhs: AnyTypeIdentity
) -> Bool
