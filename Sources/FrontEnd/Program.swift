import Archivist
import OrderedCollections
import Utilities

/// A Hylo program.
public struct Program: Sendable {

  /// The modules loaded in this program.
  public private(set) var modules = OrderedDictionary<Module.Name, Module>()

  /// The types in the program.
  public internal(set) var types = TypeStore()

  /// The memoization caches of type inference and name resolution.
  ///
  /// This table is used by `Typer` to persist its state throughout the compilation pipeline.
  internal var typingCache: [Module.ID: Typer.Memos] = [:]

  /// The cache of `standardLibraryDeclaration(_:)`.
  ///
  /// This table is initialized either by `Typer.apply` before the standard library is type checked
  /// or by `self.load(module:from:)` after the standard library has been deserialized.
  private var standardLibraryDeclarations: [StandardLibraryEntity: DeclarationIdentity] = [:]

  /// Creates an empty program.
  public init() {}

  /// `true` if the program has errors.
  public var containsError: Bool {
    modules.values.contains(where: \.containsError)
  }

  /// The diagnostics of the issues in the program.
  public var diagnostics: some Collection<Diagnostic> {
    modules.values.map(\.diagnostics).joined()
  }

  /// Returns the identities of the modules in `self`.
  public var moduleIdentities: Range<Module.ID> {
    modules.values.indices
  }

  /// Returns `true` iff the module containing the the standard library is present.
  public var containsStandardLibrary: Bool {
    if let i = identity(module: .standardLibrary) {
      return !self[i].sources.isEmpty
    } else {
      return false
    }
  }

  /// Returns the identity of the module named `moduleName`.
  public mutating func demandModule(_ moduleName: Module.Name) -> Module.ID {
    if let m = modules.index(forKey: moduleName) {
      return m
    } else {
      let m = modules.count
      modules[moduleName] = Module(name: moduleName, identity: m)
      return m
    }
  }

  /// Returns the identity of the module named `moduleName` or `nil` if no such module exists.
  public func identity(module moduleName: Module.Name) -> Module.ID? {
    modules.index(forKey: moduleName)
  }

  /// Computes the scoping relationships in `m`.
  public mutating func assignScopes(_ m: Module.ID) async {
    await Scoper().visit(m, of: &self)
  }

  /// Re-compute the scoping relationships of `n`'s immediate children.
  public mutating func reassignScopes<T: SyntaxIdentity>(childrenOf n: T) {
    for c in children(n) {
      self[c.file].syntaxToParent[c.offset] = n.offset
    }
  }

  /// Assigns types to the syntax trees of `m`.
  public mutating func assignTypes(_ m: Module.ID) {
    var typer = Typer(typing: m, of: consume self)
    typer.apply()
    self = typer.release()
  }

  /// Lowers the contents of `m` to IR.
  public mutating func lower(_ m: Module.ID) {
    // Generate raw IR from the syntax tree.
    var emitter = IREmitter(insertingIn: m, of: consume self)
    emitter.incorporateTopLevelDeclarations()
    self = emitter.release()

    // Apply transformation passes.
    withTyper(typing: m) { (typer) in
      // Temporarily move all functions to a local work list.
      var work: [IRFunction] = []
      modify(&typer.program[typer.module]) { (module) in
        work = module.ir.values.indices.map({ (f) in module.takeFunction(f) })
      }

      let never = typer.program.types.never()

      // Mandatory intra-procedural passes.
      for i in work.indices where work[i].isDefined {
        work[i].foldRedundantInstructions()
        work[i].simplifyControlFlow()
        work[i].removeCodeAfterCallsReturning(never: never.erased)
        work[i].removeUnreachableBlocks()
        work[i].removedUnusedDefinitions()
        // reifyBundles
        // reifyAccesses
        work[i].closeOpenEndedRegions()
        work[i].normalizeLifetimes(emittingInto: m, using: &typer)
      }

      // Move all functions back.
      modify(&typer.program[typer.module]) { (module) in
        for f in module.ir.values.indices.reversed() {
          module.reassignFunction(work.removeLast(), to: f)
        }
      }
    }
  }

  /// Returns the result of calling `action` on a typer configured with `module`.
  public mutating func withTyper<T>(
    typing m: Module.ID, _ action: (inout Typer) -> T
  ) -> T {
    var typer = Typer(typing: m, of: consume self)
    defer { self = typer.release() }
    return action(&typer)
  }

  internal mutating func withEmitter<T>(
    insertingIn m: Module.ID, _ action: (inout IREmitter) -> T
  ) -> T {
    var emitter = IREmitter(insertingIn: m, of: consume self)
    defer { self = emitter.release() }
    return action(&emitter)
  }

  /// Projects the module identified by `m`.
  public subscript(m: Module.ID) -> Module {
    _read { yield modules.values[m] }
    _modify { yield &modules.values[m] }
  }

  /// Projects the source file identified by `f`.
  internal subscript(f: SourceFile.ID) -> Module.SourceContainer {
    _read { yield modules.values[f.module][f] }
    _modify { yield &modules.values[f.module][f] }
  }

  /// Projects the node identified by `n`.
  public subscript<T: SyntaxIdentity>(n: T) -> any Syntax {
    _read { yield modules.values[n.module][n] }
  }

  /// Projects the node identified by `n`.
  public subscript<T: Syntax>(n: T.ID) -> T {
    modules.values[n.module][n]
  }

  /// Returns the nodes that are immediate children of `n`.
  public func children<T: SyntaxIdentity>(_ n: T) -> [AnySyntaxIdentity] {
    var enumerator = ChildrenEnumerator(parent: n.erased)
    visit(n, calling: &enumerator)
    return enumerator.children
  }

  /// Returns the value at `p` on the type identified by `n` if that type is an instance of `T`.
  /// Otherwise, returns `nil`.
  public func read<T: Syntax, U>(_ n: AnySyntaxIdentity, _ p: KeyPath<T, U>) -> U? {
    if let t = self[n] as? T {
      return t[keyPath: p]
    } else {
      return nil
    }
  }

  /// Returns the elements in `ns` that identify nodes of type `T`.
  public func collect<S: Sequence, T: Syntax>(
    _ t: T.Type, in ns: S
  ) -> (some Sequence<ConcreteSyntaxIdentity<T>>) where S.Element: SyntaxIdentity {
    ns.lazy.compactMap({ (n) in cast(n, to: t) })
  }

  /// Returns the top level declarations of `m` that are of type `T`.
  public func collectTopLevel<T: Syntax>(
    _ t: T.Type, of m: Module.ID
  ) -> (some Sequence<ConcreteSyntaxIdentity<T>>) {
    collect(t, in: self[m].topLevelDeclarations)
  }

  /// Returns a textual representation of `item` using the given configuration.
  public func show<T: Showable>(
    _ item: T, configuration: TreePrinter.Configuration = .default
  ) -> String {
    var printer = TreePrinter(program: self, configuration: configuration)
    return printer.show(item)
  }

  /// Returns a textual representation of `items` using the given configuration and separating each
  /// element by `separator`.
  public func show<T: Sequence>(
    _ items: T, configuration: TreePrinter.Configuration = .default,
    separatedBy separator: String = ", "
  ) -> String where T.Element: Showable {
    var printer = TreePrinter(program: self, configuration: configuration)
    return printer.show(items, separatedBy: separator)
  }

  /// Returns the tag of `n`.
  public func tag<T: SyntaxIdentity>(of n: T) -> SyntaxTag {
    modules.values[n.module].tag(of: n)
  }

  /// `true` iff `f` has gone through scoping.
  public func isScoped(_ f: SourceFile.ID) -> Bool {
    self[f].syntaxToParent.count == self[f].syntax.count
  }

  /// Returns `true` iff `s` contains the innermost scope that strictly contains `n`.
  public func isContained<T: SyntaxIdentity>(_ n: T, in s: ScopeIdentity) -> Bool {
    // If `s` is a file, just look if `n` is in that file too.
    guard let q = s.node else { return n.file == s.file }

    // Otherwise, walk the scope hierarchy.
    var next = parent(containing: n)
    while let p = next.node {
      if p == q { return true }
      next = parent(containing: p)
    }
    return false
  }

  /// Returns `true` iff `n` denotes a declaration.
  public func isDeclaration<T: SyntaxIdentity>(_ n: T) -> Bool {
    tag(of: n).value is any Declaration.Type
  }

  /// Returns `true` iff `n` denotes a type declaration.
  public func isTypeDeclaration<T: SyntaxIdentity>(_ n: T) -> Bool {
    tag(of: n).value is any TypeDeclaration.Type
  }

  //// Returns `true` iff `n` denotes an extension or conformance declaration.
  public func isTypeExtendingDeclaration<T: SyntaxIdentity>(_ n: T) -> Bool {
    tag(of: n).value is any TypeExtendingDeclaration.Type
  }

  /// Returns `true` iff `n` introduces a name that can be overloaded.
  public func isOverloadable<T: SyntaxIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
    case FunctionDeclaration.self:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `n` denotes a scope.
  public func isScope<T: SyntaxIdentity>(_ n: T) -> Bool {
    tag(of: n).value is any Scope.Type
  }

  /// Returns `true` iff `n` is a trait requirement.
  ///
  /// - Rquires: The module containing `n` is scoped.
  public func isRequirement<T: SyntaxIdentity>(_ n: T) -> Bool {
    traitRequiring(n) != nil
  }

  /// Returns `true` iff `n` introduces entities in the implicit context.
  public func isImplicit<T: SyntaxIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
    case BindingDeclaration.self:
      return self[castUnchecked(n, to: BindingDeclaration.self)].isImplicit
    case ConformanceDeclaration.self:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `n` declares a member in an type extension.
  ///
  /// - Rquires: The module containing `n` is scoped.
  public func isExtensionMember<T: SyntaxIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
    case FunctionDeclaration.self:
      return parent(containing: n, as: ExtensionDeclaration.self) != nil
    default:
      return false
    }
  }

  /// Returns `true` iff `n` declares a non-static member entity.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func isMember<T: SyntaxIdentity>(_ n: T) -> Bool {
    guard let m = parent(containing: n).node else { return false }

    switch tag(of: n) {
    case VariantDeclaration.self:
      return isMember(m)
    default:
      return !isStatic(n) && (isTypeDeclaration(m) || isTypeExtendingDeclaration(m))
    }
  }

  /// Returns `true` iff `n` declares a non-static member function or function bundle.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func isMemberFunction<T: SyntaxIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
    case FunctionBundleDeclaration.self:
      return isMember(n)
    case FunctionDeclaration.self:
      return isMember(n)
    case VariantDeclaration.self:
      return isMember(n)
    default:
      return false
    }
  }

  /// Returns `true` iff `n` declares a memberwise initializer.
  public func isMemberwiseInitializer<T: SyntaxIdentity>(_ n: T) -> Bool {
    if let d = cast(n, to: FunctionDeclaration.self) {
      return self[d].isMemberwiseInitializer
    } else {
      return false
    }
  }

  /// Returns `true` iff `n` declares a static member entity.
  public func isStatic<T: SyntaxIdentity>(_ n: T) -> Bool {
    // Note: the following relies on the fact that non-member declarations can't be `static`, which
    // is an invariant of syntactically well-formed ASTs.
    switch tag(of: n) {
    case BindingDeclaration.self:
      return self[castUnchecked(n, to: BindingDeclaration.self)].is(.static)
    case EnumCaseDeclaration.self:
      return true
    case FunctionBundleDeclaration.self:
      return self[castUnchecked(n, to: FunctionBundleDeclaration.self)].is(.static)
    case FunctionDeclaration.self:
      return self[castUnchecked(n, to: FunctionDeclaration.self)].is(.static)
    default:
      return false
    }
  }

  /// Returns `true` iff `n` is defined in the context of a function.
  public func isLocal<T: SyntaxIdentity>(_ n: T) -> Bool {
    var s = parent(containing: n)
    while let p = s.node {
      switch tag(of: p) {
      case FunctionDeclaration.self, VariantDeclaration.self:
        return true
      case _ where isTypeDeclaration(n) || isTypeExtendingDeclaration(n):
        return false
      default:
         s = parent(containing: p)
      }
    }

    // Top-level functions aren't local.
    return false
  }

  /// Returns `true` iff `n` defines a symbol that is captured if referred to.
  public func isCapturable<T: SyntaxIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
    case ExtensionDeclaration.self:
      return false
    default:
      return !isTypeDeclaration(n) && isLocal(n)
    }
  }

  /// Returns `true` iff `n` is a an interface for a function written in another language.
  public func isForeign(_ n: FunctionDeclaration.ID) -> Bool {
    self[n].annotations.contains(where: { (a) in a.identifier.value == "foreign" })
  }

  /// Returns `true` iff `n` has an external implementation.
  public func isExtern(_ n: FunctionDeclaration.ID) -> Bool {
    self[n].annotations.contains(where: { (a) in a.identifier.value == "extern" })
  }

  /// Returns `true` iff `n` denotes an expression.
  public func isExpression<T: SyntaxIdentity>(_ n: T) -> Bool {
    tag(of: n).value is any Expression.Type
  }

  /// Returns `true` iff `n` is the expression of a value marked for mutation.
  public func isMarkedForMutation(_ n: ExpressionIdentity) -> Bool {
    var q = n
    while true {
      if tag(of: q) == InoutExpression.self {
        return true
      } else if let x = cast(q, to: NameExpression.self), let y = self[x].qualification {
        q = y
      } else if let x = cast(q, to: Call.self), self[x].style == .bracketed {
        q = self[x].callee
      } else {
        return false
      }
    }
  }

  /// Returns `true` iff `n` is modifying its callee and/or one of its arguments in place.
  public func isMutating(_ n: Call.ID) -> Bool {
    isMarkedForMutation(self[n].callee)
      || self[n].arguments.contains(where: { (a) in isMarkedForMutation(a.value) })
  }

  /// Returns `true` iff `n` is a name expression of the form  `.new` or `q.new`, where `q` is any
  /// arbitrary qualification.
  public func isConstructorReference(_ n: NameExpression.ID) -> Bool {
    if let m = cast(n, to: NameExpression.self) {
      return self[m].name.value.identifier == "new"
    } else {
      return false
    }
  }

  /// Returns `true` iff `w` denotes a synthetic conformance that does not involve any user code.
  public func isTransitivelySyntheticConformance(_ w: WitnessExpression) -> Bool {
    switch w.value {
    case .reference(let d):
      return isTransitivelySyntheticConformance(d)
    case .termApplication(let a, _), .typeApplication(let a, _):
      return isTransitivelySyntheticConformance(a)
    default:
      return false
    }
  }

  /// Returns `true` iff `r` denotes a synthetic conformance that does not involve any user code.
  private func isTransitivelySyntheticConformance(_ d: DeclarationIdentity) -> Bool {
    guard
      let x0 = cast(d, to: ConformanceDeclaration.self),
      let x1 = self[x0.module].implementations(definedBy: x0)
    else {
      // If the typer calls this method while the declaration referred to by `r` in on stack, we
      // can assume that it is checking a conformance defined for a self-referential type. Since
      // such types require some form of indirection, we can also assume that the conformance is
      // not transitively synthetic.
      return false
    }

    return x1.isTransitivelySynthetic
  }

  /// Returns `true` if the memory layout of `t` is visible from `scopeOfUse`.
  public mutating func isInlineable(_ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity) -> Bool {
    let u = types.dealiased(t)
    switch types.tag(of: u) {
    case Enum.self:
      return isInlineable((types[u] as! Enum).declaration, in: scopeOfUse)
    case Struct.self:
      return isInlineable((types[u] as! Struct).declaration, in: scopeOfUse)
    case Tuple.self:
      return true
    default:
      return false
    }
  }

  /// Returns `true` if the definition of `t` is visible from `scopeOfUse`.
  public func isInlineable<T: ModifiableDeclaration>(
    _ d: T.ID, in scopeOfUse: ScopeIdentity
  ) -> Bool {
    (d.module == scopeOfUse.module) || self[d].is(.inlineable)
  }

  /// Returns `n` if it identifies a node of type `U`; otherwise, returns `nil`.
  public func cast<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type) -> U.ID? {
    if tag(of: n) == .init(U.self) {
      return .init(uncheckedFrom: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` assuming it identifies a node of type `U`.
  public func castUnchecked<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type = U.self) -> U.ID {
    assert(tag(of: n) == .init(U.self))
    return .init(uncheckedFrom: n.erased)
  }

  /// Returns `n` if it identifies a declaration; otherwise, returns `nil`.
  public func castToDeclaration<T: SyntaxIdentity>(_ n: T) -> DeclarationIdentity? {
    if isDeclaration(n) {
      return .init(uncheckedFrom: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` if it identifies an expression; otherwise, returns `nil`.
  public func castToExpression<T: SyntaxIdentity>(_ n: T) -> ExpressionIdentity? {
    if isExpression(n) {
      return .init(uncheckedFrom: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` if it identifies a scope; otherwise, returns `nil`.
  public func castToScope<T: SyntaxIdentity>(_ n: T) -> ScopeIdentity? {
    if isScope(n) {
      return .init(uncheckedFrom: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `w` if it is the desugared form of a conformance type. Otherwise, returns `nil`.
  public func seenAsConformanceTypeExpression(_ w: StaticCall.ID) -> ConformanceTypeSugar? {
    Utilities.read(self[w], { (tree) in tree.arguments.isEmpty ? nil : .init(tree) })
  }

  /// Returns the built-in entity referred to by `n` iff it denotes the a built-in constructor for
  /// converting scalar literals.
  ///
  /// - Requires: The module containing `n` is typed.
  public func asBuiltinScalarLiteralConversion(_ n: ExpressionIdentity) -> StandardLibraryEntity? {
    guard
      containsStandardLibrary,
      let f = cast(n, to: New.self),
      case .inherited(let w, let m, true) = declaration(referredToBy: self[f].target),
      case .reference(let d) = w.value
    else { return nil }

    // Is the witness defined in the standard library?
    if parent(containing: d).module != identity(module: .standardLibrary) {
      return nil
    }

    switch m {
    case standardLibraryDeclaration(.expressibleByIntegerLiteralInit):
      return .expressibleByIntegerLiteralInit
    default:
      return nil
    }
  }

//  /// Returns `(n, p)` where `p` denotes the struct of which `n` is a member iff `n` declares a
//  /// stored property.
//  ///
//  /// - Requires: The module containing `s` is scoped.
//  public func asStoredPropertyDeclaration(
//    _ n: DeclarationIdentity
//  ) -> (declaration: VariableDeclaration.ID, parent: StructDeclaration.ID)? {
//    guard
//      let v = cast(n, to: VariableDeclaration.self),
//      let p = parent(containing: v, as: StructDeclaration.self)
//    else { return nil }
//    return (v, p)
//  }

  /// Returns the innermost scope that strictly contains `n`.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func parent(containing s: ScopeIdentity) -> ScopeIdentity? {
    s.node.map(parent(containing:))
  }

  /// Returns the innermost scope that strictly contains `n`.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func parent<T: SyntaxIdentity>(containing n: T) -> ScopeIdentity {
    assert(isScoped(n.file), "unscoped module")
    let p = self[n.file].syntaxToParent[n.offset]
    if p >= 0 {
      return .init(uncheckedFrom: .init(file: n.file, offset: p))
    } else {
      return .init(file: n.file)
    }
  }

  /// Returns the innermost scope that contains `n` iff it is an instance of `U`. Otherwise,
  /// returns `nil`.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func parent<T: SyntaxIdentity, U: Syntax>(containing n: T, as: U.Type) -> U.ID? {
    if let m = parent(containing: n).node {
      return cast(m, to: U.self)
    } else {
      return nil
    }
  }

  /// Returns the type assigned to `n`.
  ///
  /// - Requires: The module containing `n` is typed.
  public func type<T: SyntaxIdentity>(assignedTo n: T) -> AnyTypeIdentity {
    self[n.module].type(assignedTo: n) ?? unreachable("untyped node at \(self[n].site)")
  }

  /// Returns the type assigned to `n`, assuming it is an instance of `T`.
  ///
  /// - Requires: The module containing `n` is typed.
  public func type<T: SyntaxIdentity, U: TypeTree>(assignedTo n: T, assuming: U.Type) -> U.ID {
    let t = type(assignedTo: n)
    if let u = types.cast(t, to: U.self) {
      return u
    } else {
      unreachable("expected node of type '\(U.self)'; found '\(types.tag(of: t))'")
    }
  }

  /// Returns the declaration referred to by `n`.
  ///
  /// - Requires: The module containing `n` is typed.
  public func declaration(referredToBy n: NameExpression.ID) -> DeclarationReference {
    self[n.module].declaration(referredToBy: n) ?? unreachable("untyped node at \(self[n].site)")
  }

  public func occurs<T: SyntaxIdentity>(referenceTo d: DeclarationIdentity, in n: T) -> Bool {
    switch tag(of: n) {
    case NameExpression.self:
      return declaration(referredToBy: castUnchecked(n)).target == d
    default:
      return children(n).contains(where: { (c) in occurs(referenceTo: d, in: c) })
    }
  }

  /// Returns the associated type and member requirements of `t`.
  public func requirements(
    of t: Trait.ID
  ) -> (associatedTypes: [AssociatedTypeDeclaration.ID], members: [DeclarationIdentity]) {
    let concept = types[t].declaration
    var ts: [AssociatedTypeDeclaration.ID] = []
    var ms: [DeclarationIdentity] = .init(minimumCapacity: self[concept].members.count)
    for m in self[concept].members {
      if let a = cast(m, to: AssociatedTypeDeclaration.self) {
        ts.append(a)
      } else {
        ms.append(m)
      }
    }
    return (ts, ms)
  }

  /// Returns the witness table defined by `d`.
  ///
  /// - Requires: The module containing `d` is typed.
  public func implementations(definedBy d: ConformanceDeclaration.ID) -> WitnessTable {
    self[d.module].implementations(definedBy: d) ?? unreachable("untyped node at \(self[d].site)")
  }

  /// If `n` is a requirement, returns the traits that introduces it. Otherwise, returns `nil`.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func traitRequiring<T: SyntaxIdentity>(_ n: T) -> TraitDeclaration.ID? {
    switch tag(of: n) {
    case AssociatedTypeDeclaration.self:
      return parent(containing: n, as: TraitDeclaration.self)
    case ConformanceDeclaration.self:
      return parent(containing: n, as: TraitDeclaration.self)
    case FunctionDeclaration.self:
      return parent(containing: n, as: TraitDeclaration.self)
    case VariantDeclaration.self:
      return parent(containing: parent(containing: n).node!, as: TraitDeclaration.self)
    default:
      return nil
    }
  }

  /// Returns the innermost member declaration containing `s` that does not contain any type scope
  /// containing `s`, or `nil` if no such declaration exists.
  public func innermostMemberScope(from s: ScopeIdentity) -> ScopeIdentity? {
    var next: Optional = s
    while let n = next, let d = n.node {
      if isMember(d) {
        return n
      } else if isStatic(d) || isTypeDeclaration(d) || isTypeExtendingDeclaration(d) {
        return nil
      } else {
        next = parent(containing: n)
      }
    }
    return nil
  }

  /// Returns a sequence containing `s` and its ancestors, from inner to outer.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func scopes(from s: ScopeIdentity) -> some Sequence<ScopeIdentity> {
    var next: Optional = s
    return AnyIterator {
      if let n = next {
        next = n.node.map(parent(containing:))
        return n
      } else {
        return nil
      }
    }
  }

  /// Returns `true` iff `m` is considered to occur before `n` in diagnostics.
  ///
  /// If `m` and `n` are in the same file, they are ordered by the start of their source span. If
  /// they in different source files belonging to the same module, they are ordered by the names of
  /// these files. Otherwise, they are in ordered by the names of their containing modules.
  public func occurInOrder<T: SyntaxIdentity, U: SyntaxIdentity>(
    _ m: T, _ n: U
  ) -> Bool {
    if m.erased == n.erased {
      return false
    } else if m.file == n.file {
      let l = self[m].site.start
      let r = self[n].site.start
      return (l != r) ? (l < r) : (m.erased.bits < n.erased.bits)
    } else if m.module == n.module {
      return self[m.file].source.name.lexicographicallyPrecedes(self[n.file].source.name)
    } else {
      return self[m.module].name.lexicographicallyPrecedes(self[n.module].name)
    }
  }

  /// Retutns whether `m` or `n` is lexically closer to `s`.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func compareLexicalDistances<T: SyntaxIdentity, U: SyntaxIdentity>(
    _ m: T, _ n: U, relativeTo s: ScopeIdentity
  ) -> StrictOrdering {
    // Is `m` in the same module as `s`?
    if m.module == s.module {
      // `m` is closer if it has more ancestors or `n` is in another module.
      if n.module == s.module {
        return compareAncestors(m, n)
      } else {
        return .ascending
      }
    }

    // Is `n` in the same module as `s`?
    else if n.module == s.module {
      return .descending
    }

    // Otherwise, they have the same distance.
    else { return .equal }
  }

  /// Returns the result of the three-way comparison of the number of ancestors of `m` and `n`.
  ///
  /// - Requires: `m` and `n` are in the same module, which is scoped.
  public func compareAncestors<T: SyntaxIdentity, U: SyntaxIdentity>(
    _ m: T, _ n: U
  ) -> StrictOrdering {
    assert(m.module == n.module)

    var p = parent(containing: m)
    var q = parent(containing: n)
    while let a = p.node {
      if let b = q.node {
        p = parent(containing: a)
        q = parent(containing: b)
      } else {
        return .descending
      }
    }
    return q.node == nil ? .equal : .ascending
  }

  /// Returns the declarations directly contained in `s`.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func declarations(lexicallyIn s: ScopeIdentity) -> [DeclarationIdentity] {
    if let n = s.node {
      return self[n.file].scopeToDeclarations[n.offset] ?? preconditionFailure("unscoped module")
    } else {
      return self[s.file].topLevelDeclarations
    }
  }

  /// Returns the declarations directly contained in `s` that identify nodes of type `T`.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func declarations<T: Declaration>(
    of t: T.Type, lexicallyIn s: ScopeIdentity
  ) -> some Sequence<ConcreteSyntaxIdentity<T>> {
    collect(t, in: declarations(lexicallyIn: s))
  }

  /// Returns the declarations of the stored properties of `d`.
  ///
  /// The declarations are returned in the order of their occurrence in `d`. This order does not
  /// necessarily matches the layout of the struct after code generation.
  public func storedProperties(of d: StructDeclaration.ID) -> [VariableDeclaration.ID] {
    var result: [VariableDeclaration.ID] = []
    forEachStoredProperty(of: d, do: { (v, _) in result.append(v) })
    return result
  }

  /// Returns the binding declaration that contains `d`, if any.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func bindingDeclaration(containing d: VariableDeclaration.ID) -> BindingDeclaration.ID? {
    assert(isScoped(d.file), "unscoped module")
    return self[d.file].variableToBinding[d.offset]
  }

  /// Returns the names introduced by `d`.
  public func names(introducedBy d: BindingDeclaration.ID) -> [Name] {
    var result: [Name] = []
    forEachVariable(introducedBy: self[self[d].pattern].pattern) { (v, _) in
      result.append(.init(identifier: self[v].identifier.value))
    }
    return result
  }

  /// Returns a string describing the entity declared by `d`.
  public func debugName(of d: DeclarationIdentity) -> String {
    var result = [nameOrTag(of: d)]
    for s in scopes(from: self.parent(containing: d)) {
      if let n = s.node {
        if let d = castToDeclaration(n), let s = name(of: d)?.description {
          result.append(s)
        } else {
          result.append(tag(of: n).description)
        }
      }
    }
    return result.reversed().joined(separator: ".")
  }

  /// Returns the name of the unique entity declared by `d` or a description of `d`'s tag if it
  /// declares zero or more than one named entity.
  public func nameOrTag(of d: DeclarationIdentity) -> String {
    if let n = name(of: d) {
      return n.description
    } else {
      let s = self[d].site
      let (l, c) = s.start.lineAndColumn
      return "$<\(tag(of: d)) at \(s.source.baseName):\(l).\(c)>"
    }
  }

  /// Returns the name of the unique entity declared by `d`, or `nil` if `d` declares zero or more
  /// than one named entity.
  ///
  /// - Requires: The module containing `d` is scoped.
  public func name(of d: DeclarationIdentity) -> Name? {
    switch tag(of: d) {
    case AssociatedTypeDeclaration.self:
      return name(of: castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case EnumCaseDeclaration.self:
      return name(of: castUnchecked(d, to: EnumCaseDeclaration.self))
    case EnumDeclaration.self:
      return name(of: castUnchecked(d, to: EnumDeclaration.self))
    case FunctionBundleDeclaration.self:
      return name(of: castUnchecked(d, to: FunctionBundleDeclaration.self))
    case FunctionDeclaration.self:
      return name(of: castUnchecked(d, to: FunctionDeclaration.self))
    case GenericParameterDeclaration.self:
      return name(of: castUnchecked(d, to: GenericParameterDeclaration.self))
    case ParameterDeclaration.self:
      return name(of: castUnchecked(d, to: ParameterDeclaration.self))
    case StructDeclaration.self:
      return name(of: castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      return name(of: castUnchecked(d, to: TraitDeclaration.self))
    case TypeAliasDeclaration.self:
      return name(of: castUnchecked(d, to: TypeAliasDeclaration.self))
    case VariableDeclaration.self:
      return name(of: castUnchecked(d, to: VariableDeclaration.self))
    case VariantDeclaration.self:
      return name(of: castUnchecked(d, to: VariantDeclaration.self))
    default:
      return nil
    }
  }

  /// Returns the name of `d`.
  public func name<T: TypeDeclaration>(of d: T.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d`.
  public func name(of d: EnumCaseDeclaration.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d`.
  public func name(of d: FunctionBundleDeclaration.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d` or `nil` if `d` declares a lambda.
  public func name(of d: FunctionDeclaration.ID) -> Name? {
    switch self[d].identifier.value {
    case _ where self[d].introducer.value == .memberwiseinit:
      let s = parent(containing: d, as: StructDeclaration.self)!
      var labels: [String?] = []
      forEachStoredProperty(of: s, do: { (v, _) in labels.append(self[v].identifier.value) })
      return Name(identifier: "init", labels: .init(labels))

    case .simple(let x):
      let labels = self[d].parameters.map({ (p) in self[p].label?.value })
      if let (l, ls) = labels.headAndTail, l == "self" {
        return Name(identifier: x, labels: .init(ls))
      } else {
        return Name(identifier: x, labels: .init(labels))
      }

    case .operator(let n, let x):
      return Name(identifier: x, notation: n)

    case .lambda:
      return nil
    }
  }

  /// Returns the name of `d`.
  public func name(of d: GenericParameterDeclaration.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d`.
  public func name(of d: ParameterDeclaration.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d`.
  public func name(of d: VariableDeclaration.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d`.
  ///
  /// - Requires: The module containing `d` is scoped.
  public func name(of d: VariantDeclaration.ID) -> Name {
    let n = parent(containing: d).node.flatMap(castToDeclaration(_:)).flatMap(name(of:))!
    return .init(identifier: n.identifier, labels: n.labels, introducer: self[d].effect.value)
  }

  /// Returns the symbol associated with `n`, if any.
  ///
  /// A syntax tree has an associated symbol if it is annotated with `@_symbol(s)` in sources,
  /// where `s` is a string argument.
  public func symbol<T: SyntaxIdentity>(annotating n: T) -> String? {
    annotations(n).first(where: { (a) in a.identifier.value == "_symbol" })
      .flatMap({ (e) in e.arguments.uniqueElement })
      .flatMap({ (e) in e.value.string })
  }

  /// If `n` is a function or subscript call, returns its callee. Otherwise, returns `nil`.
  public func callee(_ n: ExpressionIdentity) -> ExpressionIdentity? {
    switch tag(of: n) {
    case Call.self:
      return self[castUnchecked(n, to: Call.self)].callee
    //case SubscriptCall.self:
    default:
      return nil
    }
  }

  /// Returns the left-most tree in the qualification of `e` iff `e` is a name or new expression.
  /// Otherwise, returns `nil`.
  public func rootQualification(of e: ExpressionIdentity) -> ExpressionIdentity? {
    var root: ExpressionIdentity

    if let n = cast(e, to: NameExpression.self) {
      guard let q = self[n].qualification else { return nil }
      root = q
    } else if let n = cast(e, to: New.self) {
      root = self[n].qualification
    } else {
      return nil
    }

    while true {
      if let x = cast(root, to: NameExpression.self) {
        if let y = self[x].qualification { root = y } else { return root }
      } else if let x = cast(root, to: Call.self) {
        root = self[x].callee
      } else {
        return root
      }
    }
  }

  /// If `b`, which is the body of a routine, contains exactly one return statement, return that
  /// statemenr. Otherwise, returns `nil`.
  public func singleReturn(of b: [StatementIdentity]) -> Return.ID? {
    b.uniqueElement.flatMap({ (s) in cast(s, to: Return.self) })
  }

  /// If `b` contains exactly one statement that is an expression, returns that expression.
  /// Otherwise, returns `nil`.
  public func singleExpression(of b: [StatementIdentity]) -> ExpressionIdentity? {
    b.uniqueElement.flatMap(castToExpression(_:))
  }

  /// If `b` contains exactly one statement that is an expression, returns that expression.
  /// Otherwise, returns `nil`.
  public func singleExpression(of b: Block.ID) -> ExpressionIdentity? {
    singleExpression(of: self[b].statements)
  }

  /// Returns `b` if it is an if-expression or `singleExpression(of: b)` if it is a block.
  public func singleExpression(of b: If.ElseIdentity) -> ExpressionIdentity? {
    if let e = cast(b, to: If.self) {
      return .init(e)
    } else if let s = cast(b, to: Block.self) {
      return singleExpression(of: s)
    } else {
      unexpected(b)
    }
  }

  // Returns the branches of `e` if both are single-expression bodied.
  public func branches(
    of e: If.ID
  ) -> (onSuccess: ExpressionIdentity, onFailure: ExpressionIdentity)? {
    guard
      let a = singleExpression(of: self[e].success),
      let b = singleExpression(of: self[e].failure)
    else { return nil }
    return (a, b)
  }

  /// Returns the adjunct conformances of `d`, if any.
  public func adjuncts(of d: DeclarationIdentity) -> [ConformanceDeclaration.ID]? {
    switch tag(of: d) {
    case StructDeclaration.self:
      return self[castUnchecked(d, to: StructDeclaration.self)].conformances
    case EnumDeclaration.self:
      return self[castUnchecked(d, to: EnumDeclaration.self)].conformances
    default:
      return nil
    }
  }

  /// Calls `action` for each stored property declaration in `d`.
  ///
  /// `action` accepts a variable declaration and an index path identifying its abstract position
  /// in a record value having the type declared by `d`.
  public func forEachStoredProperty(
    of d: StructDeclaration.ID,
    do action: (VariableDeclaration.ID, IndexPath) -> Void
  ) {
    for m in self[d].members {
      if let b = cast(m, to: BindingDeclaration.self) {
        forEachVariable(introducedBy: self[self[b].pattern].pattern, do: action)
      }
    }
  }

  /// Calls `action` for each variable declaration introduced by `d`.
  ///
  /// `action` accepts a variable declaration and an index path identifying its abstract position
  /// in the a record value having the type of `d`.
  public func forEachVariable(
    introducedBy d: BindingDeclaration.ID,
    do action: (VariableDeclaration.ID, IndexPath) -> Void
  ) {
    forEachVariable(introducedBy: self[self[d].pattern].pattern, do: action)
  }

  /// Calls `action` for each variable declaration introduced in `p`.
  ///
  /// `action` accepts a variable declaration and an index path identifying its abstract position
  /// in the a record value having the type of `p`.
  public func forEachVariable(
    introducedBy p: PatternIdentity,
    at path: IndexPath = [],
    do action: (VariableDeclaration.ID, IndexPath) -> Void
  ) {
    switch tag(of: p) {
    case BindingPattern.self:
      let q = castUnchecked(p, to: BindingPattern.self)
      forEachVariable(introducedBy: self[q].pattern, at: path, do: action)

    case TuplePattern.self:
      let q = castUnchecked(p, to: TuplePattern.self)
      for (i, e) in self[q].elements.enumerated() {
        forEachVariable(introducedBy: e, at: path.appending(i), do: action)
      }

    case VariableDeclaration.self:
      action(castUnchecked(p), path)

    default:
      assert(isExpression(p))
    }
  }

  /// Returns the declaration of the implicit symbol introduced by `d`.
  public func implicit(
    introducedBy d: BindingDeclaration.ID
  ) -> (introducer: BindingPattern.Introducer, declaration: VariableDeclaration.ID) {
    assert(self[d].isImplicit)
    let p = self[d].pattern
    let v = castUnchecked(self[p].pattern, to: VariableDeclaration.self)
    return (self[p].introducer.value, v)
  }

  /// Returns the declaration of the variant with effect `k` in the bundle `d`, or `nil` if `d`
  /// does not declare a bundle or `d` does not contain such a variant.
  public func variant(_ k: AccessEffect, of d: DeclarationIdentity) -> VariantDeclaration.ID? {
    if let b = cast(d, to: FunctionBundleDeclaration.self) {
      return self[b].variants.first(where: { (v) in self[v].effect.value == k })
    } else {
      return nil
    }
  }

  /// Returns the annotations applied to `n`.
  public func annotations<T: SyntaxIdentity>(_ n: T) -> [Annotation] {
    if let m = self[n] as? any Annotatable {
      return m.annotations
    } else {
      return []
    }
  }

  /// Returns the modifiers applied to `d`.
  public func modifiers(_ d: DeclarationIdentity) -> [Parsed<DeclarationModifier>] {
    if let m = self[d] as? any ModifiableDeclaration {
      return m.modifiers
    } else {
      return []
    }
  }

  /// Returns `true` iff `d` needs a user-defined a definition.
  ///
  /// A declaration requires a definition unless it is a trait requirement, an FFI, an external
  /// function, or a memberwise initializer.
  public func requiresDefinition(_ d: DeclarationIdentity) -> Bool {
    switch tag(of: d) {
    case FunctionDeclaration.self:
      let f = castUnchecked(d, to: FunctionDeclaration.self)
      return !isRequirement(f) && !isForeign(f) && !isExtern(f) && !self[f].isMemberwiseInitializer
    default:
      return !isRequirement(d)
    }
  }

  /// Reports that `n` was not expected in the current executation path and exits the program.
  public func unexpected<T: SyntaxIdentity>(
    _ n: T, file: StaticString = #file, line: UInt = #line
  ) -> Never {
    unreachable("unexpected node '\(tag(of: n))' at \(self[n].site)", file: file, line: line)
  }

  /// Reports that `t` was not expected in the current executation path and exits the program.
  public func unexpected(
    _ t: AnyTypeIdentity, file: StaticString = #file, line: UInt = #line
  ) -> Never {
    unreachable("unexpected type '\(show(t))'", file: file, line: line)
  }

  /// Returns a source span suitable to emit a disgnostic related to `n` as a whole.
  public func spanForDiagnostic<T: SyntaxIdentity>(about n: T) -> SourceSpan {
    switch tag(of: n) {
    case AssociatedTypeDeclaration.self:
      return self[castUnchecked(n, to: AssociatedTypeDeclaration.self)].identifier.site
    case BindingDeclaration.self:
      return self[self[castUnchecked(n, to: BindingDeclaration.self)].pattern].introducer.site
    case ConformanceDeclaration.self:
      return spanForDiagnostic(about: castUnchecked(n, to: ConformanceDeclaration.self))
    case ExtensionDeclaration.self:
      return self[castUnchecked(n, to: ExtensionDeclaration.self)].introducer.site
    case FunctionDeclaration.self:
      return self[castUnchecked(n, to: FunctionDeclaration.self)].identifier.site
    case If.self:
      return self[castUnchecked(n, to: If.self)].introducer.site
    case ImportDeclaration.self:
      return self[castUnchecked(n, to: ImportDeclaration.self)].identifier.site
    case ParameterDeclaration.self:
      return self[castUnchecked(n, to: ParameterDeclaration.self)].identifier.site
    case StructDeclaration.self:
      return self[castUnchecked(n, to: StructDeclaration.self)].identifier.site
    case TraitDeclaration.self:
      return self[castUnchecked(n, to: TraitDeclaration.self)].identifier.site
    case TypeAliasDeclaration.self:
      return self[castUnchecked(n, to: TypeAliasDeclaration.self)].identifier.site

    case PatternMatch.self:
      return self[castUnchecked(n, to: PatternMatch.self)].introducer.site
    case PatternMatchCase.self:
      return self[castUnchecked(n, to: PatternMatchCase.self)].introducer.site

    case Return.self:
      return spanForDiagnostic(about: castUnchecked(n, to: Return.self))

    default:
      return self[n].site
    }
  }

  /// Returns a source span suitable to emit a disgnostic related to `n` as a whole.
  public func spanForDiagnostic(about n: ConformanceDeclaration.ID) -> SourceSpan {
    if self[n].isAdjunct {
      return spanForDiagnostic(about: self[n].witness)
    } else {
      return self[n].introducer.site
    }
  }

  /// Returns a source span suitable to emit a disgnostic related to `n` as a whole.
  public func spanForDiagnostic(about n: Return.ID) -> SourceSpan {
    if let i = self[n].introducer {
      return .empty(at: i.site.start)
    } else if let e = self[n].value {
      return spanForDiagnostic(about: e)
    } else {
      return self[n].site
    }
  }

  /// Returns `message` with placeholders replaced by their corresponding values in `arguments`.
  ///
  /// Use this method to generate strings containing one or several elements whose description is
  /// computed by one of `show(_:)`'s overloads.
  ///
  /// ```swift
  /// let t = AnyTypeIdentity.void
  /// let s = program.format("'%T' is a type", [t])
  /// assert(s == "'Void' is a type")
  /// ```
  ///
  /// Each element to show is represented by a placehoder, which is a string starting with "%". The
  /// i-th placeholder occurring in `message` (except `%%`) must have a corresponding value at the
  /// i-th position of `arguments`.
  ///
  /// Valid placehoders are:
  /// - `%S`: The textual description of an arbitrary value.
  /// - `%T`: A type.
  /// - `%%`: The percent sign; does not consume any argument.
  public func format(
    _ message: String, _ arguments: [Any], file: StaticString = #file, line: UInt = #line
  ) -> String {
    var printer = TreePrinter(program: self)
    var output = ""
    var s = message[...]
    var a = arguments[...]
    while let head = s.popFirst() {
      if head == "%" {
        output.append(next(&s, &a))
      } else {
        output.append(head)
      }
    }
    return output

    /// Replaces the placeholder at the start of `prefix` with its corresponding representation,
    /// taking values from `arguments`.
    func next(_ prefix: inout Substring, _ arguments: inout ArraySlice<Any>) -> String {
      switch prefix.popFirst() {
      case "S":
        return String(describing: arguments.popFirst() ?? expected("item"))

      case "T" where prefix.removeFirst(if: "*"):
        let ts = (arguments.popFirst() as? [AnyTypeIdentity]) ?? expected("array of types")
        return "\(printer.show(ts))"

      case "T":
        return printer.show((arguments.popFirst() as? AnyTypeIdentity) ?? expected("type"))

      case "%":
        return "%"

      case let c:
        let s = c.map(String.init(_:)) ?? ""
        fatalError("invalid placeholder '%\(s)'", file: file, line: line)
      }
    }

    /// Reports that an argument of type `s` was expected and exits the program.
    func expected(_ s: String) -> Never {
      fatalError("expected \(s)", file: file, line: line)
    }
  }

}

extension Program {

  /// The value identifying an entity from the standard library.
  public enum StandardLibraryEntity: String, CaseIterable, Hashable, Sendable {

    /// `Hylo.Bool`.
    case bool = "Bool"

    /// `Hylo.Int`.
    case int = "Int"

    /// `Hylo.Int64`.
    case int64 = "Int64"

    /// `Hylo.Deinitializable`.
    case deinitializable = "Deinitializable"

    /// `Hyloe.Deinitializable.deinit`.
    case deinitializableDeinit = "Deinitializable.deinit(:)"

    /// `Hylo.Equatable`.
    case equatable = "Equatable"

    /// `Hylo.Movable`.
    case movable = "Movable"

    /// `Hylo.Movable.take_value(from:)`
    case movableTakeValue = "Movable.take_value(from:)"

    /// `Hylo.ExpressibleByIntegerLiteral`.
    case expressibleByIntegerLiteral = "ExpressibleByIntegerLiteral"

    /// `Hylo.ExpressibleByIntegerLiteral.init(integer_literal:)`.
    case expressibleByIntegerLiteralInit = "ExpressibleByIntegerLiteral.init(integer_literal:)"

  }

  /// Returns the type of a term witnessing that `t` conforms to the core trait `p`.
  ///
  /// The module containing the standard library must have been loaded and type checked.
  public mutating func typeOfWitness(
    of t: AnyTypeIdentity, is p: StandardLibraryEntity
  ) -> AnyTypeIdentity {
    let f = types.cast(standardLibraryType(p), to: UniversalType.self)!
    return types.application(of: f, to: [t])
  }

  /// Returns the type of the given standard library entity.
  ///
  /// The module containing the standard library must have been loaded and type checked.
  public func standardLibraryType(_ n: StandardLibraryEntity) -> AnyTypeIdentity {
    let d = standardLibraryDeclaration(n)
    let t = type(assignedTo: d, assuming: Metatype.self)
    return types[t].inhabitant
  }

  /// Returns the declaration of the given standard library entity.
  ///
  /// The source files of the standard library must have been loaded but the module many not
  /// necessarily be type checked already.
  public func standardLibraryDeclaration(
    _ n: StandardLibraryEntity
  ) -> DeclarationIdentity {
    standardLibraryDeclarations[n] ?? fatalError("missing or corrupt standard library")
  }

  /// Returns the declaration of the given standard library assuming it is represented by `T`.
  ///
  /// The source files of the standard library must have been loaded but the module many not
  /// necessarily be type checked already.
  public func standardLibraryDeclaration<T: Declaration>(
    _ n: StandardLibraryEntity, as: T.Type
  ) -> T.ID {
    castUnchecked(standardLibraryDeclaration(n), to: T.self)
  }

  /// Fills `program.standardLibraryDeclarations`.
  ///
  /// This method must be called before type checking the standard library.
  internal mutating func initializeStandardLibraryCaches() {
    for n in Program.StandardLibraryEntity.allCases {
      guard
        let a = identity(module: .standardLibrary),
        let b = select(from: a, .symbol(n.rawValue)).uniqueElement,
        let d = castToDeclaration(b)
      else { fatalError("missing or corrupt standard library") }
      standardLibraryDeclarations[n] = d
    }
  }

}

extension Program {

  /// The type of a table mapping module names to their identity in a program.
  internal typealias ModuleIdentityMap = [Module.Name: Module.ID]

  /// Serializes `m` to `archive`.
  public func write<A>(module m: Module.ID, to archive: inout WriteableArchive<A>) throws {
    // Configure the serialization context.
    let c = Module.SerializationContext(
      identities: .init(uniqueKeysWithValues: modules.values.map({ (m) in (m.name, m.identity) })),
      types: types)

    // Serialize the module.
    var ctx: Any = c
    try self[m].write(to: &archive, in: &ctx)
  }

  /// Serializes `m`.
  public func archive(module m: Module.ID) throws -> BinaryBuffer {
    var w = WriteableArchive(BinaryBuffer())
    try write(module: m, to: &w)
    return w.finalize()
  }

  /// Loads the module named `moduleName` from `archive`.
  ///
  /// - Note: `self` is not modified if an exception is thrown.
  /// - Requires: `moduleName` is the name of the module stored in `archive`.
  @discardableResult
  public mutating func load<A>(
    module moduleName: Module.Name, from archive: inout ReadableArchive<A>
  ) throws -> (loaded: Bool, identity: Module.ID) {
    // Nothing to do if the module is already loaded.
    if let m = identity(module: moduleName) { return (false, m) }

    // Reserve an identity for the new module.
    let m = modules.count
    var c = Module.SerializationContext(identities: [moduleName: m], types: .init())

    // Configure the serialization context.
    swap(&c.types, &types)
    defer { swap(&c.types, &types) }
    for n in modules.values {
      c.identities[n.name] = n.identity
    }

    // Deserialize the module.
    let instance = try c.withWrapped({ (ctx) in try archive.read(Module.self, in: &ctx) })
    precondition(moduleName == instance.name)
    modules[moduleName] = instance

    // Initialize the standard library cache if necessary.
    if moduleName == .standardLibrary {
      initializeStandardLibraryCaches()
    }

    return (true, m)
  }

  /// Loads the module named `moduleName`, reading its contents from `archive`.
  ///
  /// - Note: `self` is not modified if an exception is thrown.
  /// - Requires: `moduleName` is the name of the module stored in `archive`.
  @discardableResult
  public mutating func load(
    module moduleName: Module.Name, from archive: BinaryBuffer
  ) throws -> (loaded: Bool, identity: Module.ID) {
    var r = ReadableArchive(archive)
    return try load(module: moduleName, from: &r)
  }

}

extension Program {

  public func select(_ filter: SyntaxFilter) -> some Collection<AnySyntaxIdentity> {
    moduleIdentities.map({ (m) in select(from: m, filter) }).joined()
  }

  public func select(
    from m: Module.ID, _ filter: SyntaxFilter
  ) -> some Collection<AnySyntaxIdentity> {
    modules.values[m].syntax.filter({ (n) in filter(n, in: self) })
  }

}

/// A selector identifying nodes in a syntax tree.
public indirect enum SyntaxFilter {

  /// Matches any node.
  case all

  /// Matches any node satisfying both filters.
  case and(SyntaxFilter, SyntaxFilter)

  /// Matches any node declaring a single entity with the given name.
  case name(Name)

  /// Matches any node annotated with the given symbol.
  case symbol(String)

  /// Matches any node with the given tag.
  case tag(any Syntax.Type)

  /// Matches any node satisfying the given predicate.
  case satisfies((AnySyntaxIdentity) -> Bool)

  /// Returns `true` if the node `n` of program `p` satisfies `self`.
  public func callAsFunction(_ n: AnySyntaxIdentity, in p: Program) -> Bool {
    switch self {
    case .all:
      return true
    case .and(let l, let r):
      return l(n, in: p) && r(n, in: p)
    case .name(let x):
      return p.castToDeclaration(n).map({ (d) in p.name(of: d) == x }) ?? false
    case .symbol(let x):
      return p.symbol(annotating: n) == x
    case .tag(let k):
      return p.tag(of: n) == k
    case .satisfies(let p):
      return p(n)
    }
  }

}

/// A syntax visitor that enumerates the immediate children of a node.
fileprivate struct ChildrenEnumerator: SyntaxVisitor {

  /// The node whose children are being enumerated.
  fileprivate var parent: AnySyntaxIdentity

  /// The children collected by the calls to `willEnter(_:in:)`.
  fileprivate var children: [AnySyntaxIdentity] = []

  fileprivate mutating func willEnter(_ n: AnySyntaxIdentity, in program: Program) -> Bool {
    if n != parent { children.append(n) }
    return n == parent
  }

}
