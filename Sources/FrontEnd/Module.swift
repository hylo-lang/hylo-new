import Archivist
import OrderedCollections
import Utilities

/// A collection of declarations in one or more source files.
public struct Module: Sendable {

  /// The identity of a module loaded in a program.
  public typealias ID = Int

  /// The name of a module.
  @Archivable
  public struct Name: Hashable, Sendable, CustomStringConvertible {

    /// The raw value of this name.
    public let rawValue: String

    /// Creates an instance with the given raw value.
    public init(_ rawValue: String) {
      self.rawValue = rawValue
    }

    /// A textual description of this name.
    public var description: String {
      rawValue
    }

    /// Returns `true` iff `self` lexicographicaly precedes `other`.
    public func lexicographicallyPrecedes(_ other: Self) -> Bool {
      rawValue.lexicographicallyPrecedes(other.rawValue)
    }

    /// The name of Hylo's standard library.
    public static let standardLibrary = Name("hylo.Hylo")

  }

  /// A source file added to a module.
  public struct SourceContainer: Sendable {

    /// The position of `self` in the containing module.
    internal let identity: SourceFile.ID

    /// The source file contained in `self`.
    internal let source: SourceFile

    /// The abstract syntax of `source`'s contents.
    internal var syntax: [AnySyntax] = []

    /// A table from syntax tree to its tag.
    internal var syntaxToTag: [SyntaxTag] = []

    /// The root of the syntax trees in `self`, which may be subset of the top-level declarations.
    internal var roots: [DeclarationIdentity] = []

    /// The top-level declarations in `self`.
    public internal(set) var topLevelDeclarations: [DeclarationIdentity] = []

    /// A table from syntax tree to the scope that contains it.
    ///
    /// The keys and values of the table are the offsets of the syntax trees in the source file
    /// (i.e., syntax identities sans module or source offset). Top-level declarations are mapped
    /// onto `-1`.
    internal var syntaxToParent: [Int] = []

    /// A table from scope to the declarations that it contains directly.
    internal var scopeToDeclarations: [Int: [DeclarationIdentity]] = [:]

    /// A table from variable declaration to its containing binding declaration, if any.
    internal var variableToBinding: [Int: BindingDeclaration.ID] = [:]

    /// A table from syntax tree to its type.
    internal var syntaxToType: [Int: AnyTypeIdentity] = [:]

    /// A table from name to its declaration.
    internal var nameToDeclaration: [Int: DeclarationReference] = [:]

    /// The diagnostics accumulated during compilation.
    public internal(set) var diagnostics = DiagnosticSet()

    /// Projects the node identified by `n`.
    internal subscript<T: SyntaxIdentity>(n: T) -> any Syntax {
      _read {
        assert(n.file == identity)
        yield syntax[n.offset].wrapped
      }
    }

    /// Returns the tag of `n`.
    internal func tag<T: SyntaxIdentity>(of n: T) -> SyntaxTag {
      assert(n.file == identity)
      return syntaxToTag[n.offset]
    }

    /// Inserts `child` into `self`.
    internal mutating func insert<T: Syntax>(_ child: T) -> T.ID {
      let d = syntax.count
      syntax.append(.init(child))
      syntaxToTag.append(.init(T.self))
      syntaxToParent.append(-1)
      return T.ID(uncheckedFrom: .init(file: identity, offset: d))
    }

    /// Replaces the node identified by `n` by `newTree`.
    ///
    /// - Requires: If `n` identifies a scope, then `T` must conform to `Scope`.
    internal mutating func replace<T: Expression>(
      _ n: ExpressionIdentity, for newTree: T
    ) -> T.ID {
      assert(n.file == identity)
      syntax[n.offset] = .init(newTree)
      syntaxToTag[n.offset] = .init(T.self)
      return .init(uncheckedFrom: n.erased)
    }

    /// Replaces the node identified by `n` by `newTree`.
    ///
    /// - Requires: If `n` identifies a scope, then `T` must conform to `Scope`.
    internal mutating func replace<T: Expression>(
      _ n: WildcardLiteral.ID, for newTree: T
    ) -> T.ID {
      assert(n.file == identity)
      syntax[n.offset] = .init(newTree)
      syntaxToTag[n.offset] = .init(T.self)
      return .init(uncheckedFrom: n.erased)
    }

    /// Inserts a copy of `n` into `self`.
    fileprivate mutating func clone(_ n: ExpressionIdentity) -> ExpressionIdentity {
      assert(n.file == identity)
      let d = syntax.count
      syntax.append(syntax[n.offset])
      syntaxToTag.append(syntaxToTag[n.offset])
      syntaxToParent.append(syntaxToParent[n.offset])
      scopeToDeclarations[d] = scopeToDeclarations[n.offset]
      syntaxToType[d] = syntaxToType[n.offset]
      nameToDeclaration[d] = nameToDeclaration[n.offset]
      return .init(uncheckedFrom: .init(file: identity, offset: d))
    }

    /// Adds a diagnostic to this file.
    ///
    /// - requires: The diagnostic is anchored at a position in `self`.
    internal mutating func addDiagnostic(_ d: Diagnostic) {
      assert(d.site.source.name == source.name)
      diagnostics.insert(d)
    }

  }

  /// The name of the module.
  public let name: Name

  /// The position of `self` in the containing program.
  public let identity: Module.ID

  /// The dependencies of the module.
  public private(set) var dependencies: [Module.Name] = []

  /// The source files in the module.
  public private(set) var sources = OrderedDictionary<FileName, SourceContainer>()

  /// The IR functions in the module.
  internal private(set) var ir = OrderedDictionary<IRFunction.Name, IRFunction>()

  /// Creates an empty module with the given name and identity.
  public init(name: Name, identity: Module.ID) {
    self.name = name
    self.identity = identity
  }

  /// `true` iff `self` is Hylo's standard library.
  public var isStandardLibrary: Bool {
    name == .standardLibrary
  }

  /// Returns a hash of the module that suitable for determining whether its sources have changed.
  public var fingerprint: UInt64 {
    SourceFile.fingerprint(contentsOf: sources.values.lazy.map(\.source))
  }

  /// `true` if the module has errors.
  public var containsError: Bool {
    sources.values.contains(where: \.diagnostics.containsError)
  }

  /// The diagnostics accumulated during compilation.
  public var diagnostics: some Collection<Diagnostic> {
    sources.values.map(\.diagnostics.elements).joined()
  }

  /// Adds a diagnostic to this module.
  ///
  /// - requires: The diagnostic relates to a source in `self`.
  public mutating func addDiagnostic(_ d: Diagnostic) {
    sources[d.site.source.name]!.addDiagnostic(d)
  }

  /// Adds a dependency to this module.
  public mutating func addDependency(_ d: Module.Name) {
    if !dependencies.contains(d) {
      dependencies.append(d)
    }
  }

  /// Adds a source file to this module.
  @discardableResult
  public mutating func addSource(_ s: SourceFile) -> (inserted: Bool, identity: SourceFile.ID) {
    if let f = sources.index(forKey: s.name) {
      return (inserted: false, identity: .init(module: identity, offset: f))
    } else {
      let p = Parser(s)
      var f = Module.SourceContainer(
        identity: .init(module: identity, offset: sources.count), source: s)
      p.parseTopLevelDeclarations(in: &f)
      sources[s.name] = f
      return (inserted: true, identity: f.identity)
    }
  }

  /// Adds `f` to this module.
  ///
  /// - Requires: `self` contains no IR function having the name of `f`.
  @discardableResult
  public mutating func addFunction(_ f: IRFunction) -> IRFunction.ID {
    modify(&ir[f.name]) { (d) in
      assert(d == nil, "function already declared")
      d = f
    }
    return ir.index(forKey: f.name)!
  }

  /// Inserts `child` into `self` in the bucket of `file`.
  public mutating func insert<T: Syntax>(_ child: T, in file: SourceFile.ID) -> T.ID {
    sources.values[file.offset].insert(child)
  }

  /// Inserts `child` into `self` in the scope of `parent`.
  public mutating func insert<T: Expression>(_ child: T, in parent: ScopeIdentity) -> T.ID {
    let i = insert(child, in: parent.file)
    if let p = parent.node {
      sources.values[parent.file.offset].syntaxToParent[i.offset] = p.offset
    }
    return i
  }

  /// Inserts a copy of `n` into `self`.
  ///
  /// The result of this method is a "shallow" copy of `n`, meaning that none of its children are
  /// copied. Hence, if `n` identifies a scope, the innermost parent of its immediate children is
  /// still `n` after this method returns. Use `Program.reassignScopes(childrenOf:)` to modify the
  /// parent of a cloned scope's children.
  public mutating func clone(_ n: ExpressionIdentity) -> ExpressionIdentity {
    sources.values[n.file.offset].clone(n)
  }

  /// Replaces the node identified by `n` by `newTree`.
  ///
  /// The result of `tag(of: n)` denotes `T` after this method returns. No other property of `n`
  /// is changed. The children of the node currently identified by `n` that are not children of
  /// `newTree` are notionally removed from the tree after this method returns.
  ///
  /// - Requires: If `n` identifies a scope, then `T` must conform to `Scope`.
  @discardableResult
  public mutating func replace<T: Expression>(_ n: ExpressionIdentity, for newTree: T) -> T.ID {
    assert(!(tag(of: n).value is any Scope.Type) || (T.self is any Scope))
    return sources.values[n.file.offset].replace(n, for: newTree)
  }

  /// The nodes in `self`'s abstract syntax tree.
  public var syntax: some Collection<AnySyntaxIdentity> {
    let all = sources.values.enumerated().map { (f, s) in
      s.syntax.indices.lazy.map { (n) in
        AnySyntaxIdentity(file: .init(module: identity, offset: f), offset: n)
      }
    }
    return all.joined()
  }

  /// The identities of the source files in `self`.
  public var sourceFileIdentities: [SourceFile.ID] {
    (0 ..< sources.count).map({ (s) in SourceFile.ID(module: identity, offset: s) })
  }

  /// The top-level declarations in `self`.
  public var topLevelDeclarations: some Collection<DeclarationIdentity> {
    sources.values.map(\.topLevelDeclarations).joined()
  }

  /// Projects the source file identified by `f`.
  internal subscript(f: SourceFile.ID) -> SourceContainer {
    _read {
      assert(f.module == identity)
      yield sources.values[f.offset]
    }
    _modify {
      assert(f.module == identity)
      yield &sources.values[f.offset]
    }
  }

  /// Projects the node identified by `n`.
  internal subscript<T: SyntaxIdentity>(n: T) -> any Syntax {
    assert(n.module == identity)
    return sources.values[n.file.offset].syntax[n.offset].wrapped
  }

  /// Projects the node identified by `n`.
  internal subscript<T: Syntax>(n: T.ID) -> T {
    assert(n.module == identity)
    return sources.values[n.file.offset].syntax[n.offset].wrapped as! T
  }

  /// Projects the function identified by `f`.
  internal subscript(f: IRFunction.ID) -> IRFunction {
    get { ir.values[f] }
    _modify { yield &ir.values[f] }
  }

  /// Returns the tag of `n`.
  internal func tag<T: SyntaxIdentity>(of n: T) -> SyntaxTag {
    assert(n.module == identity)
    return self[n.file].syntaxToTag[n.offset]
  }

  /// Assigns a type to `n`.
  internal mutating func setType<T: SyntaxIdentity>(_ t: AnyTypeIdentity, for n: T) {
    assert(n.module == identity)
    assert(!t[.hasVariable])
    let u = sources.values[n.file.offset].syntaxToType[n.offset].wrapIfEmpty(t)
    assert(t == u, "inconsistent property assignment")
  }

  /// Assigns a type to `n`, overriding any prior assignment.
  internal mutating func updateType<T: SyntaxIdentity>(_ t: AnyTypeIdentity, for n: T) {
    assert(n.module == identity)
    assert(!t[.hasVariable])
    sources.values[n.file.offset].syntaxToType[n.offset] = t
  }

  /// Sets the declaration to which `n` refers.
  internal mutating func bind(_ n: NameExpression.ID, to r: DeclarationReference) {
    assert(n.module == identity)
    assert(!r.hasVariable)
    let s = sources.values[n.file.offset].nameToDeclaration[n.offset].wrapIfEmpty(r)
    assert(r == s, "inconsistent property assignment")
  }

  /// Returns the type assigned to `n`, if any.
  internal func type<T: SyntaxIdentity>(assignedTo n: T) -> AnyTypeIdentity? {
    assert(n.module == identity)
    return sources.values[n.file.offset].syntaxToType[n.offset]
  }

  /// Returns the declaration referred to by `n`, if any.
  internal func declaration(referredToBy n: NameExpression.ID) -> DeclarationReference? {
    assert(n.module == identity)
    return sources.values[n.file.offset].nameToDeclaration[n.offset]
  }

}

extension Module: Archivable {

  /// A constant written at the beginning of an archive ("hylo" in hex).
  private static let serializationMagicNumber: UInt32 = 0x68796c6f

  /// The version of a serialization scheme.
  private struct SerializationVersion: Archivable {

    /// The raw value of this version.
    private let rawValue: UInt32

    /// Creates an instance with the given properties.
    private init(compatibility: UInt16, revision: UInt16) {
      self.rawValue = UInt32(compatibility) << 16 | UInt32(revision)
    }

    /// Reads an instance of `self` from `archive`.
    internal init<A>(from archive: inout ReadableArchive<A>, in _: inout Any) throws {
      self.rawValue = try archive.read(UInt32.self, endianness: .little)
    }

    /// Serializes `self` to `archive`.
    internal func write<A>(to archive: inout WriteableArchive<A>, in _: inout Any) throws {
      archive.write(rawValue, endianness: .little)
    }

    /// Returns `true` iff `self` is compatible with an archive compiled with `other`.
    internal func compatible(with other: Self) -> Bool {
      (self.rawValue >> 16) == (other.rawValue >> 16)
    }

    /// The current version of the serialization scheme.
    internal static let current = SerializationVersion(compatibility: 1, revision: 1)

  }

  /// The context of the serialization/deserialization of a module.
  internal struct SerializationContext {

    /// A mapping from module names to their identity in the program.
    internal var identities: Program.ModuleIdentityMap

    /// The types in the program.
    internal var types: TypeStore

    /// A mapping from archived module identity to its new value.
    internal var modules = OrderedDictionary<Module.ID, Module.ID>()

    /// A mapping from file name to its contents.
    internal var sources = OrderedDictionary<FileName, SourceFile>()

    /// Returns the result of calling `action` on `self` wrapped in `Any`.
    internal mutating func withWrapped<T>(_ action: (inout Any) throws -> T) rethrows -> T {
      try withUnsafeMutablePointer(to: &self) { (this) in
        var w = this.move() as Any
        defer { this.initialize(to: w as! Self) }
        return try action(&w)
      }
    }

  }

  /// Reads an instance of `self` from `archive`.
  ///
  /// This method is meant to be called by `Program.load(module:from:)`, which passes `context` as
  /// an instance of `SerializationContext` that associates a module name to its identity in the
  /// program and contains a store with the types of the program.
  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    // Magic number and version.
    guard
      try archive.read(UInt32.self, endianness: .little) == Module.serializationMagicNumber,
      try archive.read(SerializationVersion.self).compatible(with: .current)
    else { throw ArchiveError.invalidInput }

    // <fingerprint> <module name>
    let name = try archive.read(Name.self)
    let hash = try archive.read(UInt64.self, endianness: .little)

    self = try modify(&context, as: SerializationContext.self) { (ctx) in
      ctx.modules[0] = ctx.identities[name]!

      // <dependency count> <dependency name> ...
      let dependencyCount = try archive.readUnsignedLEB128()
      var dependencies: [Module.Name] = []
      for i in 0 ..< dependencyCount {
        let d = try ctx.withWrapped({ (c) in try archive.read(Name.self, in: &c) })
        dependencies.append(d)
        ctx.modules[Module.ID(i + 1)] = ctx.identities[d]
      }

      var me = Self(name: name, identity: ctx.identities[name]!)

      // <source count> <identity> <contents> ...
      let count = try Int(archive.readUnsignedLEB128())
      for _ in 0 ..< count {
        let i = try archive.read(rawValueOf: SourceFile.ID.self)!
        let s = try archive.read(SourceFile.self)
        ctx.sources[s.name] = s
        me.sources[s.name] = .init(identity: i, source: s)
      }
      return me
    }

    for i in 0 ..< self.sources.count {
      try modify(&self.sources.values[i]) { (s) in
        // Syntax trees.
        let syntaxCount = try archive.readUnsignedLEB128()
        for _ in 0 ..< syntaxCount {
          let n = try archive.read(AnySyntax.self, in: &context)
          s.syntax.append(n)
          s.syntaxToTag.append(.init(Swift.type(of: n.wrapped)))
        }

        // Semantic properties.
        s.roots = try archive.read([DeclarationIdentity].self, in: &context)
        s.topLevelDeclarations = try archive.read([DeclarationIdentity].self, in: &context)
        s.syntaxToParent = try archive.read([Int].self, in: &context)
        s.scopeToDeclarations = try archive.read([Int: [DeclarationIdentity]].self, in: &context)
        s.variableToBinding = try archive.read([Int: BindingDeclaration.ID].self, in: &context)
        s.syntaxToType = try archive.read([Int: AnyTypeIdentity].self, in: &context)
        s.nameToDeclaration = try archive.read([Int: DeclarationReference].self, in: &context)
      }
    }

    assert(hash == fingerprint, "module fingerprint does not match")
  }

  /// Serializes `self` to `archive`.
  ///
  /// This method is meant to be called by `Program.write(module:to:)`, which passes `context` as
  /// an instance of `ModuleIdentityMap` that associates a module name to its identity in the
  /// program and contains a store with the types of the program.
  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    var unwrappedContext = context as? SerializationContext ?? fatalError("bad context")

    // Magic number and version.
    archive.write(Module.serializationMagicNumber, endianness: .little)
    try archive.write(Module.SerializationVersion.current)

    // <module name> <fingerprint>
    try archive.write(name)
    archive.write(fingerprint, endianness: .little)
    unwrappedContext.modules[identity] = 0
    unwrappedContext.sources = .init(uniqueKeysWithValues: sources.mapValues(\.source))

    // <dependency count> <dependency name> ...
    archive.write(unsignedLEB128: dependencies.count)
    for d in dependencies {
      try archive.write(d, in: &context)
      unwrappedContext.modules[unwrappedContext.identities[d]!] = unwrappedContext.modules.count
    }

    // <source count> <identity> <contents> ...
    archive.write(unsignedLEB128: sources.count)
    for s in sources.values {
      try archive.write(rawValueOf: s.identity, in: &context)
      try archive.write(s.source, in: &context)
    }

    // The remainder of the module is serialized in a new context.
    try unwrappedContext.withWrapped { (ctx) in
      for s in sources.values {
        // Syntax trees.
        archive.write(unsignedLEB128: s.syntax.count)
        for n in s.syntax {
          try archive.write(n, in: &ctx)
        }

        // Semantic properties.
        try archive.write(s.roots, in: &ctx)
        try archive.write(s.topLevelDeclarations, in: &ctx)
        try archive.write(s.syntaxToParent, in: &ctx)
        try archive.write(s.scopeToDeclarations, in: &ctx, sortedBy: \.key)
        try archive.write(s.variableToBinding, in: &ctx, sortedBy: \.key)
        try archive.write(s.syntaxToType, in: &ctx, sortedBy: \.key)
        try archive.write(s.nameToDeclaration, in: &ctx, sortedBy: \.key)
      }
    }
  }

  /// Returns the name and fingerprint of the module stored in `archive`.
  public static func header<A>(
    _ archive: inout ReadableArchive<A>
  ) throws -> (Module.Name, UInt64) {
    // Magic number and version.
    guard
      try archive.read(UInt32.self, endianness: .little) == Module.serializationMagicNumber,
      try archive.read(SerializationVersion.self).compatible(with: .current)
    else { throw ArchiveError.invalidInput }

    // <module name> <fingerprint>
    let name = try archive.read(Name.self)
    let hash = try archive.read(UInt64.self, endianness: .little)
    return (name, hash)
  }

}
