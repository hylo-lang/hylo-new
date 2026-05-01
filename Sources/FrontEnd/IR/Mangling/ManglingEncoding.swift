import Utilities

/// Hylo's mangling algorithm.
struct ManglingEncoding: Sendable {

  // Mangling conventions:
  //
  // We mangle three kinds of symbols:
  // - entities (declarations, translation units, modules, scopes)
  // - types
  // - witness tables (`IRWitnessTable`)
  //
  // For entities, we encode the full qualification first, from outermost to innermost.
  //
  // We memoize encoded entities. If we first encode `M0.TU.A.B.C` and later need `M0.TU.A.D`,
  // we emit a lookup token for the shared `M0.TU.A` prefix. While encoding entities that are not
  // finished yet, we can emit a relative-lookup token to refer to the innermost open entity.
  // In the example above, generic parameters can refer to `M0.TU.A.D` while `M0.TU.A.D` is still
  // being encoded.
  //
  // We also memoize strings. Repeated strings are encoded with a string-lookup token.
  // Some common symbols are reserved and encoded with dedicated reserved tokens.

  /// The program defining the symbols being mangled.
  private let program: Program

  /// Creates an instance mangling symbols defined in `program`.
  init(_ program: Program) {
    self.program = program
  }

  /// Writes to `output` the mangled representation of `s`.
  mutating func mangled(type s: AnyTypeIdentity, to output: inout ManglingContext) {
    append(type: s, to: &output)
  }

  /// Writes to `output` the mangled representation of `s`.
  mutating func mangled(decl s: DeclarationIdentity, to output: inout ManglingContext) {
    append(decl: s, to: &output)
  }

  /// Writes to `output` the mangled representation of `s` from module `m`.
  mutating func mangled(
    function s: IRFunction.ID, of m: Module.ID, to output: inout ManglingContext
  ) {
    append(function: s, of: m, to: &output)
  }

  /// Writes to `output` the mangled representation of `s`.
  mutating func mangled(table s: IRWitnessTable, to output: inout ManglingContext) {
    append(table: s, to: &output)
  }

  /// Returns the demangled symbol from `source`.
  ///
  /// An error is returned if `source` is not fully consumed when this function returns.
  static func demangle(from source: inout DemanglingContext) -> DemangledSymbol {
    guard let o = source.peekOperator() else { return .error(nil, remaining: source.remaining) }
    let r: DemangledSymbol
    if o.isEntityOperator {
      r = .entity(takeEntity(from: &source))
    } else if o.isTypeOperator {
      r = .type(takeType(from: &source))
    } else {
      if source.takeOperator() == .witnessTable {
        r = takeWitnessTable(from: &source)
      } else {
        return .error(nil, remaining: source.remaining)
      }
    }
    return source.isComplete ? r : .error(r, remaining: source.remaining)
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(decl d: DeclarationIdentity, to output: inout ManglingContext) {
    if output.addIf(reservedOrRecorded: .node(.init(d)), in: program) { return }

    // First add the qualification of the declaration.
    appendQualification(of: d, to: &output)
    // If this is a scope, then just add it as a scope and finish.
    if let s = program.castToScope(d) {
      append(scope: s, to: &output)
      return
    }

    // Handle declarations that are not scopes.
    switch program.tag(of: d) {
    case AssociatedTypeDeclaration.self:
      append(unqualified: AssociatedTypeDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    case BindingDeclaration.self:
      append(unqualified: BindingDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    case EnumCaseDeclaration.self:
      append(unqualified: EnumCaseDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    case ImportDeclaration.self:
      append(unqualified: ImportDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    case GenericParameterDeclaration.self:
      append(unqualified: GenericParameterDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    case ParameterDeclaration.self:
      append(unqualified: ParameterDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    case VariableDeclaration.self:
      append(unqualified: VariableDeclaration.ID(uncheckedFrom: d.erased), to: &output)
    default:
      program.unexpected(d)
    }

    output.record(symbol: .node(AnySyntaxIdentity(d)), in: program)
  }

  /// Demangles a (possibly qualified) entity from `source`.
  static private func takeEntity(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    var qualifiedEntity: DemangledEntity? = nil

    while let o = source.takeOperator() {
      let demangled: DemangledEntity

      switch o {
      case .lookup:
        demangled = entityOrError(source.takeLookupReference())
      case .lookupRelative:
        demangled = .relative
      case .reserved:
        demangled = entityOrError(source.takeReserved())
      case .associatedTypeDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .enumCaseDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .enumDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .bindingDeclaration:
        demangled = takeBindingDeclaration(from: &source)
      case .conformanceDeclaration:
        demangled = takeConformanceDeclaration(from: &source)
      case .extensionDeclaration:
        demangled = takeExtensionDeclaration(from: &source)
      case .functionDeclaration:
        demangled = takeFunctionDeclaration(from: &source)
      case .staticFunctionDeclaration:
        demangled = takeStaticFunctionDeclaration(from: &source)
      case .functionBundleDeclaration:
        demangled = takeFunctionBundleDeclaration(from: &source)
      case .initializerDeclaration:
        demangled = takeInitializerDeclaration(from: &source)
      case .synthesizedFunctionDeclaration:
        demangled = takeSynthesizedFunctionDeclaration(from: &source)
      case .implementationDeclaration:
        demangled = takeImplementationDeclaration(from: &source)
      case .existentializedDeclaration:
        demangled = takeExistentializedDeclaration(from: &source)
      case .genericParameterDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .importDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .parameterDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .structDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .typeAliasDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .traitDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .variableDeclaration:
        demangled = takeUnqualifiedEntity(from: &source)
      case .variantDeclaration:
        demangled = takeVariantDeclaration(from: &source)
      case .anonymousScope:
        demangled = takeAnonymousScope(from: &source)
      case .module:
        demangled = takeModule(from: &source)
      case .sourceFile:
        demangled = takeSourceFile(from: &source)
      case .virtualSourceFile:
        demangled = takeVirtualSourceFile(from: &source)
      default:
        demangled = .error
        break
      }

      if qualifiedEntity != nil {
        qualifiedEntity = .qualified(head: demangled, previous: qualifiedEntity!)
      } else {
        qualifiedEntity = demangled
      }

      // Record that we've seen `demangled`.
      if o != .lookup && o != .lookupRelative && o != .reserved {
        source.record(symbol: .entity(qualifiedEntity!))
      }

      // Stop if we've encountered an error or reached the end.
      if demangled == .error || source.isComplete {
        break
      }

      // Stop if we cannot continue, or if we need to continue with something that cannot be a
      // scope or a declaration. Also consider the case that we start another declaration.
      guard let n = source.peekOperator() else { break }
      if n == .reserved || n == .module || n == .lookupRelative || !n.isEntityOperator {
        break
      }
    }

    return qualifiedEntity ?? .error
  }

  /// Writes the mangled qualification of `n` to `output`.
  private mutating func appendQualification<T: SyntaxIdentity>(
    of n: T, to output: inout ManglingContext
  ) {
    // Find the prefix of the qualification that should be mangled as a reference.
    var qs: [ScopeIdentity] = []
    var earlyExit = false
    let p = program.parent(containing: n)
    for s in program.scopes(from: p) {
      if s.node != nil, output.addIf(reservedOrRecorded: .node(s.node!), in: program) {
        earlyExit = true
        break
      } else if output.addIf(reservedOrRecorded: s.asSymbol, in: program) {
        earlyExit = true
        break
      } else if output.addIf(qualification: s) {
        precondition(qs.isEmpty)
        return
      } else {
        qs.append(s)
      }
    }

    // Write the mangled representation of the qualification's suffix.
    if !earlyExit {
      append(module: p.module, to: &output)
      output.record(symbol: .module(p.module), in: program)
    }
    for s in qs.reversed() {
      append(scope: s, to: &output)
      output.record(symbol: s.asSymbol, in: program)
    }
  }

  /// Writes the mangled representation of `d` sans qualification to `output`.
  private mutating func append<T: Declaration>(
    unqualified d: T.ID, to output: inout ManglingContext
  ) {
    switch SyntaxTag(T.self) {
    case AssociatedTypeDeclaration.self:
      output.add(operator: .associatedTypeDeclaration)
    case EnumCaseDeclaration.self:
      output.add(operator: .enumCaseDeclaration)
    case EnumDeclaration.self:
      output.add(operator: .enumDeclaration)
    case GenericParameterDeclaration.self:
      output.add(operator: .genericParameterDeclaration)
    case ImportDeclaration.self:
      output.add(operator: .importDeclaration)
    case ParameterDeclaration.self:
      output.add(operator: .parameterDeclaration)
    case StructDeclaration.self:
      output.add(operator: .structDeclaration)
    case TraitDeclaration.self:
      output.add(operator: .traitDeclaration)
    case TypeAliasDeclaration.self:
      output.add(operator: .typeAliasDeclaration)
    case VariableDeclaration.self:
      output.add(operator: .variableDeclaration)
    default:
      unreachable()
    }
    output.add(string: program.name(of: DeclarationIdentity(d))!.identifier)
  }

  /// Demangles an unqualified entity declaration from `source`.
  private static func takeUnqualifiedEntity(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    source.takeString().map({ (s) in .scope(s) }) ?? .error
  }

  /// Writes the mangled representation of `d` sans qualification to `output`.
  private mutating func append(
    unqualified d: BindingDeclaration.ID, to output: inout ManglingContext
  ) {
    output.add(operator: .bindingDeclaration)
    output.add(items: program.names(introducedBy: d)) { (o, n) in
      append(name: n, to: &o)
    }
  }

  /// Demangles a binding declaration from `source`.
  private static func takeBindingDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    if let names =
      source.takeItems(takingEachWith: { (s) in
        takeName(from: &s)
      }) {
      return .binding(names: names)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `m` to `output`.
  private mutating func append(module m: Module.ID, to output: inout ManglingContext) {
    if output.addIf(reservedOrRecorded: .module(m), in: program) { return }
    output.add(operator: .module)
    output.add(string: program[m].name.description)
  }

  /// Demangles a module declaration from `source`.
  private static func takeModule(from source: inout DemanglingContext) -> DemangledEntity {
    source.takeString().map({ (s) in .module(s) }) ?? .error
  }

  /// Writes the mangled representation of `s` to `output`.
  private mutating func append(scope s: ScopeIdentity, to output: inout ManglingContext) {
    if output.addIf(reservedOrRecorded: s.asSymbol, in: program) { return }

    let q = output.record(qualification: s)

    // Does `s` point to regular scope?
    if let n = s.node {
      switch program.tag(of: n) {
      case Block.self:
        append(anonymous: s, to: &output)
      case If.self:
        append(anonymous: s, to: &output)
      case ConformanceDeclaration.self:
        append(conformance: ConformanceDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case EnumDeclaration.self:
        append(unqualified: EnumDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case EnumCaseDeclaration.self:
        append(unqualified: EnumCaseDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case ExtensionDeclaration.self:
        append(extension: ExtensionDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case FunctionDeclaration.self:
        append(function: FunctionDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case FunctionBundleDeclaration.self:
        append(functionBundle: FunctionBundleDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case StructDeclaration.self:
        append(unqualified: StructDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case TraitDeclaration.self:
        append(unqualified: TraitDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case TypeAliasDeclaration.self:
        append(unqualified: TypeAliasDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      case VariantDeclaration.self:
        append(variant: VariantDeclaration.ID(uncheckedFrom: n.erased), to: &output)
      default:
        program.unexpected(n)
      }
    }

    // `s` points to a translation unit.
    else {
      precondition(s.isFile)
      append(translationUnit: s.file, to: &output)
    }
    _ = output.record(qualification: q)
    output.record(symbol: s.asSymbol, in: program)
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(anonymous d: ScopeIdentity, to output: inout ManglingContext) {
    output.add(operator: .anonymousScope)
    output.add(integer: UInt64(d.node!.bits))
  }

  /// Demangles an anonymous scope from `source`.
  private static func takeAnonymousScope(from source: inout DemanglingContext) -> DemangledEntity {
    source.takeUInt64().map({ (n) in .anonymousScope(n) }) ?? .error
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(
    conformance d: ConformanceDeclaration.ID, to output: inout ManglingContext
  ) {
    output.add(operator: .conformanceDeclaration)
    append(typeOf: DeclarationIdentity(d), to: &output)
    output.add(items: program[d].contextParameters.usings) { (o, u) in
      append(decl: u, to: &o)
    }
  }

  /// Demangles a conformance declaration from `source`.
  private static func takeConformanceDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    let t = takeType(from: &source)
    if let usings =
      source.takeItems(takingEachWith: { (s) -> DemangledEntity in
        takeEntity(from: &s)
      }) {
      return .conformanceDeclaration(type: t, usings: usings)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(
    extension d: ExtensionDeclaration.ID, to output: inout ManglingContext
  ) {
    output.add(operator: .extensionDeclaration)
    append(typeOf: d, to: &output)
    output.add(items: program[d].contextParameters.usings) { (o, u) in
      append(decl: u, to: &o)
    }
  }

  /// Demangles an extension declaration from `source`.
  private static func takeExtensionDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    let t = takeType(from: &source)
    if let usings =
      source.takeItems(takingEachWith: { (s) -> DemangledEntity in
        takeEntity(from: &s)
      }) {
      return .extensionDeclaration(type: t, usings: usings)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(
    function d: FunctionDeclaration.ID,
    to output: inout ManglingContext
  ) {
    // If the function is anonymous, just encode a unique ID.
    guard let n = program.name(of: DeclarationIdentity(d)) else {
      append(anonymous: ScopeIdentity(node: d), to: &output)
      return
    }

    if program.isStatic(d) {
      output.add(operator: .staticFunctionDeclaration)
    } else {
      output.add(operator: .functionDeclaration)
    }

    append(name: n, to: &output)
    append(typeOf: d, to: &output)
  }

  /// Demangles a function declaration from `source`.
  private static func takeFunctionDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    if let n = takeName(from: &source) {
      let t = takeType(from: &source)
      return .functionDeclaration(name: n, type: t, isStatic: false)
    } else {
      return .error
    }
  }

  /// Demangles a static function declaration from `source`.
  private static func takeStaticFunctionDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    if let n = takeName(from: &source) {
      let t = takeType(from: &source)
      return .functionDeclaration(name: n, type: t, isStatic: true)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(
    functionBundle d: FunctionBundleDeclaration.ID, to output: inout ManglingContext
  ) {
    // If the function bundle is anonymous, just encode a unique ID.
    guard let n = program.name(of: DeclarationIdentity(d)) else {
      append(anonymous: ScopeIdentity(node: d), to: &output)
      return
    }

    output.add(operator: .functionBundleDeclaration)
    append(name: n, to: &output)
    append(typeOf: d, to: &output)
  }

  /// Demangles a function bundle declaration from `source`.
  private static func takeFunctionBundleDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    if let n = takeName(from: &source) {
      let t = takeType(from: &source)
      return .functionBundleDeclaration(name: n, type: t)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `d` to `output`.
  private mutating func append(variant d: VariantDeclaration.ID, to output: inout ManglingContext) {
    output.add(operator: .variantDeclaration)
    output.add(base64Digit: program[d].effect.value)
  }

  /// Demangles a variant declaration from `source`.
  private static func takeVariantDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    if let d = source.takeBase64Digit(),
      let v = AccessEffect(rawValue: d.rawValue) {
      return .variant(v)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `file` to `output`.
  private mutating func append(
    translationUnit file: SourceFile.ID, to output: inout ManglingContext
  ) {
    switch program[file].source.name {
    case .local(let u):
      // Note: assumes all files in a module have a different base name.
      output.add(operator: .sourceFile)
      output.add(string: u.deletingPathExtension().lastPathComponent)
    case .virtual(let i):
      output.add(operator: .virtualSourceFile)
      output.add(integer: Int(i))
    }
  }

  /// Demangles a source file from `source`.
  private static func takeSourceFile(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    source.takeString().map({ (s) in .sourceFile(s) }) ?? .error
  }

  /// Demangles a virtual source file from `source`.
  private static func takeVirtualSourceFile(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    source.takeInt().map({ (s) in .virtualSourceFile(s) }) ?? .error
  }

  /// Writes the mangled representation of `s` defined in `m`, to `output`.
  private mutating func append(
    function s: IRFunction.ID, of m: Module.ID, to output: inout ManglingContext
  ) {
    append(function: program[m].ir[s].name, of: m, to: &output)
  }

  /// Writes the mangled representation of `s` defined in `m`, to `output`.
  private mutating func append(
    function s: IRFunction.Name, of m: Module.ID, to output: inout ManglingContext
  ) {
    switch s {
    case .lowered(let d):
      // Note: no symbol needed; we assume it's a lowered function.
      append(decl: d, to: &output)
    case .initializer(let d):
      output.add(operator: .initializerDeclaration)
      append(unqualified: d, to: &output)
    case .synthesized(let d, let a):
      output.add(operator: .synthesizedFunctionDeclaration)
      append(decl: d, to: &output)
      append(typeArguments: a, to: &output)
    case .implementation(let d, let c, let a):
      output.add(operator: .implementationDeclaration)
      append(decl: d, to: &output)
      append(conformance: c, to: &output)
      append(typeArguments: a, to: &output)
    case .existentialized(let s):
      output.add(operator: .existentializedDeclaration)
      append(function: s, of: m, to: &output)
    }
  }

  /// Demangles an initializer declaration from `source`.
  private static func takeInitializerDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    .initializer(takeEntity(from: &source))
  }

  /// Demangles a synthesized function declaration from `source`.
  private static func takeSynthesizedFunctionDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    let e = takeEntity(from: &source)
    if let a = takeTypeArguments(from: &source) {
      return .synthesizedFunction(e, a)
    } else {
      return .error
    }
  }

  /// Demangles an implementation declaration from `source`.
  private static func takeImplementationDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    let e = takeEntity(from: &source)
    let c = takeConformanceDeclaration(from: &source)
    if let a = takeTypeArguments(from: &source) {
      return .implementation(e, c, a)
    } else {
      return .error
    }
  }

  /// Demangles an existentialized declaration from `source`.
  private static func takeExistentializedDeclaration(
    from source: inout DemanglingContext
  ) -> DemangledEntity {
    .existentialized(takeEntity(from: &source))
  }

  /// Writes the mangled representation of `s` to `output`.
  private mutating func append(table s: IRWitnessTable, to output: inout ManglingContext) {
    output.add(operator: .witnessTable)
    append(type: s.witnessType, to: &output)
  }

  /// Demangles a witness table from `source`.
  private static func takeWitnessTable(from source: inout DemanglingContext) -> DemangledSymbol {
    let t = takeType(from: &source)
    return .witnessTable(t)
  }

  /// Writes the mangled representation of `d`'s type to `output`.
  private mutating func append<T: SyntaxIdentity>(typeOf d: T, to output: inout ManglingContext) {
    append(type: program.type(assignedTo: d), to: &output)
  }

  /// Writes the mangled representation of `s` to `output`.
  private mutating func append(type s: AnyTypeIdentity, to output: inout ManglingContext) {
    if output.addIf(reservedOrRecorded: .type(s), in: program) { return }

    let a = program.types[s]
    switch a {
    case let t as Arrow:
      append(arrow: t, to: &output)
    case let t as AssociatedType:
      append(associatedType: t, to: &output)
    case let t as Bundle:
      append(bundle: t, to: &output)
    case let t as Enum:
      append(enum: t, to: &output)
    case let t as EqualityWitness:
      append(equalityWitness: t, to: &output)
    case let t as FunctionPointer:
      append(functionPointer: t, to: &output)
    case let t as GenericParameter:
      append(genericParameter: t, to: &output)
    case let t as Implication:
      append(implication: t, to: &output)
    case let t as LiteralType:
      append(literalType: t, to: &output)
    case let t as MachineType:
      append(machine: t, to: &output)
    case let t as Metakind:
      append(metakind: t, to: &output)
    case let t as Metatype:
      append(metatype: t, to: &output)
    case let t as OpaqueType:
      append(opaque: t, to: &output)
    case let t as RemoteType:
      append(remote: t, to: &output)
    case let t as Struct:
      append(struct: t, to: &output)
    case let t as Trait:
      append(trait: t, to: &output)
    case let t as Tuple:
      append(tuple: t, to: &output)
    case let t as TypeAlias:
      append(typeAlias: t, to: &output)
    case let t as TypeApplication:
      append(typeApplication: t, to: &output)
    case let t as UniversalType:
      append(universal: t, to: &output)
    default:
      unreachable()
    }
    output.record(symbol: .type(s), in: program)
  }

  /// Demangles a type from `source`.
  static private func takeType(from source: inout DemanglingContext) -> DemangledType {
    guard let o = source.takeOperator() else { return .error }
    let demangled: DemangledType

    switch o {
    case .lookupType:
      demangled = typeOrError(source.takeLookupReference())
    case .reservedType:
      demangled = typeOrError(source.takeReserved())
    case .arrowType:
      demangled = takeArrowType(from: &source)
    case .associatedType:
      demangled = takeAssociatedType(from: &source)
    case .bundleType:
      demangled = takeBundle(from: &source)
    case .enumType:
      demangled = takeEnum(from: &source)
    case .equalityWitnessType:
      demangled = takeEqualityWitness(from: &source)
    case .functionPointerType:
      demangled = takeFunctionPointerType(from: &source)
    case .genericParameterConformerType:
      demangled = takeGenericParameterConformerType(from: &source)
    case .genericParameterUserType:
      demangled = takeGenericParameterUserType(from: &source)
    case .genericParameterNthType:
      demangled = takeGenericParameterNthType(from: &source)
    case .implicationType:
      demangled = takeImplicationType(from: &source)
    case .literalIntegerType:
      demangled = .integerLiteral
    case .literalFloatType:
      demangled = .floatLiteral
    case .machineIntegerType:
      demangled = takeMachineIntegerType(from: &source)
    case .machineFloatType:
      demangled = takeMachineFloatType(from: &source)
    case .machinePointerType:
      demangled = .machine(.ptr)
    case .machineWordType:
      demangled = .machine(.word)
    case .metakindType:
      demangled = takeMetakindType(from: &source)
    case .metatypeType:
      demangled = takeMetatypeType(from: &source)
    case .opaqueEnvironmentType:
      demangled = takeOpaqueEnvironmentType(from: &source)
    case .remoteType:
      demangled = takeRemoteType(from: &source)
    case .structType:
      demangled = takeStruct(from: &source)
    case .traitType:
      demangled = takeTrait(from: &source)
    case .tupleConsType:
      demangled = takeTupleConsType(from: &source)
    case .tupleEmptyType:
      demangled = takeTupleEmptyType(from: &source)
    case .typeAliasType:
      demangled = takeTypeAlias(from: &source)
    case .typeApplicationType:
      demangled = takeApplicationType(from: &source)
    case .universalType:
      demangled = takeUniversalType(from: &source)
    default:
      demangled = .error
    }

    // Record that we've seen `demangled`.
    if o != .lookupType && o != .lookupRelative && o != .reservedType {
      source.record(symbol: .type(demangled))
    }

    return demangled
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(arrow t: Arrow, to output: inout ManglingContext) {
    output.add(operator: .arrowType)
    output.add(base64Digit: t.style)
    output.add(base64Digit: t.effect)
    append(type: t.environment, to: &output)
    output.add(items: t.inputs) { (o, i) in
      o.add(string: i.label ?? "")
      append(type: i.type, to: &o)
    }
    append(type: t.output, to: &output)
  }

  /// Demangles an arrow type from `source`.
  private static func takeArrowType(from source: inout DemanglingContext) -> DemangledType {
    if
      let c = source.take(Call.Style.self),
      let a = source.take(AccessEffect.self),
      let e = Optional.some(takeType(from: &source)),
      let inputs = source.takeItems(takingEachWith: { (s) in takeParameter(from: &s) }) {
      let output = takeType(from: &source)
      return .arrow(style: c, effect: a, environment: e, inputs: inputs, output: output)
    } else {
      return .error
    }
  }

  /// Demangles a parameter or tuple element from `stream`.
  private static func takeParameter(
    from stream: inout DemanglingContext
  ) -> DemangledType.Parameter? {
    guard let l = stream.takeString() else { return nil }
    let t = takeType(from: &stream)
    return .init(label: l.isEmpty ? nil : l, type: t)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(associatedType t: AssociatedType, to output: inout ManglingContext) {
    output.add(operator: .associatedType)
    append(decl: DeclarationIdentity(t.declaration), to: &output)
    append(type: t.qualification.type, to: &output)
  }

  /// Demangles an associated type from `source`.
  private static func takeAssociatedType(from source: inout DemanglingContext) -> DemangledType {
    let d = takeEntity(from: &source)
    let n = takeType(from: &source)
    return .associatedType(declaration: d, type: n)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(bundle t: Bundle, to output: inout ManglingContext) {
    output.add(operator: .bundleType)
    append(type: t.shape.erased, to: &output)
    output.add(base64Digit: t.variants.rawValue)
  }

  /// Demangles a bundle type from `source`.
  private static func takeBundle(from source: inout DemanglingContext) -> DemangledType {
    let s = takeType(from: &source)
    if let v = source.takeBase64Digit() {
      return .bundle(shape: s, variants: AccessEffectSet(rawValue: v.rawValue))
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(enum t: Enum, to output: inout ManglingContext) {
    output.add(operator: .enumType)
    append(decl: DeclarationIdentity(t.declaration), to: &output)
  }

  /// Demangles an enum from `source`.
  private static func takeEnum(from source: inout DemanglingContext) -> DemangledType {
    return .enumType(takeEntity(from: &source))
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(
    equalityWitness t: EqualityWitness, to output: inout ManglingContext
  ) {
    output.add(operator: .equalityWitnessType)
    append(type: t.lhs, to: &output)
    append(type: t.rhs, to: &output)
  }

  /// Demangles an equality witness from `source`.
  private static func takeEqualityWitness(from source: inout DemanglingContext) -> DemangledType {
    let lhs = takeType(from: &source)
    let rhs = takeType(from: &source)
    return .equalityWitness(lhs, rhs)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(
    functionPointer t: FunctionPointer, to output: inout ManglingContext
  ) {
    output.add(operator: .functionPointerType)
    output.add(items: t.inputs) { (o, i) in
      append(type: i, to: &o)
    }
    append(type: t.output, to: &output)
  }

  /// Demangles a function pointer type from `source`.
  private static func takeFunctionPointerType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    if let inputs = source.takeItems(takingEachWith: { (s) in takeType(from: &s) }) {
      let output = takeType(from: &source)
      return .functionPointer(inputs: inputs, output: output)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(
    genericParameter t: GenericParameter, to output: inout ManglingContext
  ) {
    switch t {
    case .conformer(let d, let k):
      output.add(operator: .genericParameterConformerType)
      append(decl: DeclarationIdentity(d), to: &output)
      append(kind: k, to: &output)
    case .user(let d, let k):
      output.add(operator: .genericParameterUserType)
      append(decl: DeclarationIdentity(d), to: &output)
      append(kind: k, to: &output)
    case .nth(let n, let k):
      output.add(operator: .genericParameterNthType)
      output.add(integer: Int(n))
      append(kind: k, to: &output)
    }
  }

  /// Demangles a generic parameter conformer type from `source`.
  private static func takeGenericParameterConformerType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    let d = takeEntity(from: &source)
    return takeKind(from: &source).map({ (k) in .genericParameterConformer(declaration: d, kind: k) }) ?? .error
  }

  /// Demangles a generic parameter user type from `source`.
  private static func takeGenericParameterUserType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    let d = takeEntity(from: &source)
    return takeKind(from: &source).map({ (k) in .genericParameterUser(declaration: d, kind: k) }) ?? .error
  }

  /// Demangles a generic parameter nth type from `source`.
  private static func takeGenericParameterNthType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    if let n = source.takeInt(), let k = takeKind(from: &source) {
      return .genericParameterNth(index: n, kind: k)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(implication t: Implication, to output: inout ManglingContext) {
    output.add(operator: .implicationType)
    output.add(items: t.usings) { (o, u) in
      append(type: u, to: &o)
    }
    append(type: t.head, to: &output)
  }

  /// Demangles an implication type from `source`.
  private static func takeImplicationType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    if let usings = source.takeItems(takingEachWith: { (s) in takeType(from: &s) }) {
      let head = takeType(from: &source)
      return .implication(usings: usings, head: head)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(literalType t: LiteralType, to output: inout ManglingContext) {
    switch t {
    case .integer:
      output.add(operator: .literalIntegerType)
    case .float:
      output.add(operator: .literalFloatType)
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(machine t: MachineType, to output: inout ManglingContext) {
    switch t {
    case .i(let width):
      output.add(operator: .machineIntegerType)
      output.add(integer: Int(width))
    case .word:
      output.add(operator: .machineWordType)
    case .float16:
      output.add(operator: .machineFloatType)
      output.add(integer: 16)
    case .float32:
      output.add(operator: .machineFloatType)
      output.add(integer: 32)
    case .float64:
      output.add(operator: .machineFloatType)
      output.add(integer: 64)
    case .float128:
      output.add(operator: .machineFloatType)
      output.add(integer: 128)
    case .ptr:
      output.add(operator: .machinePointerType)
    }
  }

  /// Demangles a machine integer type from `source`.
  private static func takeMachineIntegerType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    return source.takeInt().map({ (n) in .machine(.i(UInt8(truncatingIfNeeded: n))) }) ?? .error
  }

  /// Demangles a machine float type from `source`.
  private static func takeMachineFloatType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    switch source.takeInt() {
    case .some(16):
      return .machine(.float16)
    case .some(32):
      return .machine(.float32)
    case .some(64):
      return .machine(.float64)
    case .some(128):
      return .machine(.float128)
    default:
      return .error
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(metakind t: Metakind, to output: inout ManglingContext) {
    output.add(operator: .metakindType)
    append(kind: t.inhabitant, to: &output)
  }

  /// Demangles a metakind from `stream`.
  private static func takeMetakindType(from source: inout DemanglingContext) -> DemangledType {
    takeKind(from: &source).map({ (k) in .metakind(k) }) ?? .error
  }

  /// Writes the mangled representation of `k` to `output`.
  private mutating func append(kind k: Kind, to output: inout ManglingContext) {
    output.add(integer: k.rawValue)
  }

  /// Demangles a kind from `source`.
  private static func takeKind(from source: inout DemanglingContext) -> Kind? {
    guard let i = source.takeUInt32() else { return nil }
    return Kind(rawValue: i)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(metatype t: Metatype, to output: inout ManglingContext) {
    output.add(operator: .metatypeType)
    append(type: t.inhabitant, to: &output)
  }

  /// Demangles a metatype from `stream`.
  private static func takeMetatypeType(from source: inout DemanglingContext) -> DemangledType {
    .metatype(takeType(from: &source))
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(opaque t: OpaqueType, to output: inout ManglingContext) {
    switch t {
    case .environment(let d):
      output.add(operator: .opaqueEnvironmentType)
      append(decl: d, to: &output)
    }
  }

  /// Demangles an opaque environment type from `stream`.
  private static func takeOpaqueEnvironmentType(
    from source: inout DemanglingContext
  ) -> DemangledType {
    .opaqueEnvironment(takeEntity(from: &source))
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(remote t: RemoteType, to output: inout ManglingContext) {
    output.add(operator: .remoteType)
    append(type: t.projectee, to: &output)
    output.add(base64Digit: t.access)
  }

  /// Demangles a remote type from `stream`.
  private static func takeRemoteType(from source: inout DemanglingContext) -> DemangledType {
    let t = takeType(from: &source)
    if let a = source.take(AccessEffect.self) {
      return .remote(t, a)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(struct t: Struct, to output: inout ManglingContext) {
    output.add(operator: .structType)
    append(decl: DeclarationIdentity(t.declaration), to: &output)
  }

  /// Demangles a struct type from `stream`.
  private static func takeStruct(from source: inout DemanglingContext) -> DemangledType {
    let e = takeEntity(from: &source)
    return .structType(e)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(trait t: Trait, to output: inout ManglingContext) {
    output.add(operator: .traitType)
    append(decl: DeclarationIdentity(t.declaration), to: &output)
  }

  /// Demangles a trait type from `stream`.
  private static func takeTrait(from source: inout DemanglingContext) -> DemangledType {
    let e = takeEntity(from: &source)
    return .traitType(e)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(tuple t: Tuple, to output: inout ManglingContext) {
    switch t {
    case .cons(let h, let t):
      output.add(operator: .tupleConsType)
      append(type: h, to: &output)
      append(type: t, to: &output)
    case .empty:
      output.add(operator: .tupleEmptyType)
    }
  }

  /// Demangles a tuple cons type from `stream`.
  private static func takeTupleConsType(from source: inout DemanglingContext) -> DemangledType {
    let h = takeType(from: &source)
    let t = takeType(from: &source)
    return .tupleConsType(h, t)
  }

  /// Demangles a tuple empty type from `stream`.
  private static func takeTupleEmptyType(from source: inout DemanglingContext) -> DemangledType {
    return .tupleEmptyType
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(typeAlias t: TypeAlias, to output: inout ManglingContext) {
    output.add(operator: .typeAliasType)
    append(decl: DeclarationIdentity(t.declaration), to: &output)
    append(type: t.aliasee, to: &output)
  }

  /// Demangles a type alias from `source`.
  private static func takeTypeAlias(from source: inout DemanglingContext) -> DemangledType {
    let d = takeEntity(from: &source)
    let t = takeType(from: &source)
    return .typeAlias(declaration: d, aliasee: t)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(
    typeApplication t: TypeApplication,
    to output: inout ManglingContext
  ) {
    output.add(operator: .typeApplicationType)
    append(type: t.abstraction, to: &output)
    append(typeArguments: t.arguments, to: &output)
  }

  /// Demangles an application type from `source`.
  private static func takeApplicationType(from source: inout DemanglingContext) -> DemangledType {
    let t = takeType(from: &source)
    if let a = takeTypeArguments(from: &source) {
      return .typeApplication(abstraction: t, arguments: a)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `a` to `output`.
  private mutating func append(typeArguments a: TypeArguments, to output: inout ManglingContext) {
    output.add(items: a.elements) { (o, e) in
      append(type: e.key.erased, to: &o)
      append(type: e.value, to: &o)
    }
  }

  /// Demangles type arguments from `source`.
  private static func takeTypeArguments(
    from source: inout DemanglingContext
  ) -> [DemangledType.TypeApplicationArgument]? {
    let takeArgument = { (s: inout DemanglingContext) -> DemangledType.TypeApplicationArgument? in
      let k = takeType(from: &s)
      let v = takeType(from: &s)
      return .init(formal: k, argument: v)
    }
    return source.takeItems(takingEachWith: takeArgument)
  }

  /// Writes the mangled representation of `t` to `output`.
  private mutating func append(universal t: UniversalType, to output: inout ManglingContext) {
    output.add(operator: .universalType)
    output.add(items: t.parameters) { (o, p) in
      append(type: p.erased, to: &o)
    }
    append(type: t.head, to: &output)
  }

  /// Demangles a universal type from `source`.
  private static func takeUniversalType(from source: inout DemanglingContext) -> DemangledType {
    if let p = source.takeItems(takingEachWith: { (s) in takeType(from: &s) }) {
      let h = takeType(from: &source)
      return .universalType(parameters: p, head: h)
    } else {
      return .error
    }
  }

  /// Writes the mangled representation of `name` to `output`.
  private mutating func append(name: Name, to output: inout ManglingContext) {
    // Only encode notation and introducer; labels are encoded in types.
    // Encode the presence of introducer in the tag.
    var tag = UInt8(name.notation.rawValue)
    if name.introducer != nil { tag = tag | 0x80 }
    output.add(base64Digit: tag)
    if let i = name.introducer {
      output.add(base64Digit: i)
    }
    output.add(string: name.identifier)
  }

  /// Demangles a name from `source`.
  private static func takeName(from source: inout DemanglingContext) -> Name? {
    guard let tag = source.take(Base64Digit.self)?.rawValue else { return nil }
    let hasIntroducer = (tag & 0x80) != 0
    let notation = OperatorNotation(rawValue: tag & 0x7F)
    let introducer = hasIntroducer
      ? source.take(Base64Digit.self).flatMap { (d) in AccessEffect(rawValue: d.rawValue) }
      : nil
    if let identifier = source.takeString(), let notation = notation {
      return Name(identifier: identifier, notation: notation, introducer: introducer)
    } else {
      return nil
    }
  }

  /// Returns the entity in `s` if it is an entity, or `.error` otherwise.
  private static func entityOrError(_ s: DemangledSymbol?) -> DemangledEntity {
    if case .some(.entity(let e)) = s {
      return e
    } else {
      return .error
    }
  }

  /// Returns the type in `s` if it is a type, or `.error` otherwise.
  private static func typeOrError(_ s: DemangledSymbol?) -> DemangledType {
    if case .some(.type(let t)) = s {
      return t
    } else {
      return .error
    }
  }

}

extension ScopeIdentity {

  /// The mangling symbol corresponding to `self`.
  fileprivate var asSymbol: MangledSymbol {
    if isFile {
      .fileScope(self)
    } else {
      .node(node!)
    }
  }
}
