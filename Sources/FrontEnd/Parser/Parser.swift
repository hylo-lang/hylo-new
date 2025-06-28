import Utilities

/// The parsing of a source file.
public struct Parser {

  /// The context in which a parser is being used.
  private enum Context {

    /// The default context.
    case `default`

    /// The parsing of member declarations.
    case typeBody

    /// The parsing of the subpattern of binding pattern.
    case bindingSubpattern

  }

  /// The tokens in the input.
  private var tokens: Lexer

  /// The position immediately after the last consumed token.
  private var position: SourcePosition

  /// The next token to consume, if already extracted from the source.
  private var lookahead: Token? = nil

  /// The errors that have been collected so far.
  private var errors: [ParseError] = []

  /// The context in which the parser is being used.
  private var context: Context = .default

  /// Creates an instance parsing `source`.
  public init(_ source: SourceFile) {
    self.tokens = Lexer(tokenizing: source)
    self.position = .init(source.startIndex, in: source)
  }

  // MARK: Declarations

  /// Parses the top-level declarations of a file.
  internal consuming func parseTopLevelDeclarations(in file: inout Module.SourceContainer) {
    assert(file.roots.isEmpty)
    var roots: [DeclarationIdentity] = []
    while peek() != nil {
      do {
        try roots.append(parseDeclaration(in: &file))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in (t.tag == .semicolon) || t.isDeclarationHead })
      } catch {
        unreachable()
      }
    }
    for e in errors { file.addDiagnostic(.init(e)) }
    swap(&file.roots, &roots)
  }

  /// Parses a declaration.
  ///
  ///     declaration ::=
  ///       associated-type-declaration
  ///       binding-declaration
  ///       extension-declaration
  ///       function-declaration
  ///       given-declaration
  ///       struct-declaration
  ///       trait-declaration
  ///
  private mutating func parseDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let prologue = try parseDeclarationPrologue(in: &file)

    guard let head = peek() else { throw expected("declaration") }
    switch head.tag {
    case .inout, .let, .set, .sink, .var:
      return try .init(parseBindingDeclaration(after: prologue, in: &file))
    case .case:
      return try .init(parseEnumCaseDeclaration(after: prologue, in: &file))
    case .enum:
      return try .init(parseEnumDeclaration(after: prologue, in: &file))
    case .fun:
      return try parseFunctionOrBundleDeclaration(after: prologue, in: &file)
    case .given:
      return try parseGivenDeclaration(after: prologue, in: &file)
    case .extension:
      return try .init(parseExtensionDeclaration(after: prologue, in: &file))
    case .`init`:
      return try .init(parseInitializerDeclaration(after: prologue, in: &file))
    case .struct:
      return try .init(parseStructDeclaration(after: prologue, in: &file))
    case .trait:
      return try .init(parseTraitDeclaration(after: prologue, in: &file))
    case .type:
      return try parseTypeAliasOrAssociatedTypeDeclaration(after: prologue, in: &file)
    case .name where head.text == "memberwise":
      return try .init(parseInitializerDeclaration(after: prologue, in: &file))
    default:
      throw expected("declaration", at: .empty(at: head.site.start))
    }
  }

  /// Parses the annotations and modifiers of a declaration.
  private mutating func parseDeclarationPrologue(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationPrologue {
    let a = try parseAnnotations(in: &file)
    let m = parseDeclarationModifiers()
    return .init(annotations: a, modifiers: m)
  }

  /// Parses a sequence of annotations.
  private mutating func parseAnnotations(
    in file: inout Module.SourceContainer
  ) throws -> [Annotation] {
    var annotations: [Annotation] = []
    while next(is: .at) {
      try annotations.append(parseAnnotation(in: &file))
    }
    return annotations
  }

  /// Parses an annotation.
  private mutating func parseAnnotation(
    in file: inout Module.SourceContainer
  ) throws -> Annotation {
    let introducer = try take(.at) ?? expected("'@'")
    let identifier = try take(.name) ?? expected("identifier")

    if introducer.site.end != identifier.site.start {
      let s = SourceSpan(from: introducer.site.end, to: identifier.site.start)
      report(.init("extraneous whitespace between '@' and annotation identifier", at: s))
    }

    let arguments: [Parsed<Annotation.Argument>]
    if !whitespaceBeforeNextToken() && next(is: .leftParenthesis) {
      (arguments, _) = try inParentheses { (m0) in
        try m0.commaSeparated(until: Token.hasTag(.rightParenthesis)) { (m1) in
          try m1.parseAnnotationArgument()
        }
      }
    } else {
      arguments = []
    }

    return Annotation(
      identifier: .init(identifier),
      arguments: arguments,
      site: span(from: introducer.site.start))
  }

  /// Parses an argument of an annotation.
  private mutating func parseAnnotationArgument() throws -> Parsed<Annotation.Argument> {
    // Is it a string argument?
    if let s = take(.stringLiteral) {
      return .init(.string(String(s.text.dropFirst().dropLast())), at: s.site)
    }

    // Is it a number argument?
    else if let s = take(.integerLiteral) {
      if let n = Int(s.text) {
        return .init(.number(n), at: s.site)
      } else {
        throw ParseError("'\(s.text)' is not a valid annotation argument", at: s.site)
      }
    }

    // None of the above.
    else { throw expected("annotation argument") }
  }

  /// Parses a sequence of declaration modifiers.
  private mutating func parseDeclarationModifiers() -> [Parsed<DeclarationModifier>] {
    var modifiers: [Parsed<DeclarationModifier>] = []
    while let m = parseOptionalDeclarationModifier() {
      append(m)
    }
    return modifiers

    func append(_ m: Parsed<DeclarationModifier>) {
      for i in 0 ..< modifiers.count {
        if modifiers[i].value == m.value {
          report(.init("duplicate modifier", at: m.site))
          return
        } else if !m.value.canOccurWith(modifiers[i].value) {
          report(.init("'\(m.value)' is incompatible with '\(modifiers[i].value)'", at: m.site))
          return
        } else if !m.value.canOccurAfter(modifiers[i].value) {
          report(.init("'\(m.value)' should occur before '\(modifiers[i].value)'", at: m.site))
          modifiers.insert(m, at: i)
          return
        }
      }
      modifiers.append(m)
    }
  }

  /// Parses a declaration modifier if the next token denotes one.
  ///
  ///     declaration-modifier ::= (one of)
  ///       static private internal private
  ///
  private mutating func parseOptionalDeclarationModifier() -> Parsed<DeclarationModifier>? {
    if let m = parseExpressibleByTokenTag(DeclarationModifier.self) {
      return m
    } else if context == .typeBody, let t = take(contextual: "indirect") {
      return .init(.indirect, at: t.site)
    } else {
      return nil
    }
  }

  /// Parses a binding declaration.
  ///
  ///     binding-declaration ::=
  ///       binding-pattern ('=' expression)?
  ///
  private mutating func parseBindingDeclaration(
    as role: BindingDeclaration.Role = .unconditional,
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> BindingDeclaration.ID {
    let b = try parseBindingPattern(in: &file)
    let i = try parseOptionalInitializerExpression(in: &file)

    // No annotations allowed on binding declarations.
    _ = sanitize(prologue.annotations, accepting: { _ in false })

    return file.insert(
      BindingDeclaration(
        modifiers: prologue.modifiers, role: role, pattern: b, initializer: i,
        site: span(from: file[b].site.start)))
  }

  /// Parses the declaration of an enum case.
  ///
  ///     enum-case-declaration ::=
  ///       'case' identifier '(' parameter-list? ')' ('=' expression)?
  ///
  private mutating func parseEnumCaseDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> EnumCaseDeclaration.ID {
    let introducer = try take(.case) ?? expected("'case'")
    let identifier = parseSimpleIdentifier()
    let parameters = try parseParenthesizedParameterList(in: &file)
    let body: ExpressionIdentity?
    if let assign = take(.assign) {
      body = try parseExpression(in: &file)
      if !parameters.isEmpty {
        let m = "enum case with parameters cannot have an explicit definition"
        report(.init(m, at: assign.site))
      }
    } else {
      body = nil
    }

    // No modifiers or annotations allowed on enum cases.
    _ = sanitize(prologue.annotations, accepting: { _ in false })
    _ = sanitize(prologue.modifiers, accepting: { _ in false })

    return file.insert(
      EnumCaseDeclaration(
        introducer: introducer,
        identifier: identifier,
        parameters: parameters,
        body: body,
        site: span(from: introducer)))
  }

  /// Parses an enum declaration.
  private mutating func parseEnumDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> EnumDeclaration.ID {
    let introducer = try take(.enum) ?? expected("'enum'")
    let identifier = parseSimpleIdentifier()
    let parameters = try parseOptionalTypeParameterClause(in: &file)
    let representation = try next(is: .leftParenthesis) ? parseExpression(in: &file) : nil
    let conformances = try parseOptionalAdjunctConformanceList(until: .leftBrace, in: &file)
    let members = try parseTypeBody(in: &file, accepting: \.isValidEnumMember)

    return file.insert(
      EnumDeclaration(
        annotations: prologue.annotations,
        modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToTypeDeclaration),
        introducer: introducer,
        identifier: identifier,
        parameters: parameters,
        representation: representation,
        conformances: conformances,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses an extension declaration.
  ///
  ///     extension-declaration ::=
  ///       'extension' compile-time-parameters? expression type-body
  ///       'extension' identifier ':' expression type-body
  ///
  private mutating func parseExtensionDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> ExtensionDeclaration.ID {
    let introducer = try take(.extension) ?? expected("'extension'")
    var contextParameters = try parseOptionalContextClause(in: &file)
    let extendee = try parseExpression(in: &file)

    // Are we parsing a trait extension?
    if let colon = take(.colon) {
      if
        let n = file[extendee] as? NameExpression,
        n.isUnqualifiedIdentifier && contextParameters.isEmpty
      {
        let r = try parseExpression(in: &file)
        let l = file.insert(n)
        let w = ExpressionIdentity(desugaredConformance(of: .init(l), to: r, in: &file))
        let u = file.insert(UsingDeclaration(witness: w, site: file[r].site))
        let p = file.insert(
          GenericParameterDeclaration(
            identifier: .init(n.name.value.identifier, at: n.site),
            ascription: nil,
            site: n.site))

        contextParameters = .init(
          types: [p], usings: [.init(u)], site: n.site.extended(upTo: position.index))
      } else {
        report(.init("'unexpected context bound'", at: colon.site))
        recover(at: Token.hasTag(.leftBrace))
      }
    }

    let members = try parseTypeBody(in: &file, accepting: \.isValidStructMember)

    // No modifiers or annotations allowed on extensions.
    _ = sanitize(prologue.annotations, accepting: { _ in false })
    _ = sanitize(prologue.modifiers, accepting: { _ in false })

    return file.insert(
      ExtensionDeclaration(
        introducer: introducer,
        contextParameters: contextParameters,
        extendee: extendee,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a given binding or a conformance declaration.
  ///
  ///     given-declaration ::=
  ///       'given' binding-declaration
  ///       'given' conformance-declaration
  ///
  private mutating func parseGivenDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let introducer = try take(.given) ?? expected("'given'")

    // Are we parsing a given binding declaration?
    if next(satisfies: \.isBindingIntroducer) {
      return try .init(parseBindingDeclaration(as: .given, after: prologue, in: &file))
    }

    // Catch common errors.
    if let u = take(.underscore) {
      report(expected("binding introducer", at: u.site))
    }

    // If the next tokens are `<name> <colon>`, we're parsing a named given. Otherwise, the name
    // name we might have parsed is part of a compound expression.
    var backup = self
    var identifier = take(.name)
    if take(.colon) == nil {
      swap(&self, &backup)
      identifier = nil
    }

    // Parse the context parameters and conformer of a conformance declaration.
    let parameters = try parseOptionalContextClause(in: &file)
    let lhs = try parseExpression(in: &file)

    // If the next token is `=`, we're parsing a given binding declaration whose `let` introducer
    // was left implicit (e.g., `given Int = 1`).
    if let e = try parseOptionalInitializerExpression(in: &file) {
      let s = SourceSpan.empty(at: introducer.site.end)
      let p: PatternIdentity = if let i = identifier {
        .init(file.insert(VariableDeclaration(identifier: .init(i))))
      } else {
        .init(file.insert(WildcardLiteral(site: s)))
      }

      if !parameters.isEmpty {
        report(.init("arbitrary given functions are not supported yet", at: parameters.site))
      }

      let b = file.insert(
        BindingPattern(
          introducer: .init(.let, at: s), pattern: p, ascription: lhs,
          site: span(from: introducer)))
      let d = file.insert(
        BindingDeclaration(
          modifiers: [], role: .given, pattern: b, initializer: e,
          site: span(from: introducer)))
      return .init(d)
    }

    // Otherwise, expect a conformance declaration.
    else {
      _ = try take(contextual: "is") ?? expected("'is'")
      let concept = try parseExpression(in: &file)
      let witness = desugaredConformance(of: lhs, to: concept, in: &file)
      let members = self.next(is: .leftBrace)
        ? try parseTypeBody(in: &file, accepting: \.isValidStructMember)
        : nil

      // No annotations allowed on given declarations.
      _ = sanitize(prologue.annotations, accepting: { _ in false })

      let d = file.insert(
        ConformanceDeclaration(
          modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToConformance),
          introducer: introducer,
          identifier: identifier.map(Parsed.init(_:)),
          contextParameters: parameters,
          witness: witness,
          members: members,
          site: span(from: introducer)))
      return .init(d)
    }
  }

  /// Parses a function bundle declaration.
  ///
  ///     function-declaration ::=
  ///       function-head callable-body?
  ///     function-head ::=
  ///       'fun' function-identifier parameter-clauses access-effect? return-type-ascription?
  ///     function-bundle-declaration ::=
  ///       function-bundle-head bundle-body?
  ///     function-bundle-head ::=
  ///       'fun' function-identifier parameter-clauses 'auto' return-type-ascription?
  ///
  private mutating func parseFunctionOrBundleDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let introducer = try take(.fun) ?? expected("'fun'")
    let identifier = try parseFunctionIdentifier()
    let captures = try parseOptionalCaptureList(in: &file) ?? .empty(at: position)
    let (contextParameters, parameters) = try parseParameterClauses(in: &file)
    let effect = parseOptionalAccessEffect() ?? .init(.let, at: .empty(at: position))

    // Insert the self-parameter of non-static member declarations.
    let isMember: Bool
    var p: [ParameterDeclaration.ID] = []
    if (context == .typeBody) && !prologue.contains(.static) {
      isMember = true
      p = [synthesizeSelfParameter(effect: effect, in: &file)] + parameters
    } else {
      isMember = false
      p = parameters
    }

    let output = try parseOptionalReturnTypeAscription(in: &file)

    // Are we parsing a bundle declaration?
    if effect.value == .auto {
      let b = try parseBundleBody(in: &file)
      let i = asBundleIdentifier(identifier)
      let n = file.insert(
        FunctionBundleDeclaration(
          annotations: prologue.annotations,
          modifiers: prologue.modifiers,
          introducer: .init(introducer, at: introducer.site),
          identifier: i,
          contextParameters: contextParameters,
          captures: captures,
          parameters: p,
          effect: effect,
          output: output,
          variants: b,
          site: introducer.site.extended(upTo: position.index)))
      return .init(n)
    }

    // We're parsing a regular function declaration.
    else {
      let f = Parsed(FunctionDeclaration.Introducer.fun, at: introducer.site)
      let b = try parseOptionalCallableBody(in: &file)
      let n = file.insert(
        FunctionDeclaration(
          annotations: prologue.annotations,
          modifiers: prologue.modifiers,
          introducer: f,
          identifier: identifier,
          contextParameters: contextParameters,
          captures: captures,
          parameters: p,
          effect: isMember ? .init(.let, at: effect.site) : effect,
          output: output,
          body: b,
          site: introducer.site.extended(upTo: position.index)))
      return .init(n)
    }
  }

  /// Parses an initializer declaration.
  ///
  ///     initializer-declaration ::=
  ///       'init' parameter-clauses callable-body?
  ///       'memberwise' 'init'
  ///
  private mutating func parseInitializerDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> FunctionDeclaration.ID {
    let introducer = try parseInitializerIntroducer()
    let receiver = synthesizeSelfParameter(effect: .init(.set, at: introducer.site), in: &file)

    // Are we parsing a custom initializer?
    if introducer.value == .`init` {
      let (contextParameters, parameters) = try parseParameterClauses(in: &file)
      let b = try parseOptionalCallableBody(in: &file)

      return file.insert(
        FunctionDeclaration(
          annotations: prologue.annotations,
          modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToInitializer),
          introducer: introducer,
          identifier: .init(.simple("init"), at: introducer.site),
          contextParameters: contextParameters,
          captures: .empty(at: introducer.site.end),
          parameters: [receiver] + parameters,
          effect: .init(.let, at: introducer.site),
          output: nil,
          body: b,
          site: introducer.site.extended(upTo: position.index)))
    }

    // Are we parsing a memberwise initializer?
    else if introducer.value == .memberwiseinit {
      return file.insert(
        FunctionDeclaration(
          annotations: prologue.annotations,
          modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToInitializer),
          introducer: introducer,
          identifier: .init(.simple("init"), at: introducer.site),
          contextParameters: .empty(at: .empty(at: position)),
          captures: .empty(at: introducer.site.end),
          parameters: [receiver],
          effect: .init(.let, at: introducer.site),
          output: nil,
          body: nil,
          site: introducer.site))
    }

    else { unreachable("invalid introducer") }
  }

  /// Parses the introducer of an initializer declaration.
  ///
  ///     initializer-introducer ::=
  ///       'memberwise'? 'init'
  ///
  private mutating func parseInitializerIntroducer() throws
    -> Parsed<FunctionDeclaration.Introducer>
  {
    if let t = take(.`init`) {
      return .init(.`init`, at: t.site)
    } else if let t = take(contextual: "memberwise") {
      let u = take(.`init`) ?? fix(expected("'init'"), with: t)
      return .init(.memberwiseinit, at: t.site.extended(toCover: u.site))
    } else {
      throw expected("'init'")
    }
  }

  /// Parses the parameter clauses of a callable declaration.
  ///
  ///     parameter-clauses ::=
  ///       context-clause? parameter-list
  ///
  private mutating func parseParameterClauses(
    in file: inout Module.SourceContainer
  ) throws -> (ContextParameters, [ParameterDeclaration.ID]) {
    let s = try parseOptionalContextClause(in: &file)
    let r = try parseParenthesizedParameterList(in: &file)
    return (s, r)
  }

  /// Parses a type parameter clause iff the next token is a left angle bracket.
  ///
  ///     type-parameter-clause ::=
  ///       '<' generic-parameter (',' generic-parameter)* ','? '>'
  ///
  /// Unlike a context clause, a type parameter clause does not admit using declarations.
  private mutating func parseOptionalTypeParameterClause(
    in file: inout Module.SourceContainer
  ) throws -> [GenericParameterDeclaration.ID] {
    if !next(is: .leftAngle) { return [] }
    return try inAngles { (me) in
      let ps = try me.parseCommaSeparatedGenericParameters(admittingUsings: false, in: &file)
      if let h = me.take(.where) {
        me.report(.init("where clause is not allowed here", at: .empty(at: h.site.start)))
        me.recover(at: Token.hasTag(.rightAngle))
      }
      return ps.map(\.0)
    }
  }

  /// Parses a context clause iff the next token is a left angle bracket.
  ///
  ///     context-clause ::=
  ///       '<' generic-parameters where-clause? '>'
  ///
  private mutating func parseOptionalContextClause(
    in file: inout Module.SourceContainer
  ) throws -> ContextParameters {
    if !next(is: .leftAngle) { return .empty(at: .empty(at: position)) }
    let start = nextTokenStart()

    let (ts, us) = try inAngles { (me) in
      // Parse the type parameters and their context bounds.
      let typesAndBounds = try me.parseCommaSeparatedGenericParameters(
        admittingUsings: true, in: &file)

      // Insert desugared context bounds before usings explicitly declared.
      var types = [GenericParameterDeclaration.ID](minimumCapacity: typesAndBounds.count)
      var usings: [DeclarationIdentity] = []
      for (t, bs) in typesAndBounds {
        types.append(t)
        usings.append(contentsOf: bs.map(DeclarationIdentity.init(_:)))
      }

      // Parse other usings.
      try usings.append(contentsOf: me.parseOptionalWhereClause(in: &file))
      return (types, usings)
    }

    return ContextParameters(types: ts, usings: us, site: span(from: start))
  }

  /// Parses the generic parameter declarations of a context clause.
  private mutating func parseCommaSeparatedGenericParameters(
    admittingUsings admitUsings: Bool,
    in file: inout Module.SourceContainer
  ) throws -> [(GenericParameterDeclaration.ID, [UsingDeclaration.ID])] {
    let (ps, _) = try commaSeparated(until: Token.oneOf([.rightAngle, .where])) { (me) in
      try me.parseGenericParameterDeclaration(admittingUsings: admitUsings, in: &file)
    }
    return ps
  }

  /// Parses a generic parameter declaration.
  ///
  ///     generic-parameter ::=
  ///       identifier kind-ascription?
  ///
  private mutating func parseGenericParameterDeclaration(
    admittingUsings admitUsings: Bool,
    in file: inout Module.SourceContainer
  ) throws -> (GenericParameterDeclaration.ID, [UsingDeclaration.ID]) {
    let n = try take(.name) ?? expected("identifier")
    let a = try parseOptionalKindAscription(in: &file)

    let b = try parseOptionalContextBoundList(on: n, in: &file)
    if let c = b.first, !admitUsings {
      report(.init("context bound is not allowed here", at: .empty(at: file[c].site.start)))
    }

    let p = file.insert(
      GenericParameterDeclaration(identifier: .init(n), ascription: a, site: n.site))
    return (p, b)
  }

  private mutating func parseOptionalContextBoundList(
    on conformer: Token, in file: inout Module.SourceContainer
  ) throws -> [UsingDeclaration.ID] {
    guard take(contextual: "is") != nil else { return [] }
    let bs = try ampersandSeparated(until: Token.oneOf([.comma, .where, .rightAngle])) { (me) in
      try me.parseContextBound(on: conformer, in: &file)
    }
    if bs.isEmpty {
      report(expected("expression"))
    }
    return bs
  }

  private mutating func parseContextBound(
    on conformer: Token, in file: inout Module.SourceContainer
  ) throws -> UsingDeclaration.ID {
    let rhs = try parseCompoundExpression(in: &file)
    let lhs = ExpressionIdentity(file.insert(NameExpression(.init(conformer))))
    let witness = ExpressionIdentity(desugaredConformance(of: lhs, to: rhs, in: &file))
    return file.insert(UsingDeclaration(witness: witness, site: file[rhs].site))
  }

  /// Parses a capture list.
  ///
  ///     capture-list ::=
  ///       '[' binding-declaration (',' binding-declaration)* (',' '...'?)? ']'
  ///
  private mutating func parseOptionalCaptureList(
    in file: inout Module.SourceContainer
  ) throws -> CaptureList? {
    if !next(is: .leftBracket) { return nil }

    return try inBrackets { (m0) in
      // Are we parsing `[...]`?
      if let t = m0.take(.ellipsis) {
        return .init(explicit: [], allowsInferredCaptures: true, site: t.site)
      }

      // Parse a comma-separated list of binding declarations.
      let s = m0.position
      let (ds, lastComma) = try m0.commaSeparated(until: Token.hasTag(.rightBracket)) { (m1) in
        try m1.parseBindingDeclaration(after: .empty, in: &file)
      }

      // Is there a trailing ellipsis?
      if let t = m0.take(.ellipsis) {
        if lastComma == nil { m0.report(m0.expected("','", at: .empty(at: t.site.start))) }
        return .init(explicit: ds, allowsInferredCaptures: true, site: .empty(at: s))
      } else {
        return .init(explicit: ds, allowsInferredCaptures: false, site: .empty(at: s))
      }

    }
  }

  /// Parses a list of adjunct conformance declarations iff the next token is `.is`.
  ///
  ///     adjunct-conformance-list ::=
  ///       'is' compound-expression ('&' compound-expression)*
  ///
  private mutating func parseOptionalAdjunctConformanceList(
    until rightDelimiter: Token.Tag, in file: inout Module.SourceContainer
  ) throws -> [ConformanceDeclaration.ID] {
    if let introducer = take(contextual: "is") {
      return try ampersandSeparated(until: Token.hasTag(rightDelimiter)) { me in
        try me.parseAdjunctConformance(introducedBy: introducer, in: &file)
      }
    } else {
      return []
    }
  }

  /// Parses an adjunct conformance declaration.
  ///
  /// An adjunct conformance declaration is parsed as a compound expression after to the head of a
  /// type declaration. It is immediately desugared as a static call whose first argument is a name
  /// expression referring to the conforming type, which forms the type of the witness produced by
  /// the conformance. For example, if the conformance is spelled out as `P<A>` in source, the
  /// expression of the witness is desugared as `P<Self, A>`.
  private mutating func parseAdjunctConformance(
    introducedBy introducer: Token, in file: inout Module.SourceContainer
  ) throws -> ConformanceDeclaration.ID {
    let b = try parseCompoundExpression(in: &file)
    let w = try desugared(bound: b)
    let s = file[w].site

    return file.insert(
      ConformanceDeclaration(
        modifiers: [],
        introducer: introducer,
        identifier: nil,
        contextParameters: .empty(at: s),
        witness: w,
        members: [],
        site: s))

    /// Desugards a compound expression into a call of the form `P<Self, ...>`.
    func desugared(bound b: ExpressionIdentity) throws -> StaticCall.ID {
      switch file[b] {
      case let n as NameExpression:
        return file.insert(StaticCall(callee: b, arguments: conformer(), site: n.site))
      case let n as StaticCall:
        return file.replace(b, for: n.replacing(arguments: conformer() + n.arguments))
      case let n:
        throw ParseError("invalid context bound", at: n.site)
      }
    }

    /// Returns a name expression referring to the conforming type.
    func conformer() -> [ExpressionIdentity] {
      let s = SourceSpan.empty(at: position)
      let e = file.insert(NameExpression(.init("Self", at: s)))
      return [.init(e)]
    }
  }

  /// Parses a where clause iff the next token is `.where`. Otherwise, returns an empty clause.
  private mutating func parseOptionalWhereClause(
    in file: inout Module.SourceContainer
  ) throws -> [DeclarationIdentity] {
    guard take(.where) != nil else { return [] }
    let (ps, _) = try commaSeparated(until: Token.hasTag(.rightAngle)) { (me) in
      try me.parseContextParameter(in: &file)
    }
    return ps
  }

  /// Parses a context parameter.
  private mutating func parseContextParameter(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    if next(satisfies: \.isBindingIntroducer) {
      return try parseNamedContextParameter(in: &file)
    } else {
      return try parseAnonymousContextParameter(in: &file)
    }
  }

  /// Parses a context parameter introduced as a binding declaration.
  private mutating func parseNamedContextParameter(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    .init(try parseBindingDeclaration(as: .given, after: .empty, in: &file))
  }

  /// Parses a context parameter introduced without a name.
  private mutating func parseAnonymousContextParameter(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let l = try parseCompoundExpression(in: &file)
    let s = try take(contextual: "is") ?? take(.equal) ?? expected("'is' or '=='")
    let r = try parseCompoundExpression(in: &file)

    let witness: ExpressionIdentity
    if s.tag == .equal {
      let w = EqualityWitnessExpression(
        lhs: l, rhs: r, site: file[l].site.extended(toCover: file[r].site))
      witness = .init(file.insert(w))
    } else {
      witness = .init(desugaredConformance(of: l, to: r, in: &file))
    }

    let d = file.insert(UsingDeclaration(witness: witness, site: file[witness].site))
    return .init(d)
  }

  /// Parses a comma-separated list of parameter declarations.
  private mutating func parseParenthesizedParameterList(
    in file: inout Module.SourceContainer
  ) throws -> [ParameterDeclaration.ID] {
    let (ps, _) = try inParentheses { (m0) in
      try m0.commaSeparated(until: Token.hasTag(.rightParenthesis)) { (m1) in
        try m1.parseParameterDeclaration(in: &file)
      }
    }
    return ps
  }

  /// Parses a parameter declaration.
  ///
  ///     parameter-declaration ::=
  ///       expression-label? identifier (':' expression)? ('=' expression)?
  ///     expression-label ::=
  ///       identifier
  ///       keyword
  ///
  private mutating func parseParameterDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> ParameterDeclaration.ID {
    let start = nextTokenStart()
    let label: Parsed<String>?
    let identifier: Parsed<String>

    switch (take(if: \.isArgumentLabel), take(.name)) {
    case (let n, .some(let m)):
      identifier = Parsed(m)
      label = n.map({ (t) in t.tag == .underscore ? nil : Parsed(t) }) ?? identifier

    case (.some(let n), nil):
      if n.isKeyword { report(.init("'\(n.text)' is not a valid identifier", at: n.site)) }
      identifier = Parsed(n)
      label = identifier

    case (nil, nil):
      throw expected("parameter declaration")
    }

    let ascription = try parseOptionalParameterAscription(in: &file)
    let defaultValue = try parseOptionalInitializerExpression(in: &file)

    return file.insert(
      ParameterDeclaration(
        label: label,
        identifier: identifier,
        ascription: ascription?.type,
        defaultValue: defaultValue,
        lazyModifier: ascription?.lazyModifier,
        site: span(from: start)))
  }

  /// Parses the body of a callable abstraction iff the next token is a left brace.
  private mutating func parseOptionalCallableBody(
    in file: inout Module.SourceContainer
  ) throws -> [StatementIdentity]? {
    if next(is: .leftBrace) {
      return try parseCallableBody(in: &file)
    } else {
      return nil
    }
  }

  /// Parses the body of a callable abstraction.
  ///
  /// The body is parsed as a sequence of statements enclosed in braces. If the sequence is empty,
  /// the result is a list containing one return statement having no return value. If the sequence
  /// contains a single expression, the result is a list containing one return statement having
  /// that expression as a return value. Otherwise, the result contains the parsed statements.
  private mutating func parseCallableBody(
    in file: inout Module.SourceContainer
  ) throws -> [StatementIdentity] {
    var ss = try entering(.default, { (me) in try me.parseBracedStatementList(in: &file) })

    if ss.isEmpty {
      let r = file.insert(Return(introducer: nil, value: nil, site: .empty(at: position)))
      ss.append(.init(r))
    } else if let s = ss.uniqueElement, file.tag(of: s).value is any Expression.Type {
      let e = ExpressionIdentity(uncheckedFrom: s.erased)
      let r = file.insert(Return(introducer: nil, value: e, site: file[s].site))
      ss[0] = .init(r)
    }

    return ss
  }

  private mutating func parseBundleBody(
    in file: inout Module.SourceContainer
  ) throws -> [VariantDeclaration.ID] {
    let start = nextTokenStart()

    let vs = try inBraces { (m0) in
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
        try m1.parseVariant(in: &file)
      }
    }

    if vs.isEmpty {
      report(.init("bundle requires at least one variant declaration", at: .empty(at: start)))
    }
    return vs
  }

  /// Parses the body of a variant in a function or subscript bundle.
  private mutating func parseVariant(
    in file: inout Module.SourceContainer
  ) throws -> VariantDeclaration.ID {
    let k = try parseOptionalAccessEffect() ?? expected("access effect")
    let b = try parseOptionalCallableBody(in: &file)
    return file.insert(VariantDeclaration(effect: k, body: b, site: span(from: k.site.start)))
  }

  /// Parses a struct declaration.
  ///
  ///     struct-declaration ::=
  ///       struct-introducer identifier type-body
  ///     struct-introducer ::=
  ///       'struct' | 'enum'
  ///
  private mutating func parseStructDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> StructDeclaration.ID {
    let introducer = try take(.struct) ?? expected("'struct'")
    let identifier = parseSimpleIdentifier()
    let parameters = try parseOptionalTypeParameterClause(in: &file)
    let conformances = try parseOptionalAdjunctConformanceList(until: .leftBrace, in: &file)
    let members = try parseTypeBody(in: &file, accepting: \.isValidStructMember)

    return file.insert(
      StructDeclaration(
        annotations: prologue.annotations,
        modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToTypeDeclaration),
        introducer: introducer,
        identifier: identifier,
        parameters: parameters,
        conformances: conformances,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a trait declaration.
  ///
  ///     trait-declaration ::=
  ///       'trait' identifier type-body
  ///
  private mutating func parseTraitDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> TraitDeclaration.ID {
    let introducer = try take(.trait) ?? expected("'trait'")
    let identifier = parseSimpleIdentifier()
    let parameters = try parseOptionalContextClause(in: &file)

    // Base traits are desugared as given requirements before other members.
    var members = try parseOptionalRefinementList(of: identifier.value,  in: &file)
    try members.append(contentsOf: parseTypeBody(in: &file, accepting: \.isValidTraitMember))

    if let p = parameters.usings.first {
      report(.init("constraints on trait parameters are not supported yet", at: file[p].site))
    }

    return file.insert(
      TraitDeclaration(
        annotations: prologue.annotations,
        modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToTypeDeclaration),
        introducer: introducer,
        identifier: identifier,
        parameters: parameters.types,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses an ampersand-separated list of base traits iff the next token is the `refines` keyword
  /// and desugars them as given requirements.
  ///
  /// A base trait declaration is parsed as a compound expression affixed to the head of a trait
  /// declaration. It is immediately desugared as a given requirement whose witness denotes a
  /// conformance to the base trait.
  private mutating func parseOptionalRefinementList(
    of refined: String, in file: inout Module.SourceContainer
  ) throws -> [DeclarationIdentity] {
    guard let introducer = take(contextual: "refines") else { return [] }

    return try ampersandSeparated(until: Token.hasTag(.rightBrace)) { (me) in
      let span = SourceSpan.empty(at: me.nextTokenStart())
      let t0 = try me.parseCompoundExpression(in: &file)
      let t1 = me.synthesizeNameExpression([refined, "Self"], at: span, in: &file)
      let t2 = me.desugaredConformance(of: .init(t1), to: t0, in: &file)
      let t3 = file.insert(
        ConformanceDeclaration(
          modifiers: [],
          introducer: introducer,
          identifier: nil,
          contextParameters: .empty(at: span),
          witness: t2,
          members: nil,
          site: file[t0].site))
      return DeclarationIdentity(t3)
    }
  }

  /// Parses a the body of a type declaration.
  ///
  ///     type-body ::=
  ///       '{' ';'* type-members? '}'
  ///     type-members ::=
  ///       type-members? ';'* declaration ';'*
  ///
  private mutating func parseTypeBody(
    in file: inout Module.SourceContainer, accepting isValid: (SyntaxTag) -> Bool
  ) throws -> [DeclarationIdentity] {
    try entering(.typeBody) { (m0) in
      try m0.inBraces { (m1) in
        try m1.semicolonSeparated(until: .rightBrace) { (m2) in
          let d = try m2.parseDeclaration(in: &file)
          if !isValid(file.tag(of: d)) {
            m2.report(.init("declaration is not allowed here", at: .empty(at: file[d].site.start)))
          }
          return d
        }
      }
    }
  }

  /// Parses a variable declaration.
  private mutating func parseVariableDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> VariableDeclaration.ID {
    let n = try take(.name) ?? expected("identifier")
    return file.insert(VariableDeclaration(identifier: .init(n)))
  }

  /// Parses a type alias or associated type declaration.
  private mutating func parseTypeAliasOrAssociatedTypeDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let introducer = try take(.type) ?? expected("'type'")
    let identifier = parseSimpleIdentifier()

    // If the next token is `<` or `=`, commit to a type alias declaration.
    if next(is: .leftAngle) || next(is: .assign) {
      let parameters = try parseOptionalTypeParameterClause(in: &file)
      _ = try take(.assign) ?? expected("'='")
      let aliasee = try parseExpression(in: &file)

      // No annotations allowed on type aliases.
      _ = sanitize(prologue.annotations, accepting: { _ in false })

      let d = file.insert(
        TypeAliasDeclaration(
          modifiers: sanitize(prologue.modifiers, accepting: \.isApplicableToTypeDeclaration),
          introducer: introducer,
          identifier: identifier,
          parameters: parameters,
          aliasee: aliasee,
          site: introducer.site.extended(upTo: position.index)))
      return .init(d)
    }

    // Otherwise, commit to an associated type declaration.
    else {
      // No modifiers or annotations allowed on associated types.
      _ = sanitize(prologue.annotations, accepting: { _ in false })
      _ = sanitize(prologue.modifiers, accepting: { _ in false })

      let d = file.insert(
        AssociatedTypeDeclaration(
          introducer: introducer,
          identifier: identifier,
          site: span(from: introducer)))
      return .init(d)
    }
  }

  /// Parses an initializer/default expression iff the next token an equal sign.
  ///
  ///     initializer-expression ::=
  ///       '=' expression
  ///
  private mutating func parseOptionalInitializerExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.assign) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Returns `modifiers` sans those that do not satisfy `isValid`.
  private mutating func sanitize(
    _ modifiers: consuming [Parsed<DeclarationModifier>],
    accepting isValid: (DeclarationModifier) -> Bool
  ) -> [Parsed<DeclarationModifier>] {
    var end = modifiers.count
    for i in (0 ..< modifiers.count).reversed() where !isValid(modifiers[i].value) {
      report(.init("declaration cannot be marked '\(modifiers[i].value)'", at: modifiers[i].site))
      modifiers.swapAt(i, end - 1)
      end -= 1
    }
    return .init(modifiers.prefix(upTo: end))
  }

  /// Returns `annotations` sans those that do not satisfy `isValid`.
  private mutating func sanitize(
    _ annotations: consuming [Annotation],
    accepting isValid: (Annotation) -> Bool
  ) -> [Annotation] {
    var end = annotations.count
    for i in (0 ..< annotations.count).reversed() where !isValid(annotations[i]) {
      report(.init("invalid annotation", at: annotations[i].site))
      annotations.swapAt(i, end - 1)
      end -= 1
    }
    return .init(annotations.prefix(upTo: end))
  }

  // MARK: Expressions

  /// Parses an expression.
  private mutating func parseExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    try parseInfixExpression(in: &file)
  }

  /// Parses the root of infix expression whose operator binds at least as tightly as `p`.
  private mutating func parseInfixExpression(
    minimumPrecedence p: PrecedenceGroup = .assignment, in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    let s = position
    var l = try parseConversionExpression(in: &file)

    // Can we parse a term operator?
    while p < .max {
      // Next token isn't considered an infix operator unless it is surrounded by whitespaces.
      guard let h = peek(), h.isOperatorHead, whitespaceBeforeNextToken() else { break }
      guard let (o, q) = try parseOptionalInfixOperator(notTighterThan: p) else { break }

      let r = try parseInfixExpression(minimumPrecedence: q.next, in: &file)
      let f = file.insert(
        NameExpression(
          qualification: l,
          name: .init(Name(identifier: String(o.text), notation: .infix), at: o),
          site: o))
      let n = file.insert(
        Call(
          callee: .init(f),
          arguments: [.init(label: nil, value: r)], style: .parenthesized,
          site: span(from: s)))
      l = .init(n)
    }

    // Can we parse a type operator?
    if next(is: .oplus) {
      var elements = [l]
      while take(.oplus) != nil {
        try elements.append(parseConversionExpression(in: &file))
      }
      let n = file.insert(SumTypeExpression(elements: elements, site: span(from: s)))
      l = .init(n)
    }

    // Done.
    return l
  }

  /// Parses an expression possibly wrapped in a conversion.
  private mutating func parseConversionExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    let l = try parsePrefixExpression(in: &file)
    guard let o = take(.conversion) else { return l }

    let r = try parseExpression(in: &file)
    let n = file.insert(
      Conversion(
        source: l, target: r, semantics: .init(o.text)!,
        site: file[l].site.extended(upTo: position.index)))
    return .init(n)
  }

  /// Parses an expression possibly prefixed by an operator
  private mutating func parsePrefixExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    // Is there a prefix operator? (note: `&` is not a prefix operator)
    if let h = peek(), h.isOperatorHead, (h.tag != .ampersand) {
      let o = try parseOperator()
      if whitespaceBeforeNextToken() { report(separatedUnaryOperator(o)) }

      let e = try parseCompoundExpression(in: &file)
      let f = file.insert(
        NameExpression(
          qualification: e,
          name: .init(Name(identifier: String(o.text), notation: .prefix), at: o),
          site: o))
      let n = file.insert(
        Call(
          callee: .init(f),
          arguments: [], style: .parenthesized,
          site: span(from: file[e].site.start)))
      return .init(n)
    }

    // No prefix operator; simply parse a compound expression.
    else { return try parseCompoundExpression(in: &file) }
  }

  /// Parses an expression made of one or more components.
  ///
  ///     compound-expression ::=
  ///       compound-expression-head
  ///       compound-expression '.' (unqualified-name-expression | decimal-number)
  ///
  private mutating func parseCompoundExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    // Is there a mutation marker?
    let marker = take(.ampersand)
    if let m = marker, whitespaceBeforeNextToken() {
      report(separatedUnaryOperator(m.site))
    }

    let head = try parsePrimaryExpression(in: &file)
    return try appendCompounds(to: head, markedForMutationWith: marker, in: &file)
  }

  /// Parses the arguments and nominal components that can be affixed to `head`.
  private mutating func appendCompounds(
    to head: ExpressionIdentity, markedForMutationWith marker: consuming Token?,
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    var h = head
    while true {
      // Qualifications and bracketed calls bind more tightly than mutation markers.
      if let n = try appendNominalComponent(to: h, in: &file) {
        h = n
      } else if let n = try appendBracketedArguments(to: h, in: &file) {
        h = n
      } else if let m = marker.take() {
        h = .init(file.insert(InoutExpression(marker: m, lvalue: h, site: span(from: m))))
      } else if let n = try appendParenthesizedArguments(to: h, in: &file) {
        h = n
      } else if let n = try appendAngledArguments(to: h, in: &file) {
        h = n
      } else {
        break
      }
    }
    return h
  }

  /// If the next token is a dot, parses a nominal component and returns a name expression
  /// qualified by `head`. Otherwise, returns `nil`.
  private mutating func appendNominalComponent(
    to head: ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.dot) == nil { return nil }
    let n = try parseName()
    let s = span(from: file[head].site.start)
    let m = file.insert(NameExpression(qualification: head, name: n, site: s))
    return .init(m)
  }

  /// If the next token is a left angle, parses an argument list and returns a static call applying
  /// `head`. Otherwise, returns `nil`.
  private mutating func appendAngledArguments(
    to head: ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if whitespaceBeforeNextToken() || !next(is: .leftAngle) { return nil }
    let (a, _) = try inAngles { (m0) in
      try m0.commaSeparated(until: Token.hasTag(.rightAngle)) { (m1) in
        try m1.parseExpression(in: &file)
      }
    }
    let s = file[head].site.extended(upTo: position.index)
    let m = file.insert(StaticCall(callee: head, arguments: a, site: s))
    return .init(m)
  }

  /// If the next token is a left bracket, parses an argument list and returns a call applying
  /// `head`. Otherwise, returns `nil`.
  private mutating func appendBracketedArguments(
    to head: ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if whitespaceBeforeNextToken() || !next(is: .leftBracket) { return nil }
    let (a, _) = try inBrackets { (me) in
      try me.parseLabeledExpressionList(until: .rightBracket, in: &file)
    }
    let s = file[head].site.extended(upTo: position.index)
    let m = file.insert(Call(callee: head, arguments: a, style: .bracketed, site: s))
    return .init(m)
  }

  /// If the next token is a left parenthesis, parses an argument list and returns a call applying
  /// `head`. Otherwise, returns `nil`.
  private mutating func appendParenthesizedArguments(
    to head: ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if whitespaceBeforeNextToken() || !next(is: .leftParenthesis) { return nil }
    let (a, _) = try inParentheses { (me) in
      try me.parseLabeledExpressionList(until: .rightParenthesis, in: &file)
    }
    let s = file[head].site.extended(upTo: position.index)
    let m = file.insert(Call(callee: head, arguments: a, style: .parenthesized, site: s))
    return .init(m)
  }

  /// Parses a list of labeled expressions.
  ///
  ///     labeled-expression-list ::=
  ///       labeled-expression (',' labeled-expression)* ','?
  ///     labeled-expression ::=
  ///       (expression-label ':')? expression
  ///
  private mutating func parseLabeledExpressionList(
    until rightDelimiter: Token.Tag, in file: inout Module.SourceContainer
  ) throws -> ([LabeledExpression], lastComma: Token?) {
    try labeledSyntaxList(until: rightDelimiter) { (me) in
      try me.parseExpression(in: &file)
    }
  }

  /// Parses a primary expression.
  ///
  ///     primary-expression ::=
  ///       boolean-literal
  ///       tuple-literal
  ///       wildcard-literal
  ///       unqualified-name-expression
  ///       impliclty-qualified-name-expression
  ///       remote-type-expression
  ///       singleton-type-expression
  ///       tuple-type-expression
  ///       '(' expression ')'
  ///
  private mutating func parsePrimaryExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    switch peek()?.tag {
    case .true, .false:
      return .init(file.insert(BooleanLiteral(site: take()!.site)))
    case .integerLiteral:
      return .init(file.insert(IntegerLiteral(site: take()!.site)))
    case .stringLiteral:
      return .init(file.insert(StringLiteral(site: take()!.site)))
    case .underscore:
      return try .init(parseWildcardLiteral(in: &file))
    case .dot:
      return try .init(parseImplicitlyQualifiedNameExpression(in: &file))
    case .if:
      return try .init(parseIf(in: &file))
    case .match:
      return try .init(parsePatternMatch(in: &file))
    case .fun:
      return try .init(parseLambda(in: &file))
    case .name:
      return try .init(parseUnqualifiedNameExpression(in: &file))
    case .auto, .inout, .let, .set, .sink:
      return try .init(parseRemoteTypeExpression(in: &file))
    case .leftBrace:
      return try .init(parseTupleTypeExpression(in: &file))
    case .leftBracket:
      return try .init(parseArrowExpression(in: &file))
    case .leftParenthesis:
      return try parseTupleOrParenthesizedExpression(in: &file)
    default:
      throw expected("expression")
    }
  }

  /// Parses the expression of an arrow type.
  ///
  ///     arrow-expression ::=
  ///       '[' expression? ']' '(' arrow-parameter-list? ')' access-effect? '->' expression
  ///
  private mutating func parseArrowExpression(
    in file: inout Module.SourceContainer
  ) throws -> ArrowExpression.ID {
    let start = nextTokenStart()

    // Environment.
    let environment = try inBrackets { (me) -> ExpressionIdentity? in
      me.next(is: .rightBracket) ? nil : try me.parseExpression(in: &file)
    }

    // Parameters.
    let (parameters, _) = try inParentheses { (m0) in
      try m0.commaSeparated(until: Token.hasTag(.rightParenthesis)) { (m1) in
        try m1.parseArrowParameter(in: &file)
      }
    }

    // Effect and return type.
    let effect = parseOptionalAccessEffect() ?? .init(.let, at: .empty(at: position))
    _ = try take(.arrow) ?? expected("'->'")
    let output = try parseExpression(in: &file)

    return file.insert(
      ArrowExpression(
        environment: environment,
        parameters: parameters,
        effect: effect,
        output: output,
        site: span(from: start)))
  }

  /// Parses an arrow parameter.
  private mutating func parseArrowParameter(
    in file: inout Module.SourceContainer
  ) throws -> ArrowExpression.Parameter {
    let label: Parsed<String>?
    let ascription: ExpressionIdentity

    // If the next token is an access effect, it is either a label and then following token is a
    // colon, or it is the effect of a remote type expression.
    if let k = parseOptionalAccessEffect() {
      if take(.colon) != nil {
        label = Parsed(String(k.site.text), at: k.site)
        ascription = try parseExpression(in: &file)
      } else {
        let e = try parseExpression(in: &file)
        let a = file.insert(
          RemoteTypeExpression(access: k, projectee: e, site: span(from: k.site.start)))
        label = nil
        ascription = .init(a)
      }
    }

    // If the next token is a name or keyword, it is either a label and then following token is a
    // colon, or it is part of an expression.
    else if let n = take(if: \.isArgumentLabel) {
      if take(.colon) != nil {
        label = n.tag == .underscore ? nil : Parsed(n)
        ascription = try parseExpression(in: &file)
      } else if n.tag == .name {
        let identifier = Name(identifier: String(n.text))
        label = nil
        ascription = .init(file.insert(NameExpression(Parsed(identifier, at: n.site))))
      } else {
        throw ParseError("'\(n.text)' is not a valid identifier", at: n.site)
      }
    }

    // Otherwise, just parse a type expression.
    else {
      label = nil
      ascription = try parseExpression(in: &file)
    }

    let a = desugaredParameterAscription(ascription, in: &file)
    return .init(label: label, ascription: a)
  }

  /// Parses an if-expression.
  ///
  ///     conditional-expression ::=
  ///       'if' condition-item (',' condition-item)* '{' statement-list '}' else?
  ///     else ::=
  ///       'else' conditional-expression
  ///       'else' '{' statement-list '}'
  ///
  private mutating func parseIf(in file: inout Module.SourceContainer) throws -> If.ID {
    let i = try take(.if) ?? expected("'if'")
    let c = try parseConditionList(in: &file)
    let s = try parseConditionalBody(in: &file)
    let f = try parseElseBranch(in: &file)
    return file.insert(
      If(introducer: i, conditions: c, success: s, failure: f, site: span(from: i)))
  }

  /// Parses a condition.
  private mutating func parseConditionList(
    in file: inout Module.SourceContainer
  ) throws -> [ConditionIdentity] {
    var result = [try parseCondition(in: &file)]
    while take(.comma) != nil {
      result.append(try parseCondition(in: &file))
    }
    return result
  }

  /// Parses a single item in a condition.
  private mutating func parseCondition(
    in file: inout Module.SourceContainer
  ) throws -> ConditionIdentity {
    let head = try peek() ?? expected("expression")
    switch head.tag {
    case .inout, .let, .set, .sink, .var:
      return try .init(parseBindingDeclaration(as: .condition, after: .empty, in: &file))
    default:
      return try .init(parseExpression(in: &file))
    }
  }

  /// Parses the else-branch of a conditional expression iff the next token if `else` or returns
  /// an empty block otherwise.
  private mutating func parseElseBranch(
    in file: inout Module.SourceContainer
  ) throws -> If.ElseIdentity {
    // Can we consume `else`?
    if take(.else) != nil {
      if next(is: .if) {
        return try .init(parseIf(in: &file))
      } else {
        return try .init(parseConditionalBody(in: &file))
      }
    }

    // Create an empty block at the currentposition.
    else {
      return .init(file.insert(Block(introducer: nil, statements: [], site: .empty(at: position))))
    }
  }

  /// Parses the body of a conditional expression or loop.
  private mutating func parseConditionalBody(
    in file: inout Module.SourceContainer
  ) throws -> Block.ID {
    let start = nextTokenStart()
    let ss = try parseBracedStatementList(in: &file)
    return file.insert(Block(introducer: nil, statements: ss, site: span(from: start)))
  }

  /// Parses a pattern matching expression.
  ///
  ///     pattern-match ::=
  ///       'match' expression '{' pattern-match-case* '}'
  ///
  private mutating func parsePatternMatch(
    in file: inout Module.SourceContainer
  ) throws -> PatternMatch.ID {
    let i = try take(.match) ?? expected("'match'")
    let s = try parseExpression(in: &file)
    let b = try inBraces { (m0) in
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
        try m1.parsePatternMatchCase(in: &file)
      }
    }

    return file.insert(
      PatternMatch(introducer: i, scrutinee: s, branches: b, site: span(from: i)))
  }

  /// Parses a case of a pattern matching expression.
  ///
  ///     pattern-match-case ::=
  ///       'case' pattern '{' statetement* '}'
  ///
  private mutating func parsePatternMatchCase(
    in file: inout Module.SourceContainer
  ) throws -> PatternMatchCase.ID {
    let i = try take(.case) ?? expected("'case'")
    let p = try parsePattern(in: &file)
    let b = try inBraces { (m0) in
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
        try m1.parseStatement(in: &file)
      }
    }

    return file.insert(
      PatternMatchCase(introducer: i, pattern: p, body: b, site: span(from: i)))
  }

  /// Parses a lambda.
  ///
  ///     lambda ::=
  ///       'fun' lambda-captures parameter-list ('->' expression)? callable-body
  ///
  private mutating func parseLambda(in file: inout Module.SourceContainer) throws -> Lambda.ID {
    let introducer = try take(.fun) ?? expected("'fun'")
    let captures = try parseOptionalCaptureList(in: &file) ?? .inferred(at: position)
    let parameters = try parseParenthesizedParameterList(in: &file)
    let effect = parseOptionalAccessEffect() ?? .init(.let, at: .empty(at: position))
    let output = try parseOptionalReturnTypeAscription(in: &file)
    let body = try parseCallableBody(in: &file)

    let f = file.insert(
      FunctionDeclaration(
        annotations: [],
        modifiers: [],
        introducer: .init(.fun, at: introducer.site),
        identifier: .init(.lambda, at: introducer.site),
        contextParameters: .empty(at: .empty(at: introducer.site.end)),
        captures: captures,
        parameters: parameters,
        effect: effect,
        output: output, body: body,
        site: span(from: introducer)))
    return file.insert(Lambda(function: f, site: span(from: introducer)))
  }

  /// Parses a remote type expression.
  ///
  ///     remote-type-expression ::=
  ///       access-effect expression
  ///
  private mutating func parseRemoteTypeExpression(
    in file: inout Module.SourceContainer
  ) throws -> RemoteTypeExpression.ID {
    let k = parseAccessEffect()
    let e = try parseExpression(in: &file)
    return file.insert(
      RemoteTypeExpression(access: k, projectee: e, site: k.site.extended(upTo: position.index)))
  }

  /// Parses an access effect.
  ///
  ///     access-effect ::= (one of)
  ///       auto let inout set sink
  ///
  private mutating func parseAccessEffect() -> Parsed<AccessEffect> {
    if let k = parseOptionalAccessEffect() {
      return k
    } else {
      return fix(expected("access specifier"), with: Parsed(.let, at: .empty(at: position)))
    }
  }

  /// Parses an access effect iff the next token denotes one.
  private mutating func parseOptionalAccessEffect() -> Parsed<AccessEffect>? {
    parseExpressibleByTokenTag(AccessEffect.self)
  }

  /// Parses a name expression with an implicit qualification.
  ///
  ///     implicitly-qualified-name-expression ::=
  ///       '.' identifier
  ///
  private mutating func parseImplicitlyQualifiedNameExpression(
    in file: inout Module.SourceContainer
  ) throws -> NameExpression.ID {
    let dot = try take(.dot) ?? expected("'.'")
    let n = try parseName()
    let q = file.insert(ImplicitQualification(site: dot.site))
    return file.insert(NameExpression(qualification: .init(q), name: n, site: span(from: dot)))
  }

  /// Parses an unqualified name expression.
  ///
  ///     unqualified-name-expression ::= (token)
  ///       identifier ('@' access-effect)?
  ///
  private mutating func parseUnqualifiedNameExpression(
    in file: inout Module.SourceContainer
  ) throws -> NameExpression.ID {
    let n = try parseName()
    return file.insert(NameExpression(n))
  }

  /// Parses a name.
  private mutating func parseName() throws -> Parsed<Name> {
    let head = try peek() ?? expected("name")

    var identifier: String
    var notation: OperatorNotation = .none
    var introducer: AccessEffect? = nil

    if head.isOperatorNotation {
      (notation, identifier) = try parseOperatorIdentifier().value
    } else if head.tag == .name {
      _ = take()
      identifier = String(head.text)
    } else {
      throw expected("name")
    }

    if take(affixed: .at) != nil {
      introducer = parseAccessEffect().value
    }

    return .init(
      Name(identifier: identifier, notation: notation, introducer: introducer),
      at: span(from: head.site.start))
  }

  /// Parses a tuple type expression.
  ///
  ///     tuple-type-expression ::=
  ///       '{' tuple-type-body? '}'
  ///     tuple-type-body ::=
  ///       labeled-expression (',' labeled-expression)*
  ///
  private mutating func parseTupleTypeExpression(
    in file: inout Module.SourceContainer
  ) throws -> TupleTypeExpression.ID {
    let start = nextTokenStart()
    let (elements, _) = try inBraces { (me) in
      try me.parseLabeledExpressionList(until: .rightBrace, in: &file)
    }
    return file.insert(TupleTypeExpression(elements: elements, site: span(from: start)))
  }

  /// Parses a tuple literal or a parenthesized expression.
  ///
  ///     tuple-literal ::=
  ///       '(' tuple-literal-body? ')'
  ///     tuple-literal-body ::=
  ///       labeled-expression (',' labeled-expression)*
  ///
  private mutating func parseTupleOrParenthesizedExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    let start = nextTokenStart()
    let (elements, lastComma) = try inParentheses { (me) in
      try me.parseLabeledExpressionList(until: .rightParenthesis, in: &file)
    }

    if (elements.count == 1) && (elements[0].label == nil) && (lastComma == nil) {
      return elements[0].value
    } else {
      return .init(file.insert(TupleLiteral(elements: elements, site: span(from: start))))
    }
  }

  /// Parses a wildcard literal.
  ///
  ///     wildcard-literal ::=
  ///       '_'
  ///
  private mutating func parseWildcardLiteral(
    in file: inout Module.SourceContainer
  ) throws -> WildcardLiteral.ID {
    let u = try take(.underscore) ?? expected("'_'")
    return file.insert(WildcardLiteral(site: u.site))
  }

  /// Parses a type ascription iff the next token is a colon.
  ///
  ///     type-ascription ::=
  ///       ':' expression
  ///
  private mutating func parseOptionalTypeAscription(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.colon) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Parses a kind ascription iff the next token is a double colon.
  ///
  ///     kind-ascription ::=
  ///       '::' kind-expression
  ///
  private mutating func parseOptionalKindAscription(
    in file: inout Module.SourceContainer
  ) throws -> KindExpression.ID? {
    if take(.doubleColon) != nil {
      return try parseKind(in: &file)
    } else {
      return nil
    }
  }

  /// Parses a return type ascription iff the next token is an arrow.
  ///
  ///     return-type-ascription ::=
  ///       '->' expression
  ///
  private mutating func parseOptionalReturnTypeAscription(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.arrow) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Parses the type ascription of a parameter iff the next token is a colon.
  private mutating func parseOptionalParameterAscription(
    in file: inout Module.SourceContainer
  ) throws -> (lazyModifier: Token?, type: RemoteTypeExpression.ID)? {
    if take(.colon) != nil {
      let m = take(contextual: "lazy")
      let e = try parseExpression(in: &file)
      let a = desugaredParameterAscription(e, in: &file)
      return (m, a)
    } else {
      return nil
    }
  }

  // MARK: Kinds

  /// Parses a the expression of a kind.
  ///
  ///     kind-expression ::=
  ///       '*'
  ///       '(' kind-expression ')'
  ///       kind-expression ('->' kind-expression)*
  ///
  private mutating func parseKind(
    in file: inout Module.SourceContainer
  ) throws -> KindExpression.ID {
    if peek()?.tag == .leftParenthesis {
      return try inParentheses({ (me) in try me.parseKind(in: &file) })
    }

    let head = try take(.star) ?? expected("kind")
    var kind = file.insert(KindExpression(value: .proper, site: head.site))

    while take(.arrow) != nil {
      let r = try parseKind(in: &file)
      let s = head.site.extended(upTo: position.index)
      kind = file.insert(KindExpression(value: .arrow(kind, r), site: s))
    }

    return kind
  }

  // MARK: Patterns

  /// Parses a pattern.
  ///
  ///     pattern ::=
  ///       binding-pattern
  ///       tuple-pattern
  ///       expression
  ///
  private mutating func parsePattern(
    in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    switch peek()?.tag {
    case .inout, .let, .set, .sink:
      return try .init(parseBindingPattern(in: &file))
    case .name:
      return try parseNameOrDeconstructingPattern(in: &file)
    case .dot:
      return try parseImplicitlyQualifiedDeconstructingPattern(in: &file)
    case .leftParenthesis:
      return try parseTupleOrParenthesizedPattern(in: &file)
    case .underscore:
      return try .init(parseWildcardLiteral(in: &file))
    default:
      return try .init(parseExpression(in: &file))
    }
  }

  /// Parses a binding pattern.
  private mutating func parseBindingPattern(
    in file: inout Module.SourceContainer
  ) throws -> BindingPattern.ID {
    let i = try parseBindingIntroducer()

    // Identifiers occurring in binding subpatterns denote variable declarations.
    return try entering(.bindingSubpattern) { (me) in
      let p = try me.parsePattern(in: &file)
      let a = try me.parseOptionalTypeAscription(in: &file)
      let s = i.site.extended(upTo: me.position.index)
      return file.insert(BindingPattern(introducer: i, pattern: p, ascription: a, site: s))
    }
  }

  /// Parses the introducer of a binding pattern.
  ///
  ///     binding-introducer ::=
  ///       'sink'? 'let'
  ///       'var'
  ///       'inout'
  ///
  private mutating func parseBindingIntroducer() throws -> Parsed<BindingPattern.Introducer> {
    switch peek()?.tag {
    case .let:
      return Parsed(.let, at: take()!.site)
    case .set:
      return Parsed(.set, at: take()!.site)
    case .var:
      return Parsed(.var, at: take()!.site)
    case .inout:
      return Parsed(.inout, at: take()!.site)
    case .sink:
      let a = take()!
      let b = take(.let) ?? fix(expected("'let'"), with: a)
      return Parsed(.sinklet, at: a.site.extended(toCover: b.site))
    default:
      throw expected("binding introducer")
    }
  }

  /// Parses a deconstructing pattern with an implicit qualification.
  ///
  ///     implicitly-qualified-pattern ::=
  ///       '.' extraction-pattern
  ///
  private mutating func parseImplicitlyQualifiedDeconstructingPattern(
    in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    if let dot = peek(), dot.tag == .dot {
      let q = ExpressionIdentity(file.insert(ImplicitQualification(site: dot.site)))
      return try parseNameOrExtractingPattern(qualifiedBy: q, in: &file)
    } else {
      throw expected("'.'")
    }
  }

  /// Parses a compound name expression or a deconstructing pattern.
  private mutating func parseNameOrDeconstructingPattern(
    in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    // If we're parsing the sub-pattern of a binding pattern, parse unparenthesized names as
    // variable declarations.
    if context == .bindingSubpattern {
      return try .init(parseVariableDeclaration(in: &file))
    }

    // Otherwise, starts with a name expression and look if it qualifies a deconstructing pattern.
    else {
      let q = try ExpressionIdentity(parseUnqualifiedNameExpression(in: &file))
      return try parseNameOrExtractingPattern(qualifiedBy: q, in: &file)
    }
  }

  /// Parses a compound expression or an extracting pattern qualified by `q`.
  private mutating func parseNameOrExtractingPattern(
    qualifiedBy q: ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    let start = file[q].site.start
    var head = q

    while true {
      if let n = try appendNominalComponent(to: head, in: &file) {
        head = n
      } else if let n = try appendAngledArguments(to: head, in: &file) {
        head = n
      } else if next(is: .leftParenthesis) && !whitespaceBeforeNextToken() {
        // Parse the last component as an unqualified deconstructing pattern.
        let (e, _) = try inParentheses { (me) in try
          me.parseLabeledPatternList(until: .rightParenthesis, in: &file)
        }
        let s = span(from: start)
        let n = file.insert(ExtractorPattern(extractor: head, elements: e, site: s))
        return .init(n)
      } else {
        // Give up on parsing a pattern and assume we just parsed some qualification.
        return try .init(appendCompounds(to: head, markedForMutationWith: nil, in: &file))
      }
    }
  }

  /// Parses a tuple pattern or a parenthesized pattern.
  ///
  ///     tuple-pattern ::=
  ///       '(' tuple-pattern-body? ')'
  ///     tuple-pattern-body ::=
  ///       labeled-pattern (',' labeled-pattern)*
  ///
  private mutating func parseTupleOrParenthesizedPattern(
    in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    let start = nextTokenStart()
    let (elements, lastComma) = try inParentheses { (me) in
      try me.parseLabeledPatternList(until: .rightParenthesis, in: &file)
    }

    if (elements.count == 1) && (elements[0].label == nil) && (lastComma == nil) {
      return elements[0].value
    } else {
      return .init(file.insert(TuplePattern(elements: elements, site: span(from: start))))
    }
  }

  /// Parses a parenthesized list of labeled expressions.
  ///
  ///     labeled-pattern-list ::=
  ///       labeled-pattern (',' labeled-pattern)* ','?
  ///     labeled-pattern ::=
  ///       (expression-label ':')? pattern
  ///
  private mutating func parseLabeledPatternList(
    until rightDelimiter: Token.Tag, in file: inout Module.SourceContainer
  ) throws -> ([LabeledPattern], lastComma: Token?) {
    try labeledSyntaxList(until: rightDelimiter) { (me) in
      try me.parsePattern(in: &file)
    }
  }

  // MARK: Statements

  /// Parses a statement.
  ///
  ///     statement ::=
  ///       assignment-statement
  ///       discard-statement
  ///       return-statement
  ///       declaration
  ///       expression
  ///
  private mutating func parseStatement(
    in file: inout Module.SourceContainer
  ) throws -> StatementIdentity {
    let head = try peek() ?? expected("statement")
    defer { ensureStatementDelimiter() }

    switch head.tag {
    case .underscore:
      return try .init(parseDiscardStement(in: &file))
    case .return:
      return try .init(parseReturnStatement(in: &file))
    case _ where head.isDeclarationHead:
      return try .init(parseDeclaration(in: &file))
    default:
      return try parseAssignmentOrExpression(in: &file)
    }
  }

  /// Parses a discard statement.
  ///
  ///     discard-statement ::=
  ///       '_' '=' expression
  ///
  private mutating func parseDiscardStement(
    in file: inout Module.SourceContainer
  ) throws -> Discard.ID {
    let i = try take(.underscore) ?? expected("'_'")
    if take(.assign) == nil {
      throw expected("'='")
    }
    let v = try parseExpression(in: &file)
    return file.insert(Discard(value: v, site: span(from: i)))
  }

  /// Parses a return statement.
  ///
  ///     return-statement ::=
  ///       'return' expression?
  ///
  private mutating func parseReturnStatement(
    in file: inout Module.SourceContainer
  ) throws -> Return.ID {
    let i = try take(.return) ?? expected("'return'")

    // The return value must be on the same line.
    let v: ExpressionIdentity?
    if statementDelimiterBeforeNextToken() || next(is: .rightBrace) {
      v = nil
    } else {
      v = try parseExpression(in: &file)
    }

    return file.insert(Return(introducer: i, value: v, site: span(from: i)))
  }

  /// Parses an assignment or an expression.
  ///
  ///     assignment-statement ::=
  ///       expression '=' expression
  ///
  private mutating func parseAssignmentOrExpression(
    in file: inout Module.SourceContainer
  ) throws -> StatementIdentity {
    let l = try parseExpression(in: &file)
    if let a = take(.assign) {
      if !withespacesAround(a.site) { report(inconsistentWhitespaces(around: a.site)) }
      let r = try parseExpression(in: &file)
      let n = file.insert(
        Assignment(lhs: l, rhs: r, site: file[l].site.extended(upTo: position.index)))
      return .init(n)
    } else {
      return .init(l)
    }
  }

  /// Parses a list of statements in braces.
  private mutating func parseBracedStatementList(
    in file: inout Module.SourceContainer
  ) throws -> [StatementIdentity] {
    try inBraces { (m0) in
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
        try m1.parseStatement(in: &file)
      }
    }
  }

  // MARK: Identifiers

  /// Parses a function identifier.
  ///
  ///     function-identider ::=
  ///       identifier
  ///       operator-identifier
  ///
  private mutating func parseFunctionIdentifier(
  ) throws -> Parsed<FunctionIdentifier> {
    if let t = peek() {
      if t.isOperatorNotation {
        let i = try parseOperatorIdentifier()
        return .init(.operator(i.value.notation, i.value.identifier), at: i.site)
      } else if t.isOperatorHead {
        report(.init("missing operator notation", at: .empty(at: t.site.start)))
        let o = try parseOperator()
        return .init(.operator(.none, String(o.text)), at: o)
      }
    }

    let identifier = parseSimpleIdentifier()
    return .init(.simple(identifier.value), at: identifier.site)
  }

  /// Returns `i` asa bundle identifier, reporting an error if it's an operator.
  private mutating func asBundleIdentifier(_ i: Parsed<FunctionIdentifier>) -> Parsed<String> {
    if case .simple(let s) = i.value {
      return .init(s, at: i.site)
    } else {
      report(.init("operator identifier cannot be used to name bundle", at: i.site))
      return .init(i.value.description, at: i.site)
    }
  }

  /// Parses an operator identifier.
  ///
  ///     operator-identifier ::= (token)
  ///       operator-notation operator
  ///
  private mutating func parseOperatorIdentifier(
  ) throws -> Parsed<(notation: OperatorNotation, identifier: String)> {
    let n = try parseOperatorNotation()
    let i = try parseOperator()

    if n.site.end != i.start {
      report(.init("illegal space between after operator notation", at: i))
    }

    return .init((n.value, String(i.text)), at: n.site.extended(toCover: i))
  }

  /// Parses an operator notation.
  private mutating func parseOperatorNotation() throws -> Parsed<OperatorNotation> {
    try parseExpressibleByTokenTag(OperatorNotation.self) ?? expected("operator notation")
  }

  /// Parses an operator and returns the region of the file from which it has been extracted.
  private mutating func parseOperator() throws -> SourceSpan {
    // Single-token operators.
    if let t = take(oneOf: [.ampersand, .equal, .operator]) {
      return t.site
    }

    // Multi-token operators.
    let first = try take(if: \.isOperatorHead) ?? expected("operator")
    var last = first
    while let u = peek(), u.site.region.lowerBound == last.site.region.upperBound {
      if let next = take(if: \.isOperatorTail) {
        last = next
      } else {
        break
      }
    }
    return first.site.extended(toCover: last.site)
  }

  /// Parses an infix operator and returns the region of the file from which it has been extracted
  /// iff it binds less than or as tightly as `p`.
  private mutating func parseOptionalInfixOperator(
    notTighterThan p: PrecedenceGroup
  ) throws -> (SourceSpan, PrecedenceGroup)? {
    var backup = self
    let o = try parseOperator()
    let q = PrecedenceGroup(containing: o.text)
    if whitespaceBeforeNextToken() && ((p < q) || ((p == q) && !q.isRightAssociative)) {
      return (o, q)
    } else {
      swap(&self, &backup)
      return nil
    }
  }

  /// Parses a simple identifier.
  private mutating func parseSimpleIdentifier() -> Parsed<String> {
    if let n = take(.name) {
      return .init(n)
    } else {
      report(expected("identifier"))
      return .init("$!", at: .empty(at: position))
    }
  }

  /// Parses an instance of `T` if it can be constructed from the next token.
  private mutating func parseExpressibleByTokenTag<T: ExpressibleByTokenTag>(
    _: T.Type
  ) -> Parsed<T>? {
    if let h = peek(), let v = T(tag: h.tag) {
      _ = take()
      return .init(v, at: h.site)
    } else {
      return nil
    }
  }

  // MARK: Desugarings

  /// Returns the desugaring of a sugared conformance type.
  ///
  /// A sugared conformance type is parsed as `expression ':' expression`. If the RHS is a static
  /// call, this method modifies it in-place to add the LHS as its first argument. Otherwise, a new
  /// static call is created to apply the RHS on the LHS.
  private func desugaredConformance(
    of conformer: ExpressionIdentity, to concept: ExpressionIdentity,
    in file: inout Module.SourceContainer
  ) -> StaticCall.ID {
    if let rhs = file[concept] as? StaticCall {
      let desugared = StaticCall(
        callee: rhs.callee, arguments: [conformer] + rhs.arguments,
        site: file[concept].site)
      return file.replace(concept, for: desugared)
    } else {
      return file.insert(
        StaticCall(callee: concept, arguments: [conformer], site: file[concept].site))
    }
  }

  /// Returns `ascription` if it is a remote type expression. Otherwise, returns a remote type
  /// expression with a synthesized `let` effect.
  private func desugaredParameterAscription(
    _ ascription: ExpressionIdentity, in file: inout Module.SourceContainer
  ) -> RemoteTypeExpression.ID {
    if file.tag(of: ascription) == RemoteTypeExpression.self {
      return RemoteTypeExpression.ID(uncheckedFrom: ascription.erased)
    } else {
      let s = file[ascription].site
      let k = Parsed<AccessEffect>(.let, at: .empty(at: s.start))
      return file.insert(RemoteTypeExpression(access: k, projectee: ascription, site: s))
    }
  }

  /// Returns a tree expressing the declaration of a self-parameter with the given `effect`.
  private mutating func synthesizeSelfParameter(
    effect: Parsed<AccessEffect>, in file: inout Module.SourceContainer
  ) -> ParameterDeclaration.ID {
    let t0 = Parsed("self", at: effect.site)
    let t1 = file.insert(
      NameExpression(.init("Self", at: effect.site)))
    let t2 = file.insert(
      RemoteTypeExpression(access: effect, projectee: .init(t1), site: effect.site))
    let x3 = file.insert(
      ParameterDeclaration(
        label: t0, identifier: t0, ascription: t2,
        defaultValue: nil, lazyModifier: nil, site: effect.site))
    return x3
  }

  /// Returns a name expression with the given components.
  private func synthesizeNameExpression(
    _ components: [String], at site: SourceSpan, in file: inout Module.SourceContainer
  ) -> NameExpression.ID {
    var q: NameExpression.ID? = nil
    for n in components {
      q = file.insert(
        NameExpression(
          qualification: q.map(ExpressionIdentity.init(_:)),
          name: Parsed(Name(identifier: String(n)), at: site),
          site: site))
    }
    return q!
  }

  // MARK: Helpers

  /// Returns the start position of the next token or the current position if the stream is empty.
  private mutating func nextTokenStart() -> SourcePosition {
    peek()?.site.start ?? position
  }

  /// Returns a source span from the first position of `t` to the current position.
  private func span(from t: Token) -> SourceSpan {
    .init(t.site.start.index ..< position.index, in: tokens.source)
  }

  /// Returns a source span from `s` to the current position.
  private func span(from s: SourcePosition) -> SourceSpan {
    .init(s.index ..< position.index, in: tokens.source)
  }

  /// Returns `true` iff there is a whitespace at the current position.
  private func whitespaceAtCurrentPosition() -> Bool {
    tokens.source[position.index].isWhitespace
  }

  /// Returns `true` iff there are whitespaces immediately before and after `s`.
  private func withespacesAround(_ s: SourceSpan) -> Bool {
    let text = tokens.source

    if (s.start.index != text.startIndex) && (s.end.index != text.endIndex) {
      let before = text.index(before: s.start.index)
      return text[before].isWhitespace && text[s.end.index].isWhitespace
    } else {
      return false
    }
  }

  /// Returns `true` iff there is a whitespace before the next token.
  private mutating func whitespaceBeforeNextToken() -> Bool {
    if let n = peek() {
      return tokens.source[position.index ..< n.site.start.index].contains(where: \.isWhitespace)
    } else {
      return false
    }
  }

  /// Returns `true` iff there is a newline before the next token or the character stream is empty.
  private mutating func newlinesBeforeNextToken() -> Bool {
    if let n = peek() {
      return tokens.source[position.index ..< n.site.start.index].contains(where: \.isNewline)
    } else {
      return tokens.source.index(after: position.index) == tokens.source.endIndex
    }
  }

  /// Returns `true` iff there is a statement delimiter before the next token.
  private mutating func statementDelimiterBeforeNextToken() -> Bool {
    (newlinesBeforeNextToken() || next(is: .semicolon) || next(is: .rightBrace))
  }

  /// Returns `true` iff the next token has tag `k`, without consuming that token.
  private mutating func next(is k: Token.Tag) -> Bool {
    peek()?.tag == k
  }

  /// Returns `true` iff the next token satisfies `predicate`, without consuming that token.
  private mutating func next(satisfies predicate: (Token) -> Bool) -> Bool {
    peek().map(predicate) ?? false
  }

  /// Returns the next token without consuming it.
  private mutating func peek() -> Token? {
    if lookahead == nil { lookahead = tokens.next() }
    return lookahead
  }

  /// Consumes and returns the next token.
  private mutating func take() -> Token? {
    let next = lookahead.take() ?? tokens.next()
    position = next?.site.end ?? .init(tokens.source.endIndex, in: tokens.source)
    return next
  }

  /// Consumes and returns the next token iff it has tag `k`.
  private mutating func take(_ k: Token.Tag) -> Token? {
    next(is: k) ? take() : nil
  }

  /// Consumes and returns the next token iff it has tag `k` and no leading whitespace.
  private mutating func take(affixed k: Token.Tag) -> Token? {
    (next(is: k) && !whitespaceBeforeNextToken()) ? take() : nil
  }

  /// Consumes and returns the next token iff it satisifies `predicate`.
  private mutating func take(if predicate: (Token) -> Bool) -> Token? {
    next(satisfies: predicate) ? take() : nil
  }

  /// Consumes and returns the next token iff it is a contextual keyword withe the given value.
  private mutating func take(contextual s: String) -> Token? {
    take(if: { (t) in (t.tag == .name) && (t.text == s) })
  }

  /// Consumes and returns the next token iff its tag is in `ks`.
  private mutating func take<T: Collection<Token.Tag>>(oneOf ks: T) -> Token? {
    take(if: { (t) in ks.contains(t.tag) })
  }

  /// Discards tokens until `predicate` isn't satisfied or all the input has been consumed.
  private mutating func discard(while predicate: (Token) -> Bool) {
    while next(satisfies: predicate) { _ = take() }
  }

  /// Discards token until `predicate` is satisfied or the next token is a unbalanced delimiter.
  private mutating func recover(at predicate: (Token) -> Bool) {
    var nesting = 0
    while let t = peek(), !predicate(t) {
      switch t.tag {
      case .leftBrace:
        nesting += 1
      case .rightBrace where nesting <= 0:
        _ = take(); return
      case .rightBrace:
        nesting -= 1
      default:
         break
      }
      _ = take()
    }
  }

  /// Parses an instance of `T` in the given context.
  private mutating func entering<T>(
    _ ctx: consuming Context, _ parse: (inout Self) throws -> T
  ) rethrows -> T {
    swap(&ctx, &self.context)
    defer { swap(&ctx, &self.context) }
    return try parse(&self)
  }

  /// Parses an instance of `T` with an optional argument label.
  private mutating func labeled<T: LabeledSyntax>(
    _ parse: (inout Self) throws -> T.Value
  ) rethrows -> T {
    var backup = self

    // Can we parse a label?
    if let l = take(if: \.isArgumentLabel) {
      if take(.colon) != nil {
        let v = try parse(&self)
        return .init(label: .init(l), value: v)
      } else {
        swap(&self, &backup)
      }
    }

    // No label
    let v = try parse(&self)
    return .init(label: nil, value: v)
  }

  /// Parses a parenthesized list of labeled syntax.
  private mutating func labeledSyntaxList<T: LabeledSyntax>(
    until rightDelimiter: Token.Tag,
    _ parse: (inout Self) throws -> T.Value
  ) throws -> ([T], lastComma: Token?) {
    try commaSeparated(until: Token.hasTag(rightDelimiter)) { (me) in
      try me.labeled(parse)
    }
  }

  /// Parses an instance of `T` enclosed in `delimiters`.
  private mutating func between<T>(
    _ delimiters: (left: Token.Tag, right: Token.Tag),
    _ parse: (inout Self) throws -> T
  ) throws -> T {
    _ = try take(delimiters.left) ?? expected(delimiters.left.errorDescription)
    do {
      let contents = try parse(&self)
      if take(delimiters.right) == nil { report(expected(delimiters.right.errorDescription)) }
      return contents
    } catch let e as ParseError {
      recover(at: { _ in false })
      if take(.rightBrace) == nil { report(expected(delimiters.right.errorDescription)) }
      throw e
    }
  }

  /// Parses an instance of `T` enclosed in angle brackets.
  private mutating func inAngles<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftAngle, .rightAngle), parse)
  }

  /// Parses an instance of `T` enclosed in braces.
  private mutating func inBraces<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftBrace, .rightBrace), parse)
  }

  /// Parses an instance of `T` enclosed in brackets.
  private mutating func inBrackets<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftBracket, .rightBracket), parse)
  }

  /// Parses an instance of `T` enclosed in parentheses.
  private mutating func inParentheses<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftParenthesis, .rightParenthesis), parse)
  }

  /// Parses a list of instances of `T` separated by colons.
  private mutating func commaSeparated<T>(
    until isRightDelimiter: (Token) -> Bool, _ parse: (inout Self) throws -> T
  ) throws -> ([T], lastComma: Token?) {
    var xs: [T] = []
    var lastComma: Token? = nil
    while let head = peek(), !isRightDelimiter(head) {
      if !xs.isEmpty && (lastComma == nil) {
        report(expected("','"))
      }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in isRightDelimiter(t) || t.tag == .comma })
      }
      if let c = take(.comma) {
        lastComma = c
      }
    }
    return (xs, lastComma)
  }

  /// Parses a list of instances of `T` separated by newlines or semicolons.
  private mutating func semicolonSeparated<T>(
    until rightDelimiter: Token.Tag?, _ parse: (inout Self) throws -> T
  ) throws -> [T] {
    var xs: [T] = []
    while let head = peek() {
      discard(while: { (t) in t.tag == .semicolon })
      if head.tag == rightDelimiter { break }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in t.tag == rightDelimiter || t.tag == .semicolon })
      }
    }
    return xs
  }

  /// Parses a list of instances of `T` separated by ampersands (i.e., `&`).
  private mutating func ampersandSeparated<T>(
    until isRightDelimiter: (Token) -> Bool, _ parse: (inout Self) throws -> T
  ) throws -> [T] {
    var xs: [T] = []
    while let head = peek(), !isRightDelimiter(head) {
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in isRightDelimiter(t) || t.tag == .ampersand })
      }
      if take(.ampersand) == nil { break }
    }
    return xs
  }

  /// Returns a parse error reporting that `s` was expected at the current position.
  private func expected(_ s: String) -> ParseError {
    expected(s, at: .empty(at: position))
  }

  /// Returns a parse error reporting that `s` was expected at `site`.
  private func expected(_ s: String, at site: SourceSpan) -> ParseError {
    .init("expected \(s)", at: site)
  }

  /// Ensures there is a statement delimiter before the next token, reporting an error otherwise.
  private mutating func ensureStatementDelimiter() {
    if !statementDelimiterBeforeNextToken() {
      report(missingSemicolon(at: .empty(at: position)))
    }
  }

  /// Returns a parse error reporting a missing statement separator at `site`.
  private func missingSemicolon(at site: SourceSpan) -> ParseError {
    .init("consecutive statements on the same line must be separated by ';'", at: site)
  }

  /// Returns a parse error reporting an unexpected wildcard at `site`.
  private func unexpectedWildcard(at site: SourceSpan) -> ParseError {
    let m = """
    '_' can only appear as a pattern, as a compile-time argument, or on the left-hand side of an \
    assignment
    """
    return .init(m, at:  site)
  }

  /// Returns a parse error reporting inconsistent whitespaces surrounding an infix operator.
  private func inconsistentWhitespaces(around o: SourceSpan) -> ParseError {
    .init("infix operator '\(o.text)' requires whitespaces on both sides", at: o)
  }

  /// Returns a parse error reporting an unary operator separated from its operand.
  private func separatedUnaryOperator(_ o: SourceSpan) -> ParseError {
    .init("unary operator '\(o.text)' cannot be separated from its operand", at: o)
  }

  /// Reports `e` and returns `v`.
  private mutating func fix<T>(_ e: ParseError, with v: T) -> T {
    report(e)
    return v
  }

  /// Reports `e`.
  private mutating func report(_ e: ParseError) {
    errors.append(e)
  }

}

/// An error that occurred during parsing.
public struct ParseError: Error, CustomStringConvertible, Sendable {

  /// A description of the error that occurred.
  public let description: String

  /// The source code or source position (if empty) identified as the cause of the error.
  public let site: SourceSpan

  /// Creates an instance reporting `problem` at `site`.
  public init(_ problem: String, at site: SourceSpan) {
    self.description = problem
    self.site = site
  }

}

extension Diagnostic {

  /// Creates a diagnostic describing `e`.
  fileprivate init(_ e: ParseError) {
    self.init(.error, e.description, at: e.site)
  }

}

extension Parsed<String> {

  /// Creates an instance with the text of `t`.
  fileprivate init(_ t: Token) {
    self.init(String(t.text), at: t.site)
  }

}

extension Parsed<Name> {

  /// Creates an instance with the text of `t`.
  fileprivate init(_ t: Token) {
    self.init(Name(identifier: String(t.text)), at: t.site)
  }

}

extension Token {

  /// Returns a predicate that holds for a token iff that token's tag is in `ks`.
  fileprivate static func oneOf<T: Collection<Token.Tag>>(_ ks: T) -> (Token) -> Bool {
    { (t) in ks.contains(t.tag) }
  }

}

extension Token.Tag {

  /// Returns a description of `self` for error reporting.
  fileprivate var errorDescription: String {
    switch self {
    case .colon: "':'"
    case .leftAngle: "'<'"
    case .rightAngle: "'>'"
    case .leftBrace: "'{'"
    case .rightBrace: "'}'"
    case .leftBracket: "'['"
    case .rightBracket: "']'"
    case .leftParenthesis: "'('"
    case .rightParenthesis: "')'"
    default: "\(self)"
    }
  }

}

extension SyntaxTag {

  /// Returns `true` if a tree with this tag can occur as an enum member.
  fileprivate var isValidEnumMember: Bool {
    (self == EnumCaseDeclaration.self) || isValidStructMember
  }

  /// Returns `true` if a tree with this tag can occur as a struct member.
  fileprivate var isValidStructMember: Bool {
    switch self {
    case BindingDeclaration.self:
      return true
    case ConformanceDeclaration.self:
      return true
    case FunctionBundleDeclaration.self:
      return true
    case FunctionDeclaration.self:
      return true
    case AssociatedTypeDeclaration.self:
      return false
    default:
      return self.value is any TypeDeclaration.Type
    }
  }

  /// Returns `true` if a tree with this tag can occur as a trait member.
  fileprivate var isValidTraitMember: Bool {
    switch self {
    case AssociatedTypeDeclaration.self:
      return true
    case ConformanceDeclaration.self:
      return true
    case FunctionBundleDeclaration.self:
      return true
    case FunctionDeclaration.self:
      return true
    default:
      return false
    }
  }

}

/// A type whose instances can be created from a single token.
fileprivate protocol ExpressibleByTokenTag {

  /// Creates an instance from `tag`.
  init?(tag: Token.Tag)

}

extension AccessEffect: ExpressibleByTokenTag {

  fileprivate init?(tag: Token.Tag) {
    switch tag {
    case .auto: self = .auto
    case .inout: self = .inout
    case .let: self = .let
    case .set: self = .set
    case .sink: self = .sink
    default: return nil
    }
  }

}

extension DeclarationModifier: ExpressibleByTokenTag {

  fileprivate init?(tag: Token.Tag) {
    switch tag {
    case .static: self = .static
    case .private: self = .private
    case .internal: self = .internal
    case .public: self = .public
    default: return nil
    }
  }

}

extension OperatorNotation: ExpressibleByTokenTag {

  fileprivate init?(tag: Token.Tag) {
    switch tag {
    case .infix: self = .infix
    case .postfix: self = .postfix
    case .prefix: self = .prefix
    default: return nil
    }
  }

}

/// A sequence of annotations and modifiers prefixing a declaration.
fileprivate struct DeclarationPrologue {

  /// The prefixing annotations.
  fileprivate let annotations: [Annotation]

  /// The prefixing modifiers.
  fileprivate let modifiers: [Parsed<DeclarationModifier>]

  /// Returns `true` iff `self` contains a modifier with the given value.
  fileprivate func contains(_ m: DeclarationModifier) -> Bool {
    modifiers.contains(where: { (n) in n.value == m })
  }

  /// Returns a prologue containing no annotation and no modifier.
  fileprivate static var empty: Self {
    .init(annotations: [], modifiers: [])
  }

}
