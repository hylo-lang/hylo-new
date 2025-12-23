import BigInt
import Utilities

/// A constructor of Hylo IR.
internal struct IREmitter {

  /// The module being lowered.
  internal let module: Module.ID

  /// The program containing the module being lowered.
  internal var program: Program

  /// The current insertion context.
  private var insertionContext: InsertionContext

  /// Creates an instance inserting IR in `m`, which is a module in `p`.
  ///
  /// - Requires: `m` is typed and `p` contains the standard library.
  internal init(insertingIn m: Module.ID, of p: consuming Program) {
    self.module = m
    self.program = p
    self.insertionContext = .init()
  }

  /// Returns the resources held by this instance.
  internal consuming func release() -> Program {
    self.program
  }

  /// Inserts the IR for the top-level declarations of `self.module`.
  internal mutating func incorporateTopLevelDeclarations() {
    for d in program[module].topLevelDeclarations {
      lower(d)
    }
  }

  // MARK: Lowering

  /// Generates the IR of `d`.
  private mutating func lower(_ d: DeclarationIdentity) {
    switch program.tag(of: d) {
    case BindingDeclaration.self:
      lower(program.castUnchecked(d, to: BindingDeclaration.self))
    case ConformanceDeclaration.self:
      lower(program.castUnchecked(d, to: ConformanceDeclaration.self))
    case FunctionDeclaration.self:
      lower(program.castUnchecked(d, to: FunctionDeclaration.self))
    case StructDeclaration.self:
      lower(program.castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      lower(program.castUnchecked(d, to: TraitDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: BindingDeclaration.ID) {
    // Local binings can be stored or projected.
    if program.isLocal(d) {
      switch program[program[d].pattern].introducer.value {
      case .var, .sinklet:
        lower(storageBinding: d)
      case let i:
        unimplemented("local '\(i)' declarations")
      }
    }

    // Global bindings denote global constants computed lazily.
    else {
      unimplemented("global binding declarations")
    }
  }

  /// Generates the IR of `d`, which declares stored local bindings.
  private mutating func lower(storageBinding d: BindingDeclaration.ID) {
    assert(program.isLocal(d))
    assert(program[program[d].pattern].introducer.value == anyOf(.var, .sinklet))

    // Allocate storage for all the names declared by `d` in a single aggregate.
    let storage = lowering(d, { $0._alloca($0.program.type(assignedTo: d)) })

    // Declare all names introduced by the binding, initializing them if possible.
    let lhs = program[program[d].pattern].pattern
    if let rhs = program[d].initializer {
      lowerInitialization(bindingsIn: lhs, storedIn: storage, consuming: rhs)
    } else {
      declareBindings(in: lhs, relativeTo: storage)
    }
  }

  /// Generates IR for initializating the bindings declared in `lhs`, which refer to parts of
  /// `storage`, by consuming `rhs`.
  private mutating func lowerInitialization(
    bindingsIn lhs: PatternIdentity, storedIn storage: IRValue,
    consuming rhs: ExpressionIdentity
  ) {
    visit(lhs, nextTo: rhs, at: []) { (me, l, r, i) in
      switch me.program.tag(of: l) {
      case TuplePattern.self, VariableDeclaration.self:
        let s = me.lowering(l, { $0._subfield(storage, at: i) })
        me.lower(store: r, to: s)
        me.declareBindings(in: l, relativeTo: s)

      case WildcardLiteral.self:
        let s = me.lowered(lvalue: r)
        me.lowering(l, { _ = $0._emitDeinitialize(s) })

      default:
        me.program.unexpected(l)
      }
    }
  }

  /// Declares the bindings that are introduced in `p` and whose storage is in `s`.
  private mutating func declareBindings(in p: PatternIdentity, relativeTo s: IRValue) {
    switch program.tag(of: p) {
    case VariableDeclaration.self:
      let d = program.castUnchecked(p, to: VariableDeclaration.self)
      insertionContext.frames.top[.init(d)] = s

    default:
      program.unexpected(p)
    }
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: ConformanceDeclaration.ID) {
    // Lower explicit requirement implementations first.
    if let ms = program[d].members {
      for m in ms { lower(m) }
    }

    // TODO: Construct the function that projects the witness.
    withClearContext({ (me) in me.lowerDefinitionInClearContext(d) })
  }

  /// Generates the IR of the subscript that projects the witness declared by `d`.
  private mutating func lowerDefinitionInClearContext(_ d: ConformanceDeclaration.ID) {
    let f = demandLoweredDeclaration(of: d)
    assert(!program[module][ir: f].isDefined, "conformance already lowered")

    insertionContext.function = program[module][ir: f]
    insertionContext.point = .end(of: insertionContext.function!.addBlock())

    // TODO: Construct a witness table
    // The idea is to iterate over the implementation to figure out the shape of the concrete
    // witness object that implements the "interface" defined by the trait.
    let table = program.implementations(definedBy: d)
    var members: [IRValue] = []

    let (associatedTypes, requirements) = program.requirements(of: table.concept)
    for r in requirements {
      switch table.member(implementing: r)! {
      case .synthetic(let m, _):
        let f = demandLoweredDeclaration(syntheticImplementationOf: m, for: table.arguments)
        let n = program[module][ir: f].name
        let t = program[module][ir: f].type(uniquedIn: &program).erased
        members.append(.function(n, t))

      default:
        fatalError("not implemented")
      }
    }

    precondition(associatedTypes.isEmpty, "not implemented")

    let w = program.types.demand(
      TypeApplication(abstraction: table.concept.erased, arguments: table.arguments))

    lowering(at: program[d].introducer.site, in: .init(node: d)) { (me) in
      let x0 = me._witnesstable(type: w.erased, members: members)
      let x1 = me._access([.let], from: x0)
      me._yield(x1)
      me._end(IRAccess.self, openedBy: x1)
      me._return()
    }

    program[module][ir: f] = insertionContext.function.sink()
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: FunctionDeclaration.ID) {
    withClearContext({ (me) in me.lowerInClearContext(d) })
  }

  /// Generates the IR of `d` assuming the insertion context is clear.
  private mutating func lowerInClearContext(_ d: FunctionDeclaration.ID) {
    let f = demandLoweredDeclaration(of: d)
    assert(!program[module][ir: f].isDefined, "function already lowered")

    // Is there a body to lower?
    guard let body = program[d].body else {
      assert(!program.requiresDefinition(.init(d)), "ill-formed syntax")
      // TODO: FFI
      return
    }

    // Lower the function's definition.
    insertionContext.function = program[module][ir: f]
    insertionContext.point = .end(of: insertionContext.function!.addBlock())
    var frame = Frame()
    for (i, p) in insertionContext.function!.termParameters.enumerated() {
      if let local = p.declaration {
        frame[local] = .parameter(i)
      }
    }

    switch within(frame, { $0.lower(body: body) }) {
    case .return(let r):
      lowering(r, { $0._return() })

    case .next:
      lowering(after: body.last!, { (me) in
        // If the function returns `Void`, assume the return register is initialized to deal with
        // elided return statements.
        if me.currentFunction.isProcedure {
          let r = me.currentFunction.returnRegister!
          me._assume_state(r, initialized: true)
        }

        // Add a return statement to terminate the block.
        me._return()
      })
    }

    program[module][ir: f] = insertionContext.function.sink()
  }

  /// Generates the IR of the members in `d`.
  private mutating func lower(_ d: StructDeclaration.ID) {
    for c in program[d].conformances {
      lower(c)
    }

    for m in program[d].members {
      // Nothing to do for binding declarations.
      if program.tag(of: m) == BindingDeclaration.self { continue }
      lower(m)
    }
  }

  /// Generates the IR of the members in `d`.
  ///
  /// Requirements with no default implementation have no IR.
  private mutating func lower(_ d: TraitDeclaration.ID) {
    for m in program[d].members {
      lower(m)
    }
  }

  /// Generates the IR of `body`, which is the definition of an abstraction.
  private mutating func lower(body: [StatementIdentity]) -> ControlFlow {
    for i in body.indices {
      switch lower(body[i]) {
      case .next:
        // Just move to the next instruction.
        continue

      case let c:
        // The last statement transferred control flow; we can skip the remaining statements.
        if (i + 1) < body.count {
          report(.warning, "code will never be executed", about: body[i + 1])
        }
        return c
      }
    }

    return .next
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: StatementIdentity) -> ControlFlow {
    switch program.tag(of: s) {
    case Discard.self:
      return lower(program.castUnchecked(s, to: Discard.self))
    case Return.self:
      return lower(program.castUnchecked(s, to: Return.self))

    default:
      // If the statement is an expression, make sure it produces `Void` or `Never`.
      if let e = program.castToExpression(s) {
        let v = lowered(lvalue: e)
        lowering(s, { _ = $0._emitDeinitialize(v) })

        let t = currentFunction.result(of: v)!
        if t.type != .void {
          report(program.unusedValue(of: t.type, at: program.spanForDiagnostic(about: s)))
        }

        return .next
      }

      // Otherwise the statement should be a declaration.
      if let d = program.castToDeclaration(s) {
        lower(d)
        return .next
      } else {
        program.unexpected(s)
      }
    }
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Discard.ID) -> ControlFlow {
    let v = lowered(lvalue: program[s].value)
    lowering(s, { _ = $0._emitDeinitialize(v) })
    return .next
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Return.ID) -> ControlFlow {
    let r = currentFunction.returnRegister!

    // Store the return value into the return register.
    if let e = program[s].value {
      lower(store: e, to: r)
    } else if currentFunction.result(of: r)?.type == .void {
      lowering(s, { $0._assume_state(r, initialized: true) })
    }

    // The return instruction is emitted by the caller handling this control-flow effect.
    return .return(s)
  }

  /// Generates the IR for storing the value of `e` to `target`.
  ///
  /// `target` is the address of some uninitialized storage capable of holding an instance of `e`
  /// without any conversion (e.g., the result of an `alloca`). A `set` access is formed on that
  /// storage before the value is stored.
  private mutating func lower(store e: ExpressionIdentity, to target: IRValue) {
    switch program.tag(of: e) {
    case Call.self:
      lower(store: program.castUnchecked(e, to: Call.self), to: target)
    case IntegerLiteral.self:
      lower(store: program.castUnchecked(e, to: IntegerLiteral.self), to: target)
    case NameExpression.self:
      lower(store: program.castUnchecked(e, to: NameExpression.self), to: target)
    case SyntheticExpression.self:
      lower(store: program.castUnchecked(e, to: SyntheticExpression.self), to: target)
    case TupleLiteral.self:
      lower(store: program.castUnchecked(e, to: TupleLiteral.self), to: target)
    default:
      program.unexpected(e)
    }
  }

  /// Implements `lower(store:to:)` for call expressions.
  private mutating func lower(store e: Call.ID, to target: IRValue) {
    // Are we lowering a built-in scalar literal conversion?
    if let f = program.asBuiltinScalarLiteralConversion(program[e].callee) {
      let scalar = loweredBuiltinScalarLiteralConversion(e, applying: f)
      return lowering(e) { (me) in
        let x0 = me._subfield(target, at: [0])
        let x1 = me._access([.set], from: x0)
        me._store(scalar, to: x1)
        me._end(IRAccess.self, openedBy: x1)
      }
    }

    let returnPlace: IRValue
    let callee: LoweredCallee

    // There's at least one operand per argument and a return value. There might be more if the
    // callee accepts using parameters.
    var operands: [IRValue] = .init(minimumCapacity: program[e].arguments.count + 1)

    // If the callee is a new expression (e.g., `T.new(x)`) then `target` is passed as the first
    // argument of the underlying initializer.
    if let n = program.cast(program[e].callee, to: New.self) {
      returnPlace = lowering(e, { (me) in me._alloca(.void) })
      callee = loweredCallee(program[n].target)
      operands.append(contentsOf: callee.operands)
      operands.append(target)
    }

    // Otherwise, the callee is lowered as usual.
    else {
      returnPlace = target
      callee = loweredCallee(program[e].callee)
      operands.append(contentsOf: callee.operands)
    }

    // We compute lvalues first and query accesses next, so that mutable accesses passed down to
    // the call are not formed prematurely. This behavior supports calls to mutating methods in
    // which arguments involve (but do not retain) the receiver (e.g., `&x.modify(x.read())`).
    for a in program[e].arguments {
      operands.append(lowered(lvalue: a.value))
    }

    // At this point the callee must be a monomorphic term abstraction.
    let result = currentFunction.result(of: callee.value)!
    let abstraction = program.types.seenAsTermAbstraction(result.type)!
    let parameters = program.types[abstraction].inputs
    assert(!program.types.hasContext(result.type))
    assert(operands.count == parameters.count)

    lowering(e) { (me) in
      // Form accesses on the parameters.
      for i in 0 ..< operands.count {
        operands[i] = me._access(.init(parameters[i].access), from: operands[i])
      }
      let r = me._access([.set], from: returnPlace)

      // Do the call.
      me._apply(callee.value, to: operands, savingResultTo: r)

      // End accesses on the parameters.
      me._end(IRAccess.self, openedBy: r)
      for o in operands.reversed() {
        me._end(IRAccess.self, openedBy: o)
      }
    }
  }

  /// Implements `lower(store:to:)` for integer literals.
  private mutating func lower(store e: IntegerLiteral.ID, to target: IRValue) {
    let t = program.type(assignedTo: e)
    print(program.show(t))
  }

  /// Implements `lower(store:to:)` for name expressions.
  private mutating func lower(store e: NameExpression.ID, to target: IRValue) {
    let v = lowered(lvalue: e)
    lowering(e, { $0._emitMove([.inout, .set], v, to: target) })
  }

  /// Implements `lower(store:to:)` for synthethic expressions.
  private mutating func lower(store e: SyntheticExpression.ID, to target: IRValue) {
    lowering(e) { (me) in
      let v = me._emit(witness: me.program[e].value)
      me._emitMove([.inout, .set], v, to: target)
    }
  }

  /// Implements `lower(store:to:)` for tuple literals.
  private mutating func lower(store e: TupleLiteral.ID, to target: IRValue) {
    // Just mark the storage initialized if the literal is empty.
    if program[e].elements.isEmpty {
      lowering(e, { $0._assume_state(target, initialized: true) })
      return
    }

    // Otherwise, store each element in place.
    for (i, x) in program[e].elements.enumerated() {
      let s = lowering(x, { $0._subfield(target, at: [i]) })
      lower(store: x, to: s)
    }
  }

  /// The value and type of a lowered callee.
  private struct LoweredCallee {

    /// The lowered value of the callee (e.g., a function pointer).
    let value: IRValue

    /// A sequence of arguments notionally applied to the callee if it is partially applied.
    ///
    /// This property is assigned to the using parameters passed to `value`. Moreover, if `value`
    /// is a bound member, this property includes the receiver of that member.
    let operands: [IRValue]

    /// Returns `self` notionally applied to `a`.
    consuming func partiallyApplied(to a: IRValue) -> LoweredCallee {
      var xs = operands
      xs.append(a)
      return .init(value: value, operands: xs)
    }

  }

  /// Generates the IR for using `e` as a callee.
  ///
  /// Let `r` be the result of this method. If `e` denotes a bound member, then `r.value` is an IR
  /// function taking the bound receiver as its first (non-implicit) parameter and `r.receiver` is
  /// the receiver itself, as a lvalue.
  private mutating func loweredCallee(_ e: ExpressionIdentity) -> LoweredCallee {
    switch program.tag(of: e) {
    case NameExpression.self:
      return loweredCallee(program.castUnchecked(e, to: NameExpression.self))
    case New.self:
      unreachable("new expression should be handled in the lowering of the call")
    case SyntheticExpression.self:
      return loweredCallee(program.castUnchecked(e, to: SyntheticExpression.self))
    default:
      program.unexpected(e)
    }
  }

  /// Implements `loweredCallee(_:)` for name expressions.
  private mutating func loweredCallee(_ e: NameExpression.ID) -> LoweredCallee {
    switch program.declaration(referredToBy: e) {
    case .direct(let d):
      // The callee is referring to a function directly.
      return loweredCallee(e, referringTo: d, boundTo: nil)

    case .member(let d):
      // The callee is referring to a bound member.
      let q = lowered(lvalue: program[e].qualification!)
      return loweredCallee(e, referringTo: d, boundTo: q)

    case .inherited(let w, let m, let statically):
      // The callee referring to a member declared in extension.
      let r = statically ? nil : program[e].qualification.map({ (r) in lowered(lvalue: r) })
      let t = program.type(assignedTo: e)
      let u = program.types.lifted(t)

      return lowering(e) { (me) in
        let x0 = me._emit(witness: w)
        let x1 = me._property(m, of: x0, withType: u)
        return LoweredCallee(value: x1, operands: .init(contentsOf: r))
      }

    default:
      fatalError()
    }
  }

  /// Implements `loweredCallee(_:)` for direct declaration references.
  private mutating func loweredCallee(
    _ e: NameExpression.ID, referringTo d: DeclarationIdentity, boundTo r: IRValue?
  ) -> LoweredCallee {
    switch program.tag(of: d) {
    case FunctionDeclaration.self:
      let f = demandLoweredDeclaration(of: program.castUnchecked(d, to: FunctionDeclaration.self))
      let n = program[module][ir: f].name
      let t = program[module][ir: f].type(uniquedIn: &program).erased

      // TODO: Deal with the type of the receiver
      // Partial application tout ça tout ça
      return LoweredCallee(value: .function(n, t), operands: .init(contentsOf: r))

    default:
      program.unexpected(d)
    }
  }

  /// Implements `loweredCallee(_:)` for new expressions.
  private mutating func loweredCallee(_ e: New.ID) -> LoweredCallee {
    loweredCallee(program[e].target)
  }

  /// Implements `loweredCallee(_:)` for synthetic expressions.
  private mutating func loweredCallee(_ e: SyntheticExpression.ID) -> LoweredCallee {
    loweredCallee(program[e].value, at: program[e].site, in: program.parent(containing: e))
  }

  private mutating func loweredCallee(
    _ e: WitnessExpression, at site: SourceSpan, in scope: ScopeIdentity
  ) -> LoweredCallee {
    switch e.value {
    case .identity(let e):
      return loweredCallee(e)

    case .termApplication(let f, let a):
      let x = loweredCallee(f, at: site, in: scope)
      let y = lowering(at: site, in: scope, { (me) in me._emit(witness: a) })
      return x.partiallyApplied(to: y)

    case .typeApplication(let f, let a):
      let poly = loweredCallee(f, at: site, in: scope)
      let mono = lowering(at: site, in: scope) { (me) in me._type_apply(poly.value, to: a) }
      return LoweredCallee(value: mono, operands: poly.operands)

    default:
      fatalError("not implemented")
    }
  }

  /// Returns the type of `e` used as a callee, assuming it is the receiver of a member method if
  /// `isBoundMember` is `true`.
  private mutating func loweredCalleeType(
    of e: ExpressionIdentity, denotingReceiver isBoundMember: Bool
  ) -> AnyTypeIdentity {
    let t = program.type(assignedTo: e)
    if isBoundMember {
      // If there's a receiver, then then `e` should be a bound member function.
      assert(program.types.isLikeBoundMember(t))
      return program.types.lifted(t)
    } else {
      return t
    }
  }

  /// Generates the IR for computing the address of the value denoted by `e`.
  ///
  /// The return value is the (possibly raw) address of some storage holding the value of `e`. If
  /// `e` computes a rvalue, this value is moved into a new stack allocation.
  private mutating func lowered(lvalue e: ExpressionIdentity) -> IRValue {
    switch program.tag(of: e) {
    case NameExpression.self:
      return lowered(lvalue: program.castUnchecked(e, to: NameExpression.self))

    default:
      // Write the value computed by `e` to temporary storage.
      let t = program.type(assignedTo: e)
      let s = lowering(e) { $0._alloca(t) }
      lower(store: e, to: s)
      return s
    }
  }

  /// Implements `lower(lvalue:)` for name expressions.
  private mutating func lowered(lvalue e: NameExpression.ID) -> IRValue {
    let r = program.declaration(referredToBy: e)
    return lowering(e, { $0._emit(reference: r) })
  }

  /// Returns the value denoted by `e`, which applies a built-in constructor `f` for converting
  /// a scalar literals to a standard library type.
  private mutating func loweredBuiltinScalarLiteralConversion(
    _ e: Call.ID, applying f: Program.StandardLibraryEntity
  ) -> IRValue {
    // There must be exactly one argument.
    let source = program[e].arguments.uniqueElement!
    let target = program.type(assignedTo: e)

    // Emit the conversion.
    switch f {
    case .expressibleByIntegerLiteralInit:
      let s = program.cast(source.value, to: IntegerLiteral.self)!
      return loweredBuiltinIntegerLiteralConversion(from: s, to: target)

    default:
      program.unexpected(e)
    }
  }

  /// Returns the value denoted by `source` interpreted the contents of the integer type `target`,
  /// defined in the standard library.
  ///
  /// Standard library integer are thin wrappers around a machine type. For instance, `Int8` wraps
  /// a single `Builtin.i8` property. This method returns the value of that property converted from
  /// an integer literal.
  private mutating func loweredBuiltinIntegerLiteralConversion(
    from source: IntegerLiteral.ID, to target: AnyTypeIdentity
  ) -> IRValue {
    let value = BigInt(hyloLiteral: program[source].value)!

    switch target {
    case program.standardLibraryType(.int):
      return .integer(value, program.types.demand(MachineType.word))
    case program.standardLibraryType(.int64):
      return .integer(value, program.types.demand(MachineType.i(64)))
    default:
      program.unexpected(source)
    }
  }

  /// Returns the identity of the function lowering `d`, declaring it if needed.
  ///
  /// `d` identifies the declaration of a function, subscript, bundle, or conformance.
  private mutating func demandLoweredDeclaration<T: Declaration & Scope>(
    of d: T.ID
  ) -> IRFunction.ID {
    let name = IRFunction.Name.lowered(.init(d))
    if let i = program[module].ir.index(forKey: name) {
      return i
    }

    let ts = program.accumulatedGenericParameters(visibleFrom: .init(node: d))

    // Are we declaring a conformance?
    if program.tag(of: d) == ConformanceDeclaration.self {
      let signature = program.type(assignedTo: d)
      let witness = program.types.contextAndHead(signature)
      let output = program.types.demand(RemoteType(projectee: witness.head, access: .let))
      precondition(witness.context.isEmpty, "not implemented")

      return program[module].addFunction(
        IRFunction(
          name: name, output: .projection(output), typeParameters: ts, termParameters: []))
    }

    // Otherwise, assume `d` identifies the declaration of a function, subscript, or bundle.
    else {
      let ps = termParameters(of: .init(d))
      return program[module].addFunction(
        IRFunction(
          name: name, output: .register, typeParameters: ts, termParameters: ps))
    }
  }

  private mutating func demandLoweredDeclaration(
    syntheticImplementationOf d: DeclarationIdentity, for a: TypeArguments
  ) -> IRFunction.ID {
    let name = IRFunction.Name.synthesized(d, a)
    if let i = program[module].ir.index(forKey: name) {
      return i
    }

    let ps = termParameters(of: d)
    return program[module].addFunction(
      IRFunction(name: name, output: .register, typeParameters: [], termParameters: ps))
  }

  /// Returns the term parameters of `d`'s lowered representation, which includes `d`' explicit
  /// parameters, usings, and captures.
  ///
  /// IR functions can be generic. Type parameters are only lowered to term parameters in
  /// existentialized functions.
  private mutating func termParameters(of d: DeclarationIdentity) -> [IRParameter] {
    let abstraction = program.types.seenAsTermAbstraction(program.type(assignedTo: d))!
    var result: [IRParameter] = []

    // Parameters of memberwise initializers have no explicit declarations.
    if program.isMemberwiseInitializer(d) {
      for p in program.types[abstraction].inputs {
        let u = loweredType(addressOf: p.type)
        result.append(IRParameter(type: u, access: p.access, declaration: nil))
      }
    }

    // Other declarations have capture and parameter lists.
    else {
      let parameters = program.parametersAndCaptures(of: d)
      assert(parameters.captures.isEmpty) // TODO

      // Using parameters come first.
      for p in parameters.usings {
        let t = program.type(assignedTo: p)
        let u = loweredType(addressOf: t)

        if let b = program.cast(p, to: BindingDeclaration.self) {
          let (k, v) = program.implicit(introducedBy: b)
          result.append(IRParameter(type: u, access: .init(k), declaration: .init(v)))
        } else {
          result.append(IRParameter(type: u, access: .let, declaration: .init(p)))
        }
      }

      // If `d` is a trait requirement, the trait receiver comes next.
      if let c = program.traitRequiring(d) {
        let t = withTyper { (tp) in tp.typeOfTraitSelf(in: c) }
        let u = loweredType(addressOf: t)
        result.append(IRParameter(type: u, access: .let, declaration: nil))
      }

      // Explicit parameters come next.
      for p in parameters.explicit {
        let t = program.type(assignedTo: p, assuming: RemoteType.self)
        let u = loweredType(addressOf: program.types[t].projectee)
        result.append(IRParameter(type: u, access: program.types[t].access, declaration: .init(p)))
      }
    }

    // Return register comes last.
    if program.types[abstraction].style == .parenthesized {
      let o = loweredType(addressOf: program.types[abstraction].output)
      result.append(IRParameter(type: o, access: .set, declaration: nil))
    }

    return result
  }

  /// Returns the IR type of an address of an instance of `t`.
  private mutating func loweredType(addressOf t: AnyTypeIdentity) -> IRType {
    .addressOf(program.types.dealiased(t))
  }

  // MARK: Helpers

  /// The context in which instructions are inserted.
  private struct InsertionContext {

    /// A stack of frames keeping track of local symbols in traversed lexical scope.
    var frames = Stack()

    /// The function in which new instructions are inserted.
    var function: IRFunction? = nil

    /// Where new instructions are inserted in `function`.
    var point: InsertionPoint? = nil

    /// The region in the source code to which inserted instructions are associated.
    var anchor: Anchor? = nil

  }

  /// The local variables of a lexical scope.
  private typealias Frame = [DeclarationIdentity: IRValue]

  /// A stack of frames.
  private struct Stack {

    /// The frames in the stack, ordered from bottom to top.
    private(set) var elements: [Frame] = []

    /// Accesses the top frame.
    ///
    /// - Requires: The stack is not empty.
    var top: Frame {
      get { elements[elements.count - 1] }
      _modify { yield &elements[elements.count - 1] }
    }

    /// Accesses the IR corresponding to `d`.
    ///
    /// - Requires: For a write access, the stack is not empty.
    /// - Complexity: O(*n*) for read access where *n* is the number of frames in the stack. O(1)
    ///   for write access.
    subscript(d: DeclarationIdentity) -> IRValue? {
      get {
        for frame in elements.reversed() {
          if let operand = frame[d] { return operand }
        }
        return nil
      }
      set { top[d] = newValue }
    }

    /// Pushes `newFrame` on the stack.
    mutating func push(_ newFrame: Frame = .init()) {
      elements.append(newFrame)
    }

    /// Pops the top frame.
    ///
    /// - Requires: The stack is not empty.
    @discardableResult
    mutating func pop() -> Frame {
      return elements.removeLast()
    }

  }

  /// The description of the next action a program should execute.
  private enum ControlFlow: Equatable {

    /// Move to the next statement.
    case next

    /// Return from the current function.
    case `return`(Return.ID)

  }

  /// The function of the current insertion context, assuming it is defined.
  private var currentFunction: IRFunction {
    insertionContext.function!
  }

  /// The site with which new instruction should be associated.
  private var currentAnchor: Anchor {
    insertionContext.anchor!
  }

  /// Returns the result of calling `action` on a typer configured with `self.module`.
  private mutating func withTyper<T>(_ action: (inout Typer) -> T) -> T {
    program.withTyper(typing: module, action)
  }

  /// Returns the result of calling `action` on a copy of `self` with a cleared insertion context.
  ///
  /// Use this method to wrap the lowering of a function or subscript to save the current insertion
  /// context and restore it once `action` returns.
  private mutating func withClearContext<T>(_ action: (inout Self) -> T) -> T {
    var c = InsertionContext()
    swap(&c, &insertionContext)
    let r = action(&self)
    swap(&c, &insertionContext)
    return r
  }

  /// Returns the result of calling `action` on `self` within `f`.
  ///
  /// `f` is pushed on `self.frames` before `action` is called. When `action` returns. References
  /// to locals set by `action` are invalidated when this method returns.
  private mutating func within<T>(_ f: Frame, _ action: (inout Self) -> T) -> T {
    insertionContext.frames.push(f)
    let r = action(&self)
    insertionContext.frames.pop()
    return r
  }

  /// Returns the result of calling `action` on `self` with the insertion anchor set at `n`.
  private mutating func lowering<T: SyntaxIdentity, R>(
    _ n: T, _ action: (inout Self) -> R
  ) -> R {
    lowering(at: program[n].site, in: program.parent(containing: n), action)
  }

  /// Returns the result of calling `action` on `self` with the insertion anchor set after `n`.
  private mutating func lowering<T: SyntaxIdentity, R>(
    after n: T, _ action: (inout Self) -> R
  ) -> R {
    lowering(at: .empty(at: program[n].site.end), in: program.parent(containing: n), action)
  }

  /// Returns the result of calling `action` on `self` with the insertion context anchored at the
  /// site and scope.
  private mutating func lowering<R>(
    at site: SourceSpan, in scope: ScopeIdentity, _ action: (inout Self) -> R
  ) -> R {
    var a = Anchor(site: site, scope: scope) as Optional
    swap(&a, &insertionContext.anchor)
    let r = action(&self)
    swap(&a, &insertionContext.anchor)
    return r
  }

  /// Returns the result of calling `action` on `self` with the insertion context configured to
  /// emit new instructions before `i`, which lies in `f`.
  internal mutating func lowering<R>(
    before i: AnyInstructionIdentity, in f: inout IRFunction, _ action: (inout Self) -> R
  ) -> R {
    withClearContext { (me) in
      me.insertionContext.point = .before(i)
      me.insertionContext.anchor = f.at(i).anchor
      me.insertionContext.function = consume f
      defer { f = me.insertionContext.function.sink() }
      return action(&me)
    }
  }

  /// A callback for `visit(_:nextTo:at:calling:)`.
  private typealias PatternVisitor = (
    _ me: inout Self,
    _ pattern: PatternIdentity,
    _ scrutinee: ExpressionIdentity,
    _ path: IndexPath
  ) -> Void

  /// Calls `visitor` on each sub-pattern of `pattern` that corresponds to a sub-expressions in
  /// `scrutine`, along with the path to this sub-pattern relative to `path`.
  ///
  /// Use this method to visit a pattern side by side with a corresponding scrutinee and perform an
  /// action for each pair. Children of tuple patterns are visited in pre-order if and only if the
  /// corresponding expression is also a tuple with the same arity. Otherwise, `visitor` is called
  /// on the tuple and the sub-patterns are not visited.
  private mutating func visit(
    _ pattern: PatternIdentity, nextTo scrutinee: ExpressionIdentity, at path: IndexPath,
    calling visitor: PatternVisitor
  ) {
    switch program.tag(of: pattern) {
    case BindingPattern.self:
      let p = program.castUnchecked(pattern, to: BindingPattern.self)
      visit(p, nextTo: scrutinee, at: path, calling: visitor)
    case TuplePattern.self:
      let p = program.castUnchecked(pattern, to: TuplePattern.self)
      visit(p, nextTo: scrutinee, at: path, calling: visitor)
    default:
      visitor(&self, pattern, scrutinee, path)
    }
  }

  /// Implements `visit(_:nextTo:at:calling:)` for `BindingPattern`.
  private mutating func visit(
    _ pattern: BindingPattern.ID, nextTo scrutinee: ExpressionIdentity, at path: IndexPath,
    calling visitor: PatternVisitor
  ) {
    visit(program[pattern].pattern, nextTo: scrutinee, at: path, calling: visitor)
  }

  /// Implements `visit(_:nextTo:at:calling:)` for `TuplePattern`.
  private mutating func visit(
    _ pattern: TuplePattern.ID, nextTo scrutinee: ExpressionIdentity, at path: IndexPath,
    calling visitor: PatternVisitor
  ) {
    guard
      let s = program.cast(scrutinee, to: TupleLiteral.self),
      program[s].elements.count == program[pattern].elements.count
    else {
      return visitor(&self, .init(pattern), scrutinee, path)
    }

    for i in program[pattern].elements.indices {
      let lhs = program[pattern].elements[i]
      let rhs = program[s].elements[i]
      visit(lhs, nextTo: rhs, at: path.appending(i), calling: visitor)
    }
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// Reports a diagnostic related to `n` with the given level and message.
  private mutating func report<T: SyntaxIdentity>(_ l: Diagnostic.Level, _ m: String, about n: T) {
    report(.init(l, m, at: program.spanForDiagnostic(about: n)))
  }

  // MARK: Instruction builders

  /// Inserts `instruction` into `self.module` at `self.insertionContext.point` and returns its
  /// result the register assigned by `instruction`, if any.
  @discardableResult
  private mutating func insert<T: Instruction>(_ instruction: T) -> IRValue? {
    modify(&insertionContext.function!) { [p = insertionContext.point!] (f) in
      let i: AnyInstructionIdentity = switch p {
      case .before(let i):
        f.insert(instruction, before: i)
      case .start(let b):
        f.prepend(instruction, to: b)
      case .end(let b):
        f.append(instruction, to: b)
      }
      return f.definition(i)
    }
  }

  /// Inserts an `access` instruction.
  private mutating func _access(_ k: AccessEffectSet, from source: IRValue) -> IRValue {
    if let s = (source.register >>= currentFunction.at(_:)) as? IRAccess {
      // Reuse the source if we're just forming an access with the same capabilities.
      if s.capabilities == k { return source }
    }

    assert(currentFunction.isAddress(source))
    return insert(IRAccess(capabilities: k, source: source, anchor: currentAnchor))!
  }

  /// Inserts a `alloca` instruction.
  ///
  /// - Parameters:
  ///   - storageType: The type of the values for which the storage is allocated.
  ///   - alignment: The alignment of the allocated storage, which defaults to the preferred
  ///     alignment of `storageType`.
  ///   - inEntry: `true` iff the instruction should be inserted at the start of the current
  ///     functions' entry rather than at the current insertion point.
  internal mutating func _alloca(
    _ type: AnyTypeIdentity, alignment: IRAlignment? = nil, inEntry: Bool = true
  ) -> IRValue {
    let t = program.types.dealiased(type)
    let a = alignment ?? .align(of: t)
    let i = IRAlloca(storageType: t, alignment: a, anchor: currentAnchor)

    if inEntry {
      return modify(&insertionContext.function!) { (f) in
        let i = f.prepend(i, to: f.entry!)
        return f.definition(i)!
      }
    } else {
      return insert(i)!
    }
  }

  /// Inserts a `apply` instruction.
  internal mutating func _apply(
    _ callee: IRValue,
    to arguments: [IRValue],
    savingResultTo result: IRValue
  ) {
    let s = IRApply(
      callee: callee, arguments: arguments, result: result,
      anchor: currentAnchor)
    insert(s)
  }

  /// Inserts a `apply_builtin` instruction.
  internal mutating func _apply_builtin(
    _ callee: BuiltinFunction, to arguments: [IRValue]
  ) -> IRValue {
    let f = BuiltinFunction.trap.type(uniquingTypesWith: &program.types)
    assert(program.types[f].inputs.count == arguments.count)

    let s = IRApplyBuiltin(
      callee: callee, returnTypeOfCallee: program.types[f].output, arguments: arguments,
      anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `assume_state` instruction.
  internal mutating func _assume_state(_ s: IRValue, initialized: Bool) {
    insert(IRAssumeState(storage: s, initialized: initialized, anchor: currentAnchor))
  }

  /// Inserts an `end` instruction.
  internal mutating func _end<T: IRRegionEntry>(_: T.Type, openedBy start: IRValue) {
    assert(currentFunction.at(start.register!) is T)
    insert(T.End(start: start, anchor: currentAnchor))
  }

  /// Inserts a `load` instruction.
  internal mutating func _load(_ source: IRValue) -> IRValue {
    assert(currentFunction.isAddress(source))
    return insert(IRLoad(source: source, anchor: currentAnchor))!
  }

  /// Inserts a `move` instruction.
  internal mutating func _move(_ source: IRValue, to target: IRValue) {
    assert(currentFunction.isAddress(source))
    assert(currentFunction.isAddress(target))
    insert(IRMove(source: source, target: target, anchor: currentAnchor))
  }

  /// Inserts a `project` instruction.
  internal mutating func _project(with callee: IRValue, _ arguments: [IRValue]) -> IRValue {
    guard
      let t = currentFunction.result(of: callee),
      let a = program.types.cast(t.type, to: Arrow.self),
      let o = program.types.cast(program.types[a].output, to: RemoteType.self)
    else { badOperand() }

    let s = IRProject(
      callee: callee, arguments: arguments,
      projectee: program.types[o].projectee,
      access: program.types[o].access,
      anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `property` instruction.
  internal mutating func _property(
    _ property: DeclarationIdentity,
    of receiver: IRValue,
    withType propertyType: AnyTypeIdentity
  ) -> IRValue {
    let s = IRProperty(
      receiver: receiver, property: property, propertyType: propertyType,
      anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `return` instruction.
  internal mutating func _return() {
    insert(IRReturn(anchor: currentAnchor))
  }

  /// Inserts a `store` instruction.
  internal mutating func _store(_ value: IRValue, to target: IRValue) {
    insert(IRStore(value: value, target: target, anchor: currentAnchor))
  }

  /// Inserts a `subfield` instruction.
  internal mutating func _subfield(_ base: IRValue, at path: IndexPath) -> IRValue {
    // The instruction is equivalent to the identity if the path is empty.
    if path.isEmpty { return base }

    let (root, _) = currentFunction.result(of: base) ?? badOperand()
    let typeOfSubfield = withTyper({ (tp) in tp.field(of: root, at: path) })
    let s = IRSubfield(
      base: base, path: path, typeOfSubfield: typeOfSubfield!,
      anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `type_apply` instruction.
  internal mutating func _type_apply(
    _ callee: IRValue, to arguments: TypeArguments
  ) -> IRValue {
    // The callee must have a universal type.
    guard
      let t = currentFunction.result(of: callee),
      let u = program.types.cast(t.type, to: UniversalType.self)
    else { badOperand() }

    // Compute the type substitution.
    let a = program.types.dealiased(arguments)
    let typeOfApplication = program.types.application(of: u, to: a)
    assert(!program.types.hasContext(typeOfApplication), "illegal partial type application")

    let s = IRTypeApply(
      callee: callee, arguments: arguments, typeOfApplication: typeOfApplication,
      anchor: currentAnchor)
    return insert(s)!
  }

  /// Insertes an `unreachable` instruction.
  internal mutating func _unreachable() {
    insert(IRUnreachable(anchor: currentAnchor))
  }

  /// Inserts a `witnesstable` instruction.
  internal mutating func _witnesstable(
    type: AnyTypeIdentity, members: [IRValue]
  ) -> IRValue {
    insert(IRWitnessTable(witnessType: type, members: members, anchor: currentAnchor))!
  }

  /// Inserts a `return` instruction.
  internal mutating func _yield(_ projectee: IRValue) {
    insert(IRYield(projectee: projectee, anchor: currentAnchor))
  }

  /// Generates the IR of `r`, which computes a lvalue.
  private mutating func _emit(reference r: DeclarationReference) -> IRValue {
    switch r {
    case .direct(let d):
      return _emit(referenceTo: d)
    default:
      fatalError()
    }
  }

  /// Generates the IR for referring directly to `d`.
  private mutating func _emit(referenceTo d: DeclarationIdentity) -> IRValue {
    // Is `d` a local declaration?
    if let s = insertionContext.frames[d] {
      return s
    }

    assert(!program.isLocal(d), "unhandled local declaration")

    if let c = program.cast(d, to: ConformanceDeclaration.self) {
      return _emit(referenceTo: c)
    }

    program.unexpected(d)
  }

  /// Generates the IR for referring directly to `d`.
  private mutating func _emit(referenceTo d: ConformanceDeclaration.ID) -> IRValue {
    let t = program.type(assignedTo: d)
    precondition(!program.types.hasContext(t), "unsupported direct reference to non-simple given")

    let u = program.types.demand(RemoteType(projectee: t, access: .let)).erased
    let f = program.types.demand(Arrow(style: .bracketed, inputs: [], output: u)).erased
    let g = IRValue.function(.lowered(.init(d)), f)
    return _project(with: g, [])
  }

  /// Generates the IR for computing the lvalue referred to by `w`.
  private mutating func _emit(witness w: WitnessExpression) -> IRValue {
    switch w.value {
    case .identity(let e):
      return lowered(lvalue: e)

    case .reference(let d):
      return _emit(referenceTo: d)

    case .typeApplication(let f, let a):
      let x = _emit(witness: f)
      return _type_apply(x, to: a)

    default:
      fatalError()
    }
  }

  /// Generates the IR for deinitializing `source`.
  internal mutating func _emitDeinitialize(_ source: IRValue) -> Bool {
    let (typeOfSource, _) = currentFunction.result(of: source) ?? badOperand()

    // Nothing to do for machine types.
    if program.types.tag(of: typeOfSource) == MachineType.self {
      _assume_state(source, initialized: false)
      return true
    }

    // Other types need a conformance to `Hylo.Deinitializable`.
    guard let w = conformanceWitness(of: typeOfSource, is: .deinitializable) else {
      _ = _apply_builtin(.trap, to: [])
      return false
    }

    // Does the conformance have any operational semantics.
    if program.isTransitivelySyntheticConformance(w) {
      _assume_state(source, initialized: false)
      return true
    }

    let deinitializable = _emit(witness: w)
    let member = program.standardLibraryDeclaration(.deinitializableDeinit)
    let t0 = program.types.demand(
      Arrow(inputs: [.init(access: .sink, type: typeOfSource)], output: .void))

    let x0 = _alloca(.void)
    let x1 = _access([.sink], from: source)
    let x2 = _access([.set], from: x0)
    let x3 = _property(member, of: deinitializable, withType: t0.erased)
    let x4 = _access([.let], from: x3)

    _apply(x4, to: [x1], savingResultTo: x2)

    _end(IRAccess.self, openedBy: x4)
    _end(IRAccess.self, openedBy: x2)
    _end(IRAccess.self, openedBy: x1)

    return true
  }

  /// Generates the IR for move-initializing or move-assigning `target` with `source`.
  ///
  /// `source` computes the address of some value and `target` computes the address of some storage
  /// capable of holding that value without any conversion.
  ///
  /// The value of `semantics` defines the type of move to emit:
  /// - `[.set]` emits move-initialization, assuming `target` is uninitialized.
  /// - `[.inout]` emits move-assignment, assuming `target` is initialized.
  /// - `[.inout, .set]` emits a `move` instruction that is desugared to during definite state
  ///   analysis by move-assignment if `target` is initialized or move-initialization otherwise.
  ///
  /// If the value in `source` is instance of a machine type, it is copied byte for byte into
  /// `target`. Otherwise, the value is moved using the conformance of its type to `Hylo.Movable`.
  /// An error is reported at the current anchor if no such conformance can be resolved in the
  /// scope of that anchor and a call to `Builtin.trap` is generated.
  private mutating func _emitMove(
    _ semantics: AccessEffectSet, _ source: IRValue, to target: IRValue
  ) {
    if let k = semantics.uniqueElement {
      let (typeOfSource, _) = currentFunction.result(of: source) ?? badOperand()
      _emitMove(k, source, of: typeOfSource, to: target)
    } else {
      assert(semantics == [.set, .inout])
      _move(source, to: target)
    }
  }

  /// Generates the IR for move-initializing or move-assigning `target` with `value`.
  ///
  /// `source` computes the address of some value instance of `typeOfSource` and `target` computes
  /// the address of some storage capable of holding that value without any conversion.
  ///
  /// The value of `semantics` defines the type of move to emit:
  /// - `.set` emits move-initialization, assuming `target` is uninitialized.
  /// - `.inout` emits move-assignment, assuming `target` is initialized.
  ///
  /// If the value in `source` is instance of a machine type, it is copied byte for byte into
  /// `target`. Otherwise, the value is moved using the conformance of its type to `Hylo.Movable`.
  /// An error is reported at the current anchor if no such conformance can be resolved in the
  /// scope of that anchor and a call to `Builtin.trap` is generated.
  private mutating func _emitMove(
    _ k: AccessEffect, _ source: IRValue, of typeOfSource: AnyTypeIdentity, to target: IRValue
  ) {
    assert((k == .set) || (k == .inout))
    assert(currentFunction.isAddress(source))
    assert(currentFunction.isAddress(target))

    // Machine types are always copied.
    if program.types.tag(of: typeOfSource) == MachineType.self {
      _emitMoveBuiltin(source, to: target)
      return
    }

    // Other types require a conformance to `Hylo.Movable`.
    guard let movable = _emitWitness(of: typeOfSource, is: .movable) else {
      return
    }

    let member = program.variant(k, of: program.standardLibraryDeclaration(.movableTakeValue))!
    let t0 = program.types.demand(
      Arrow(
        inputs: [.init(access: k, type: typeOfSource), .init(access: .sink, type: typeOfSource)],
        output: .void))

    let x0 = _alloca(.void)
    let x1 = _access([k], from: target)
    let x2 = _access([.sink], from: source)
    let x3 = _access([.set], from: x0)
    let x4 = _property(.init(member), of: movable, withType: t0.erased)

    _apply(x4, to: [x1, x2], savingResultTo: x3)

    _end(IRAccess.self, openedBy: x3)
    _end(IRAccess.self, openedBy: x2)
    _end(IRAccess.self, openedBy: x1)
  }

  /// Inserts IR for move-initializing or assigning `target` with `value`, which is an instance of
  /// a built-in machine type.
  private mutating func _emitMoveBuiltin(_ value: IRValue, to target: IRValue) {
    let x0 = _access([.set], from: target)
    let x1 = _access([.sink], from: value)
    let x2 = _load(x1)
    _store(x2, to: x0)
    _end(IRAccess.self, openedBy: x1)
    _end(IRAccess.self, openedBy: x0)
  }

  /// Inserts IR (if any) for getting the address of a  witness of `t`'s conformance to `p` at the
  /// current insertion point, or a trap instruction if such a conformance cannot be derived.
  private mutating func _emitWitness(
    of t: AnyTypeIdentity, is p: Program.StandardLibraryEntity
  ) -> IRValue? {
    guard let w = conformanceWitness(of: t, is: p) else {
      _ = _apply_builtin(.trap, to: [])
      return nil
    }

    if program.isTransitivelySyntheticConformance(w) {
      fatalError()
    } else {
      return _emit(witness: w)
    }
  }

  private mutating func conformanceWitness(
    of t: AnyTypeIdentity, is p: Program.StandardLibraryEntity
  ) -> WitnessExpression? {
    let goal = program.typeOfWitness(of: t, is: p)
    let scopeOfUse = insertionContext.anchor!.scope
    let candidates = withTyper { (tp) in
      tp.summon(goal, in: scopeOfUse)
    }

    // Fail if there isn't a unique candidate.
    if let pick = candidates.uniqueElement {
      return pick.witness
    } else {
      report(program.noUniqueGivenInstance(of: goal, found: candidates, at: currentAnchor.site))
      return nil
    }
  }

}

extension Program {

  /// The term parameters of a callable abstraction.
  fileprivate struct ParametersAndCaptures {

    /// The explicit term parameters of the abstraction.
    let explicit: [ParameterDeclaration.ID]

    /// The term parameters of the abstraction's context clause.
    let usings: [DeclarationIdentity]

    /// The declarations of the symbols occurring free in the abstraction.
    let captures: [DeclarationIdentity]

  }

  /// Returns the term parameters of `d`, which identifies a callable abstraction.
  fileprivate func parametersAndCaptures(of d: DeclarationIdentity) -> ParametersAndCaptures {
    switch tag(of: d) {
    case FunctionDeclaration.self:
      return parametersAndCaptures(of: castUnchecked(d, to: FunctionDeclaration.self))
    case VariantDeclaration.self:
      return parametersAndCaptures(of: castUnchecked(d, to: VariantDeclaration.self))
    default:
      unexpected(d)
    }
  }

  /// Returns the term parameters of `d`.
  fileprivate func parametersAndCaptures(of d: FunctionDeclaration.ID) -> ParametersAndCaptures {
    .init(explicit: self[d].parameters, usings: self[d].contextParameters.usings, captures: [])
  }

  /// Returns the term parameters of `d`.
  fileprivate func parametersAndCaptures(of d: VariantDeclaration.ID) -> ParametersAndCaptures {
    let p = parent(containing: d, as: FunctionBundleDeclaration.self)!
    return .init(
      explicit: self[p].parameters, usings: self[p].contextParameters.usings, captures: [])
  }

  /// Returns generic parameters captured by `s` and the scopes semantically containing `s`.
  fileprivate func accumulatedGenericParameters(
    visibleFrom s: ScopeIdentity
  ) -> [GenericParameter.ID] {
    var accumulator: [GenericParameter.ID] = []
    var p = s
    while let n = p.node {
      // If `n` is a declaration that forms a scope and that has a universal type, then we assume
      // these parameters are introduced by `n`.
      if isDeclaration(n) {
        let t = type(assignedTo: n)
        let u = types.select(t, \Metatype.inhabitant) ?? t
        accumulator.append(contentsOf: types.contextAndHead(u).context.parameters.reversed())
      }
      p = parent(containing: n)
    }
    return accumulator.reversed()
  }

}

/// Indicates an invalid IR operand.
fileprivate func badOperand(file: StaticString = #file, line: UInt = #line) -> Never {
  preconditionFailure("bad operand", file: file, line: line)
}
