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
    case EnumCaseDeclaration.self:
      lower(program.castUnchecked(d, to: EnumCaseDeclaration.self))
    case EnumDeclaration.self:
      lower(program.castUnchecked(d, to: EnumDeclaration.self))
    case FunctionDeclaration.self:
      lower(program.castUnchecked(d, to: FunctionDeclaration.self))
    case ImportDeclaration.self:
      break
    case StructDeclaration.self:
      lower(program.castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      lower(program.castUnchecked(d, to: TraitDeclaration.self))
    case VariableDeclaration.self:
      break
    default:
      program.unexpected(d)
    }
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: BindingDeclaration.ID) {
    // Local binings can be stored or projected.
    if program.isLocal(d) {
      if program[program[d].pattern].introducesStoredBindings {
        lower(storedBinding: d)
      } else {
        lower(remoteBinding: d)
      }
    }

    // Global bindings denote global constants computed lazily.
    else {
      lower(globalBinding: d)
    }
  }

  /// Generates the IR of `d`, which declares stored local bindings.
  private mutating func lower(storedBinding d: BindingDeclaration.ID) {
    let p = program[d].pattern
    assert(program.isLocal(d))
    assert(program[p].introducer.value == anyOf(.var, .sinklet))

    // Allocate storage for all the names declared by `d` in a single aggregate.
    let storage = lowering(d, { $0._alloca($0.program.type(assignedTo: d)) })
    let lhs = program[p].pattern

    // Declare all names introduced by the binding, initializing them if possible.
    if let rhs = program[d].initializer {
      lowerInitialization(bindingsIn: lhs, storedIn: storage, consuming: rhs)
    } else {
      declareBindings(in: lhs, relativeTo: storage)
    }
  }

  /// Generates the IR of `d`, which declares remote local bindings.
  private mutating func lower(remoteBinding d: BindingDeclaration.ID) {
    let p = program[d].pattern
    assert(program.isLocal(d))
    assert(program[p].introducer.value == anyOf(.let, .set, .inout))

    // Is there an initializer?
    if let rhs = program[d].initializer {
      let request = AccessEffect(program[p].introducer.value)
      let x0 = lowered(lvalue: rhs)
      let x1 = lowering(rhs, { (me) in  me._access([request], from: x0) })
      declareBindings(in: program[p].pattern, relativeTo: x1)
    }

    // Otherwise report an error and introduce each declared symbol as a poison value.
    else {
      report(program.missingBindingInitializer(d))
      program.forEachVariable(introducedBy: d) { (v, _) in
        let t = program.type(assignedTo: v)
        associate(.init(v), with: .poison(.lowered(t, isAddress: true)))
      }
    }
  }

  /// Generates the IR of `d`, which declares remote local bindings.
  private mutating func lower(globalBinding d: BindingDeclaration.ID) {
    if let rhs = program[d].initializer {
      // Retrieve the declaration of the global's initializer.
      let g = demandLoweredDeclaration(variable: d)
      var initializer = program[d.module].ir[g.initializer].move()
      defer { program[d.module].ir[g.initializer].take(definition: initializer) }

      // Emit the definition of the global's initializer.
      let lhs = program[program[d].pattern].pattern
      initializer = withClearContext { (me) in
        me.insertionContext.function = initializer
        me.insertionContext.point = .end(of: me.insertionContext.function!.addBlock())
        me.lowerInitialization(bindingsIn: lhs, storedIn: .parameter(0), consuming: rhs)
        me.lowering(rhs, { $0._return() })
        return me.insertionContext.function.sink()
      }
    } else {
      report(program.missingBindingInitializer(d))
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
      associate(.init(d), with: s)

    case TuplePattern.self:
      let t = program.castUnchecked(p, to: TuplePattern.self)
      for (i, e) in program[t].elements.enumerated() {
        let x = lowering(e, { $0._subfield(s, at: [i]) })
        declareBindings(in: e, relativeTo: x)
      }

    case WildcardLiteral.self:
      break

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
    let f = demandLoweredDeclaration(function: d)
    assert(!program[module].ir[f].isDefined, "conformance already lowered")

    insertionContext.function = program[module].ir[f]
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
        let v = functionReference(referringTo: f)
        members.append(v)

      default:
        unimplemented("custom implementation")
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

    program[module].ir[f] = insertionContext.function.sink()
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: EnumCaseDeclaration.ID) {
    withClearContext({ (me) in me.lowerInClearContext(d) })
  }

  /// Generates the IR of `d` assuming the insertion context is clear.
  private mutating func lowerInClearContext(_ d: EnumCaseDeclaration.ID) {
    let f = demandLoweredDeclaration(constructor: d)
    assert(!program[module].ir[f].isDefined, "function already lowered")
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: EnumDeclaration.ID) {
    for c in program[d].conformances {
      lower(c)
    }

    for m in program[d].members {
      if let b = program.cast(m, to: BindingDeclaration.self) {
        // We can assume the member is static, otherwise typer would have complained.
        lower(globalBinding: b)
      } else {
        lower(m)
      }
    }
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: FunctionDeclaration.ID) {
    withClearContext({ (me) in me.lowerInClearContext(d) })
  }

  /// Generates the IR of `d` assuming the insertion context is clear.
  private mutating func lowerInClearContext(_ d: FunctionDeclaration.ID) {
    let f = demandLoweredDeclaration(function: d)
    assert(!program[module].ir[f].isDefined, "function already lowered")

    // Is there a body to lower?
    guard let body = program[d].body else {
      assert(!program.requiresDefinition(.init(d)), "ill-formed syntax")
      // TODO: FFI
      return
    }

    // Lower the function's definition.
    insertionContext.function = program[module].ir[f]
    insertionContext.point = .end(of: insertionContext.function!.addBlock())
    for (i, p) in insertionContext.function!.termParameters.enumerated() {
      let v = IRValue.parameter(i)

      // Configure the base frame with the function's parameters.
      if let local = p.declaration {
        insertionContext.function!.associate(local, with: v)
      }

      // Assume `p` is initialized if it's a `set` parameter other than the return register
      // accessing the storage of a trivially initializable object (e.g., an empty struct).
      if (p.access == .set) && (v != insertionContext.function!.returnRegister) {
        let t = insertionContext.function!.resolved(p.type)!.type
        if program.isTriviallyInitializable(t, in: .init(node: d)) {
          lowering(at: program[d].introducer.site, in: .init(node: d)) { (me) in
            me._assume_state(v, initialized: true)
          }
        }
      }
    }

    switch lower(body: body) {
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

    program[module].ir[f] = insertionContext.function.sink()
  }

  /// Generates the IR of the members in `d`.
  private mutating func lower(_ d: StructDeclaration.ID) {
    for c in program[d].conformances {
      lower(c)
    }

    for m in program[d].members {
      if let b = program.cast(m, to: BindingDeclaration.self) {
        // Nothing to do for non-static binding declarations.
        if program.isStatic(b) { lower(globalBinding: b) }
      } else {
        lower(m)
      }
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
    case Assignment.self:
      return lower(program.castUnchecked(s, to: Assignment.self))
    case Block.self:
      return lower(program.castUnchecked(s, to: Block.self))
    case Discard.self:
      return lower(program.castUnchecked(s, to: Discard.self))
    case If.self:
      return lowerAsStatement(program.castUnchecked(s, to: If.self))
    case Return.self:
      return lower(program.castUnchecked(s, to: Return.self))
    case Yield.self:
      return lower(program.castUnchecked(s, to: Yield.self))

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
  private mutating func lower(_ s: Assignment.ID) -> ControlFlow {
    // The LHS should be an inout expression.
    guard let target = program.read(program[s].lhs.erased, \InoutExpression.lvalue) else {
      report(program.assignmentNotMarkedMutating(s))
      return .next
    }

    // If the LHS does not occur in the RHS, we can build the RHS in place.
    if let n = program.cast(target, to: NameExpression.self) {
      if case .direct(let d) = program.declaration(referredToBy: n) {
        if !program.occurs(referenceTo: d, in: program[s].rhs) {
          let target = lowered(lvalue: target)
          lower(store: program[s].rhs, to: target)
          return .next
        }
      }
    }

    // Otherwise, the right-hand side stored to a temporary and then moved to the LHS.
    let t = program.type(assignedTo: program[s].rhs)
    let r = lowering(program[s].rhs, { $0._alloca(t) })
    lower(store: program[s].rhs, to: r)
    let l = lowered(lvalue: program[s].lhs)
    lowering(program[s].rhs, { $0._emitMove([.inout, .set], r, to: l) })

    return .next
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Block.ID) -> ControlFlow {
    lower(body: program[s].statements)
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Discard.ID) -> ControlFlow {
    let v = lowered(lvalue: program[s].value)
    lowering(program[s].value, { _ = $0._emitDeinitialize(v) })
    return .next
  }

  /// Generates the IR of `s` lowered as a statement.
  @discardableResult
  private mutating func lowerAsStatement(_ s: If.ID) -> ControlFlow {
    let onFailure = insertionContext.function!.addBlock()
    let tail = insertionContext.function!.addBlock()

    // Lower the conditions and the success branch.
    for c in program[s].conditions {
      insertionContext.point = .end(of: lowerCondition(c, onFailure: onFailure))
    }

    if lower(program[s].success) == .next {
      lowering(after: program[s].success, { $0._br(tail) })
    }

    // Lower the failure branch.
    insertionContext.point = .end(of: onFailure)
    if lower(StatementIdentity(uncheckedFrom: program[s].failure.erased)) == .next {
      lowering(after: program[s].failure, { $0._br(tail) })
    }

    // If neither branch returns control-flow (e.g., both branches return), then the tail won't
    // have any predecessor and will be removed during dead code elimination.
    insertionContext.point = .end(of: tail)
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

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Yield.ID) -> ControlFlow {
    let v = lowered(lvalue: program[s].value)
    lowering(s, { $0._yield(v) })
    return .next
  }

  /// Generates the IR for storing the value of `e` to `target`.
  ///
  /// `target` is the address of some uninitialized storage capable of holding an instance of `e`
  /// without any conversion (e.g., the result of an `alloca`). A `set` access is formed on that
  /// storage before the value is stored.
  private mutating func lower(store e: ExpressionIdentity, to target: IRValue) {
    switch program.tag(of: e) {
    case BooleanLiteral.self:
      lower(store: program.castUnchecked(e, to: BooleanLiteral.self), to: target)
    case Call.self:
      lower(store: program.castUnchecked(e, to: Call.self), to: target)
    case Conversion.self:
      lower(store: program.castUnchecked(e, to: Conversion.self), to: target)
    case If.self:
      lower(store: program.castUnchecked(e, to: If.self), to: target)
    case InoutExpression.self:
      lower(store: program.castUnchecked(e, to: InoutExpression.self), to: target)
    case IntegerLiteral.self:
      lower(store: program.castUnchecked(e, to: IntegerLiteral.self), to: target)
    case NameExpression.self:
      lower(store: program.castUnchecked(e, to: NameExpression.self), to: target)
    case SyntheticExpression.self:
      lower(store: program.castUnchecked(e, to: SyntheticExpression.self), to: target)
    case TupleLiteral.self:
      lower(store: program.castUnchecked(e, to: TupleLiteral.self), to: target)
    case TupleMember.self:
      lower(store: program.castUnchecked(e, to: TupleMember.self), to: target)
    default:
      program.unexpected(e)
    }
  }

  /// Implements `lower(store:to:)` for Booleanliterals.
  private mutating func lower(store e: BooleanLiteral.ID, to target: IRValue) {
    let v = IRValue.integer(
      program[e].value ? 1 : 0,
      program.types.demand(MachineType.i(1)))
    lowering(e, { $0._emitInitialize(target, to: v) })
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

    // Are we lowering a built-in call.
    if let f = program.asBuiltinFunction(program[e].callee) {
      return lowering(e) { (me) in
        let x0 = me._lower(builtin: f, appliedTo: me.program[e].arguments)
        let x1 = me._access([.set], from: target)
        me._store(x0, to: x1)
        me._end(IRAccess.self, openedBy: x1)
      }
    }

    // Otherwise, the callee is lowered as usual.
    let f = loweredCallee(program[e].callee, writingTo: target)

    // There's at least one operand per argument and a return value. There might be more if the
    // callee accepts using parameters.
    var operands = Array(f.arguments)
    operands.reserveCapacity(operands.count + program[e].arguments.count + 1)

    // We compute lvalues first and query accesses next, so that mutable accesses passed down to
    // the call are not formed prematurely. This behavior supports calls to mutating methods in
    // which arguments involve (but do not retain) the receiver (e.g., `&x.modify(x.read())`).
    for a in program[e].arguments {
      operands.append(lowered(lvalue: a.value))
    }

    // At this point the callee must be a monomorphic term abstraction.
    let t = currentFunction.result(of: f.value)!
    let u = program.types.seenAsTermAbstraction(t.type)!
    let parameters = program.types[u].inputs
    assert(!program.types.hasContext(t.type))
    assert(operands.count == parameters.count)

    lowering(e) { (me) in
      // Form accesses on the parameters.
      for i in 0 ..< operands.count {
        operands[i] = me._access(.init(parameters[i].access), from: operands[i])
      }
      let r = me._access([.set], from: f.result)

      // Do the call.
      me._apply(f.value, to: operands, savingResultTo: r)

      // End accesses on the parameters.
      me._end(IRAccess.self, openedBy: r)
      for o in operands.reversed() {
        me._end(IRAccess.self, openedBy: o)
      }
    }
  }

  /// Implements `lower(store:to:)` for conversion expressions.
  private mutating func lower(store e: Conversion.ID, to target: IRValue) {
    let lhs = program.type(assignedTo: program[e].source)
    let rhs = program.type(assignedTo: e)

    // Trivial if the conversion does not involve any change of representation.
    if let s = program.types.unifiable(lhs, rhs) {
      assert(s.isEmpty)
      lower(store: program[e].source, to: target)
    }

    // Otherwise, the semantics of the conversion depends on its direction.
    else {
      unimplemented(program.format("conversion from '%T' to '%T'", [lhs, rhs]))
    }
  }

  /// Implements `lower(store:to:)` for conditional expressions.
  private mutating func lower(store e: If.ID, to target: IRValue) {
    let onFailure = insertionContext.function!.addBlock()
    let tail = insertionContext.function!.addBlock()

    // Typer should have guaranteed that the expression is single-expresion bodied.
    let (e0, e1) = program.branches(of: e)!
    for c in program[e].conditions {
      insertionContext.point = .end(of: lowerCondition(c, onFailure: onFailure))
    }
    lower(store: e0, to: target)
    lowering(after: e0, { $0._br(tail) })

    insertionContext.point = .end(of: onFailure)
    lower(store: e1, to: target)
    lowering(after: e1, { $0._br(tail) })

    insertionContext.point = .end(of: tail)
  }

  /// Generates the IR for using `n` as a condition of a test jumping to `onFailure` if the
  /// condition does not hold or the return value if it does.
  private mutating func lowerCondition(
    _ n: ConditionIdentity, onFailure: IRBlock.ID
  ) -> IRBlock.ID {
    let onSuccess = insertionContext.function!.addBlock()

    // Is the condition a simple Boolean expression?
    if let e = program.castToExpression(n) {
      let w = lowered(lvalue: e)
      lowering(e) { (me) in
        let b = me._loadWrappedBuiltin(w)
        me._condbr(b, onSuccess, onFailure)
      }
      insertionContext.point = .end(of: onSuccess)
    }

    // Is the condition applying pattern matching?
    else if program.tag(of: n) == BindingDeclaration.self {
      fatalError("not implemented")
    }

    // Something's wrong.
    else {
      program.unexpected(n)
    }

    return onSuccess
  }

  /// Implements `lower(store:to:)` for integer literals.
  private mutating func lower(store e: InoutExpression.ID, to target: IRValue) {
    let m = "'&' may only be used to assign a variable, form a binding, or pass an argument"
    report(.init(.error, m, at: program[e].marker.site))
  }

  /// Implements `lower(store:to:)` for integer literals.
  private mutating func lower(store e: IntegerLiteral.ID, to target: IRValue) {
    unreachable()
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

  /// Implements `lower(store:to:)` for tuple member selections.
  private mutating func lower(store e: TupleMember.ID, to target: IRValue) {
    let v = lowered(lvalue: e)
    lowering(e, { $0._emitMove([.inout, .set], v, to: target) })
  }

  /// The notional value of a lowered callee as a possibly partially applied IR function together
  /// with the place in which its result is written.
  private struct LoweredCallee {

    /// The IR values in the representation of `self.`
    private let properties: [IRValue]

    /// Creates an instance with the given properties.
    init<T: Sequence<IRValue>>(value: IRValue, arguments: T, result: IRValue) {
      var vs: [IRValue] = .init(minimumCapacity: arguments.underestimatedCount + 2)
      vs.append(value)
      vs.append(result)
      vs.append(contentsOf: arguments)
      self.properties = vs
    }

    /// The lowered value of the callee (e.g., a function pointer).
    var value: IRValue {
      properties[0]
    }

    /// The place in which the result of the call is written.
    var result: IRValue {
      properties[1]
    }

    /// A sequence of arguments notionally applied to the callee if it is partially applied.
    ///
    /// This property is assigned to the using parameters passed to `value`. Moreover, if `value`
    /// is a bound member, this property includes the receiver of that member.
    var arguments: ArraySlice<IRValue> {
      properties[2...]
    }

    /// Returns `self` notionally applied to `a`.
    consuming func partiallyApplied(to a: IRValue) -> LoweredCallee {
      .init(value: value, arguments: Array(arguments, terminatedBy: a), result: result)
    }

  }

  /// Generates the IR for using `e` as a callee in a call writing to `r`.
  ///
  /// Let `f` be the result of this method. `f.value` is the IR function implementing the callee
  /// expressed by `e`. This function may be partially applied if `e` is a bound member and/or if
  /// it involves implicit arguments, in which case `f.arguments` contain these arguments.
  ///
  /// `r` is the place in which the result of the call is written. If `e` denotes the application
  ///  of a new expression, then `r` is appended to `f.arguments` and `f.result` is a new alloca.
  ///  Otherwise, `f.result` is assigned to `r`.
  private mutating func loweredCallee(
    _ e: ExpressionIdentity, writingTo r: IRValue
  ) -> LoweredCallee {
    switch program.tag(of: e) {
    case NameExpression.self:
      return loweredCallee(program.castUnchecked(e, to: NameExpression.self), writingTo: r)
    case New.self:
      return loweredCallee(program.castUnchecked(e, to: New.self), writingTo: r)
    case StaticCall.self:
      return loweredCallee(program.castUnchecked(e, to: StaticCall.self), writingTo: r)
    case SyntheticExpression.self:
      return loweredCallee(program.castUnchecked(e, to: SyntheticExpression.self), writingTo: r)
    default:
      program.unexpected(e)
    }
  }

  /// Implements `loweredCallee(_:writingTo)` for name expressions.
  private mutating func loweredCallee(
    _ e: NameExpression.ID, writingTo result: IRValue
  ) -> LoweredCallee {
    switch program.declaration(referredToBy: e) {
    case .builtin:
      // Calls to built-in functions should be handled elsewhere.
      fatalError("cannot create reference to built-in function")

    case .direct(let d):
      // The callee refers to a function directly.
      return loweredCallee(e, referringTo: d, boundTo: nil, writingTo: result)

    case .member(let d):
      // The callee refers to a bound member.
      let q = lowered(lvalue: program[e].qualification!)
      return loweredCallee(e, referringTo: d, boundTo: q, writingTo: result)

    case .inherited(let w, let m, let statically):
      // The callee refers to a member declared in extension.
      let s = statically ? nil : program[e].qualification.map({ (s) in lowered(lvalue: s) })
      let t = program.type(assignedTo: e)
      let u = program.types.lifted(t)

      return lowering(e) { (me) in
        let x0 = me._emit(witness: w)
        let x1 = me._property(m, of: x0, withType: u)
        return LoweredCallee(value: x1, arguments: Array(contentsOf: s), result: result)
      }

    default:
      program.unexpected(e)
    }
  }

  /// Implements `loweredCallee(_:writingTo)` for direct declaration references.
  private mutating func loweredCallee(
    _ e: NameExpression.ID, referringTo d: DeclarationIdentity, boundTo receiver: IRValue?,
    writingTo result: IRValue
  ) -> LoweredCallee {
    switch program.tag(of: d) {
    case FunctionDeclaration.self:
      let f = demandLoweredDeclaration(
        function: program.castUnchecked(d, to: FunctionDeclaration.self))
      return loweredCallee(referringTo: f, boundTo: receiver, writingTo: result)

    case EnumCaseDeclaration.self:
      let f = demandLoweredDeclaration(
        constructor: program.castUnchecked(d, to: EnumCaseDeclaration.self))
      return loweredCallee(referringTo: f, boundTo: receiver, writingTo: result)

    default:
      program.unexpected(d)
    }
  }

  /// Returns the IR of `function` used in a call writing to `result`, partially applied to
  /// `receiver` iff the latter is defined.
  private mutating func loweredCallee(
    referringTo function: IRFunction.ID, boundTo receiver: IRValue?, writingTo result: IRValue
  ) -> LoweredCallee {
    // TODO: Deal with the type of the receiver
    // Partial application tout ça tout ça
    let v = functionReference(referringTo: function)
    return LoweredCallee(value: v, arguments: Array(contentsOf: receiver), result: result)
  }

  /// Implements `loweredCallee(_:writingTo)` for new expressions.
  private mutating func loweredCallee(
    _ e: New.ID, writingTo result: IRValue
  ) -> LoweredCallee {
    // When the callee is a new expression (e.g., `T.new(x)`), then `result` is passed as the first
    // argument of the underlying initializer.
    let r = lowering(e, { (me) in me._alloca(.void) })
    let f = loweredCallee(program[e].target, writingTo: result)
    return LoweredCallee(
      value: f.value, arguments: Array(f.arguments, terminatedBy: f.result), result: r)
  }

  /// Implements `loweredCallee(_:writingTo)` for static calls.
  private mutating func loweredCallee(
    _ e: StaticCall.ID, writingTo result: IRValue
  ) -> LoweredCallee {
    let poly = loweredCallee(program[e].callee, writingTo: result)

    // Gather the type parameters of the callee; there should be as many as arguments.
    let f = currentFunction.result(of: poly.value)!.type
    let (context, _) = program.types.contextAndHead(f)

    // Construct a mapping from type parameter to its argument.
    let a = TypeArguments(
      mapping: context.parameters,
      to: program[e].arguments.map({ (x) in
        let t = program.type(assignedTo: x, assuming: Metatype.self)
        return program.types[t].inhabitant
      }))

    let mono = lowering(e, { (me) in me._type_apply(poly.value, to: a) })
    return LoweredCallee(value: mono, arguments: poly.arguments, result: poly.result)
  }

  /// Implements `loweredCallee(_:writingTo)` for synthetic expressions.
  private mutating func loweredCallee(
    _ e: SyntheticExpression.ID, writingTo result: IRValue
  ) -> LoweredCallee {
    loweredCallee(
      program[e].value, writingTo: result,
      at: program[e].site,
      in: program.parent(containing: e))
  }

  /// Implements `loweredCallee(_:writingTo)` for witness expressions.
  private mutating func loweredCallee(
    _ e: WitnessExpression, writingTo result: IRValue,
    at site: SourceSpan, in scope: ScopeIdentity
  ) -> LoweredCallee {
    switch e.value {
    case .identity(let e):
      return loweredCallee(e, writingTo: result)

    case .termApplication(let f, let a):
      let x = loweredCallee(f, writingTo: result, at: site, in: scope)
      let y = lowering(at: site, in: scope, { (me) in me._emit(witness: a) })
      return x.partiallyApplied(to: y)

    case .typeApplication(let f, let a):
      let poly = loweredCallee(f, writingTo: result, at: site, in: scope)
      let mono = lowering(at: site, in: scope, { (me) in me._type_apply(poly.value, to: a) })
      return LoweredCallee(value: mono, arguments: poly.arguments, result: poly.result)

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

  /// Generates the IR for loading the value denoted by `e` into a register.
  private mutating func lowered(rvalue e: ExpressionIdentity) -> IRValue {
    let v = lowered(lvalue: e)
    return lowering(e) { (me) in
      let x = me._access([.sink], from: v)
      let y = me._load(v)
      me._end(IRAccess.self, openedBy: x)
      return y
    }
  }

  /// Generates the IR for loading the result of `function` applied to `arguments` into a register.
  private mutating func _lower(
    builtin function: BuiltinFunction, appliedTo arguments: [LabeledExpression],
  ) -> IRValue {
    let xs = arguments.map({ (a) in lowered(rvalue: a.value) })
    return _apply_builtin(function, to: xs)
  }

  /// Generates the IR for computing the address of the value denoted by `e`.
  ///
  /// The return value is the (possibly raw) address of some storage holding the value of `e`. If
  /// `e` computes a rvalue, this value is moved into a new stack allocation.
  private mutating func lowered(lvalue e: ExpressionIdentity) -> IRValue {
    switch program.tag(of: e) {
    case Conversion.self:
      return lowered(lvalue: program.castUnchecked(e, to: Conversion.self))
    case InoutExpression.self:
      return lowered(lvalue: program.castUnchecked(e, to: InoutExpression.self))
    case NameExpression.self:
      return lowered(lvalue: program.castUnchecked(e, to: NameExpression.self))
    case TupleMember.self:
      return lowered(lvalue: program.castUnchecked(e, to: TupleMember.self))

    default:
      // Write the value computed by `e` to temporary storage.
      let t = program.type(assignedTo: e)
      let s = lowering(e) { $0._alloca(t) }
      lower(store: e, to: s)
      return s
    }
  }

  /// Implements `lower(lvalue:)` for explicit conversions.
  private mutating func lowered(lvalue e: Conversion.ID) -> IRValue {
    // Is there any conversion required?
    let t = program.types.dealiased(program.type(assignedTo: e))
    let u = program.types.dealiased(program.type(assignedTo: program[e].source))
    if t == u {
      return lowered(lvalue: program[e].source)
    }

    unimplemented("conversions involving change of representation")
  }

  /// Implements `lower(lvalue:)` for inout expressions.
  private mutating func lowered(lvalue e: InoutExpression.ID) -> IRValue {
    lowered(lvalue: program[e].lvalue)
  }

  /// Implements `lower(lvalue:)` for name expressions.
  private mutating func lowered(lvalue e: NameExpression.ID) -> IRValue {
    switch program.declaration(referredToBy: e) {
    case .direct(let d):
      return lowering(e, { (me) in me._emit(referenceTo: d) })

    case .member(let d):
      // Emit the receiver.
      let q = lowered(lvalue: program[e].qualification!)

      // Is `d` a stored property of a type whose layout is visible?
      if let i = storedPropertyIndex(of: d, in: program.parent(containing: e)) {
        return lowering(e, { $0._subfield(q, at: [i]) })
      } else {
        let t = program.type(assignedTo: e)
        return lowering(e, { $0._property(d, of: q, withType: t) })
      }

    default:
      fatalError()
    }
  }

  /// Implements `lower(lvalue:)` for tuple member selections.
  private mutating func lowered(lvalue e: TupleMember.ID) -> IRValue {
    let v = lowered(lvalue: program[e].parent)
    let i = program[e].member.value
    return lowering(e, { $0._subfield(v, at: [i]) })
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
    case program.standardLibraryType(.int32):
      return .integer(value, program.types.demand(MachineType.i(32)))
    case program.standardLibraryType(.int64):
      return .integer(value, program.types.demand(MachineType.i(64)))
    default:
      program.unexpected(source)
    }
  }

  /// Returns the identity of the function lowering `d`, declaring it if necessary.
  ///
  /// `d` identifies the declaration of a function, subscript, bundle, or conformance.
  private mutating func demandLoweredDeclaration<T: Declaration & Scope>(
    function d: T.ID
  ) -> IRFunction.ID {
    let name = IRFunction.Name.lowered(.init(d))
    if let i = program[module].ir.functions.index(forKey: name) {
      return i
    }

    let ts = program.withTyper(typing: d.module) { (tp) in
      tp.accumulatedGenericParameters(visibleFrom: .init(node: d))
    }

    // Are we declaring a conformance?
    if program.tag(of: d) == ConformanceDeclaration.self {
      let witness = program.types.contextAndHead(program.type(assignedTo: d))

      assert(witness.context.parameters.allSatisfy(ts.contains(_:)))
      let ps = witness.context.usings.map { (u) in
        IRParameter(type: .lowered(u, isAddress: true), access: .let, declaration: nil)
      }

      return program[module].ir.addFunction(
        IRFunction(
          name: name, output: .remote(.let, witness.head), typeParameters: ts, termParameters: ps))
    }

    // Otherwise, assume `d` identifies the declaration of a function, subscript, or bundle.
    else {
      let (ps, o) = prototype(of: .init(d))
      return program[module].ir.addFunction(
        IRFunction(name: name, output: o, typeParameters: ts, termParameters: ps))
    }
  }

  /// Returns the identity of the function lowering `d`, declaring it if necessary.
  private mutating func demandLoweredDeclaration(
    syntheticImplementationOf d: DeclarationIdentity, for a: TypeArguments
  ) -> IRFunction.ID {
    let name = IRFunction.Name.synthesized(d, a)
    if let i = program[module].ir.functions.index(forKey: name) {
      return i
    }

    let (ps, o) = prototype(of: d)
    return program[module].ir.addFunction(
      IRFunction(name: name, output: o, typeParameters: [], termParameters: ps))
  }

  /// Returns the identity of the constructor lowering `d`, declaring it if necessary.
  private mutating func demandLoweredDeclaration(
    constructor d: EnumCaseDeclaration.ID
  ) -> IRFunction.ID {
    let name = IRFunction.Name.lowered(.init(d))
    if let i = program[module].ir.functions.index(forKey: name) {
      return i
    }

    let ts = program.withTyper(typing: d.module) { (tp) in
      tp.accumulatedGenericParameters(visibleFrom: .init(node: d))
    }

    // The constructor takes each associated value as a sink parameter.
    var ps: [IRParameter] = .init(minimumCapacity: program[d].parameters.count + 1)
    for p in program[d].parameters {
      let t = program.type(assignedTo: p, assuming: RemoteType.self)
      let u = loweredType(addressOf: program.types[t].projectee)
      ps.append(IRParameter(type: u, access: program.types[t].access, declaration: .init(p)))
    }

    // The constructor returns an instance of the containing enum.
    let e = program.type(assignedTo: program.parent(containing: d).node!, assuming: Metatype.self)
    let o = loweredType(addressOf: program.types[e].inhabitant)
    ps.append(.init(type: o, access: .set, declaration: nil))

    return program[module].ir.addFunction(
      IRFunction(
        name: name, output: .indirect, typeParameters: ts, termParameters: ps))
  }

  /// Returns the IR variable lowering the global binding `d`, declaring it if necessary.
  private mutating func demandLoweredDeclaration(
    variable d: BindingDeclaration.ID
  ) -> IRGlobal {
    let name = IRGlobal.Name.lowered(d)
    if let g = program[module].ir.variables[name] {
      return g
    }

    let p = program[d].pattern
    assert(!program.isLocal(d))
    assert(program[p].introducer.value == .let)

    // Declare the global's initializer.
    let t = program.types.dealiased(program.type(assignedTo: d))
    let o = IRParameter(type: .lowered(t, isAddress: true), access: .set, declaration: nil)
    let i = IRFunction(
      name: .initializer(d), output: .indirect, typeParameters: [], termParameters: [o])
    let f = program[module].ir.addFunction(i)

    // Declare the global itself.
    let g = IRGlobal(name: name, storageType: t, alignment: .preferred, initializer: f)
    program[module].ir.addGlobal(g)
    return g
  }

  /// Returns the term parameters and return type of `d`'s lowered representation.
  ///
  /// `d` declares a function or bundle. The result includes `d`' explicit parameters, usings, and
  /// captures, in that order. Type parameters are not included. Those are only lowered to term
  /// parameters in existentialized functions.
  private mutating func prototype(
    of d: DeclarationIdentity
  ) -> ([IRParameter], IRFunction.Output) {
    let abstraction = program.types.seenAsTermAbstraction(program.type(assignedTo: d))!
    var result: [IRParameter] = []

    precondition(program.tag(of: d) == FunctionDeclaration.self, "TODO")

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
      precondition(parameters.captures.isEmpty, "TODO")

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
        let t = program.withTyper(typing: c.module, { (tp) in tp.typeOfTraitSelf(in: c) })
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

    if program.types[abstraction].style == .parenthesized {
      // Return register comes last.
      let o = loweredType(addressOf: program.types[abstraction].output)
      result.append(IRParameter(type: o, access: .set, declaration: nil))
      return (result, .indirect)
    } else {
      let o = IRFunction.Output.remote(
        program.types[abstraction].effect, program.types[abstraction].output)
      return (result, o)
    }
  }

  /// Returns the IR type of an address of an instance of `t`.
  private mutating func loweredType(addressOf t: AnyTypeIdentity) -> IRType {
    .addressOf(program.types.dealiased(t))
  }

  // MARK: Context

  /// The context in which instructions are inserted.
  private struct InsertionContext {

    /// The function in which new instructions are inserted.
    var function: IRFunction? = nil

    /// Where new instructions are inserted in `function`.
    var point: InsertionPoint? = nil

    /// The region in the source code to which inserted instructions are associated.
    var anchor: Anchor? = nil

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

  /// The site with which new instructions should be associated.
  private var currentAnchor: Anchor {
    insertionContext.anchor!
  }

  /// Associates the entity declared by `d` with the value `v` in the current function.
  public mutating func associate(_ d: DeclarationIdentity, with v: IRValue) {
    insertionContext.function!.associate(d, with: v)
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

  /// Returns the result of calling `action` on `self` with the given insertion anchor.
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
  /// emit new instructions at `p` in `f`, anchoring them to `a`.
  internal mutating func lowering<R>(
    _ p: InsertionPoint, anchoredTo a: Anchor, in f: inout IRFunction, _ action: (inout Self) -> R
  ) -> R {
    withClearContext { (me) in
      me.insertionContext.point = p
      me.insertionContext.anchor = a
      me.insertionContext.function = consume f
      defer { f = me.insertionContext.function.sink() }
      return action(&me)
    }
  }

  /// Returns the result of calling `action` on `self` with the insertion context configured to
  /// emit new instructions before `i`, which is in `f`.
  internal mutating func lowering<R>(
    before i: AnyInstructionIdentity, in f: inout IRFunction, _ action: (inout Self) -> R
  ) -> R {
    let a = f.at(i).anchor
    return lowering(.before(i), anchoredTo: a, in: &f, action)
  }

  /// Returns the result of calling `action` on `self` with the insertion context configured to
  /// emit new instructions after `i`, which is in `f`.
  internal mutating func lowering<R>(
    after i: AnyInstructionIdentity, in f: inout IRFunction, _ action: (inout Self) -> R
  ) -> R {
    let a = f.at(i).anchor
    if let j = f.instruction(after: i) {
      return lowering(.before(j), anchoredTo: a, in: &f, action)
    } else {
      return lowering(.end(of: f.block(defining: i)), anchoredTo: a, in: &f, action)
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

  /// If `d` declares a stored property of in a type whose layout is visible from `scopeOfUse`,
  /// returns that property's index. Otherwise, returns `nil`.
  ///
  /// The index of a stored property is used in instances of `IndexPath` to represent the location
  /// of a part relative to the location of a whole. For example, if `S` is a struct with two
  /// stored properties `x` and `y`, declared in that order, the index of `y` is 1.
  ///
  /// The layout of a type if visible if its declaration is in the same module as`scopeOfUse` or
  /// if its declaration is marked `inlineable`.
  private mutating func storedPropertyIndex(
    of d: DeclarationIdentity, in scopeOfUse: ScopeIdentity
  ) -> Int? {
    guard
      let v = program.cast(d, to: VariableDeclaration.self),
      let p = program.parent(containing: v, as: StructDeclaration.self),
      program.isInlineable(p, in: scopeOfUse)
    else { return nil }

    let properties = program.storedProperties(of: p)
    return properties.firstIndex(of: v)
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
  internal mutating func insert<T: Instruction>(_ instruction: T) -> IRValue? {
    modify(&insertionContext.function!) { [p = insertionContext.point!] (f) in
      let i: AnyInstructionIdentity = switch p {
      case .before(let i):
        f.insert(instruction, before: i)
      case .after(let i):
        f.insert(instruction, after: i)
      case .start(let b):
        f.prepend(instruction, to: b)
      case .end(let b):
        f.append(instruction, to: b)
      }
      return f.definition(i)
    }
  }

  /// Inserts an `access` instruction.
  internal mutating func _access(_ k: AccessEffectSet, from source: IRValue) -> IRValue {
    assert(currentFunction.isAddress(source))
    return insert(IRAccess(capabilities: k, source: source, anchor: currentAnchor))!
  }

  /// Inserts an `alloca` instruction.
  ///
  /// - Parameters:
  ///   - storage: The type of the values for which the storage is allocated.
  ///   - alignment: The alignment of the allocated storage, which defaults to the preferred
  ///     alignment of `storage` on the compilation target.
  ///   - inEntry: `true` iff the instruction should be inserted at the start of the current
  ///     functions' entry rather than at the current insertion point.
  internal mutating func _alloca(
    _ storage: AnyTypeIdentity, alignment: IRAlignment = .preferred, inEntry: Bool = false
  ) -> IRValue {
    let t = program.types.dealiased(storage)
    let s = IRAlloca(storage: t, alignment: alignment, anchor: currentAnchor)

    if inEntry {
      return modify(&insertionContext.function!) { (f) in
        let i = f.prepend(s, to: f.entry!)
        return f.definition(i)!
      }
    } else {
      return insert(s)!
    }
  }

  /// Inserts an `allocx` instruction.
  internal mutating func _allocx(
    _ type: IRValue, as storage: AnyTypeIdentity, alignment: IRAlignment = .preferred
  ) -> IRValue {
    let t = program.types.dealiased(storage)
    let s = IRAllocx(storage: t, witness: type, alignment: alignment, anchor: currentAnchor)
    return insert(s)!
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
    let f = callee.type(uniquingTypesWith: &program.types)
    assert(program.types[f].inputs.count == arguments.count)

    let s = IRApplyBuiltin(
      callee: callee, returnTypeOfCallee: program.types[f].output, arguments: arguments,
      anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `assume_state` instruction.
  internal mutating func _assume_state(_ s: IRValue, initialized: Bool) {
    let x = _access([initialized ? .set : .sink], from: s)
    insert(IRAssumeState(storage: x, initialized: initialized, anchor: currentAnchor))
    _end(IRAccess.self, openedBy: x)
  }

  /// Inserts a `br` instruction.
  internal mutating func _br(_ target: IRBlock.ID) {
    insert(IRBranch(target: target, anchor: currentAnchor))
  }

  /// Inserts a `condbr` instruction.
  internal mutating func _condbr(
    _ condition: IRValue, _ onSuccess: IRBlock.ID, _ onFailure: IRBlock.ID
  ) {
    let s = IRConditionalBranch(
      condition: condition, onSuccess: onSuccess, onFailure: onFailure,
      anchor: currentAnchor)
    insert(s)
  }

  /// Inserts an `end` instruction.
  internal mutating func _end<T: IRRegionEntry>(_: T.Type, openedBy start: IRValue) {
    assert(currentFunction.at(start.register!) is T)
    insert(T.End(start: start, anchor: currentAnchor))
  }

  /// Inserts a `global_access` instruction.
  internal mutating func _global_access(_ source: IRGlobal) -> IRValue {
    insert(IRGlobalAccess(source: source, anchor: currentAnchor))!
  }

  /// Inserts a `load` instruction.
  internal mutating func _load(_ source: IRValue) -> IRValue {
    assert(currentFunction.isAddress(source))
    return insert(IRLoad(source: source, anchor: currentAnchor))!
  }

  /// Inserts a `memcpy` instruction.
  internal mutating func _memory_copy(_ source: IRValue, to target: IRValue) {
    assert(currentFunction.isAddress(source))
    assert(currentFunction.isAddress(target))
    insert(IRMemoryCopy(source: source, target: target, anchor: currentAnchor))
  }

  /// Inserts a `move` instruction.
  internal mutating func _move(_ source: IRValue, to target: IRValue) {
    assert(currentFunction.isAddress(source))
    assert(currentFunction.isAddress(target))
    insert(IRMove(source: source, target: target, anchor: currentAnchor))
  }

  /// Inserts a `palce_cast` instruction.
  internal mutating func _place_cast<T: TypeIdentity>(_ source: IRValue, as target: T) -> IRValue {
    let t = program.types.dealiased(target.erased)
    let s = IRPlaceCast(source: source, target: t, anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `project` instruction.
  internal mutating func _project(with callee: IRValue, _ arguments: [IRValue]) -> IRValue {
    guard
      let t = currentFunction.result(of: callee),
      let a = program.types.cast(t.type, to: Arrow.self)
    else { badOperand() }

    let s = IRProject(
      callee: callee, arguments: arguments,
      projectee: program.types[a].output,
      access: program.types[a].effect,
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
    let typeOfSubfield = program.withTyper(typing: module) { (tp) in
      tp.field(of: root, at: path)
    }

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

  /// Inserts a `type_witness` application.
  internal mutating func _type_witness(
    _ callee: UniversalType.ID, _ arguments: [IRValue]
  ) -> IRValue {
    assert(program.types[callee].parameters.count == arguments.count)
    let t = program.types.demand(TypeWitness())
    let s = IRTypeWitness(
      constructor: callee, arguments: arguments, typeOfApplication: t,
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

  // MARK: Helpers

  /// Inserts the IR for extracting the built-in value stored in an instance of `Hylo.Bool`.
  private mutating func _loadWrappedBuiltin(_ wrapper: IRValue) -> IRValue {
    let x0 = _subfield(wrapper, at: [0])
    let x1 = _access([.let], from: x0)
    let x2 = _load(x1)
    _end(IRAccess.self, openedBy: x1)
    return x2
  }

  /// Generates the IR for referring directly to `d`.
  ///
  /// If `applyNullary` is `true` and `d` refers to a nullary conformance declaration, the result
  /// is an application of corresponding lowered function.
  private mutating func _emit(
    referenceTo d: DeclarationIdentity, applyingNullary applyNullary: Bool = true
  ) -> IRValue {
    // Is `d` already inserted into the local symbol table?
    if let s = currentFunction.binding(d) {
      return s
    }

    // Should `d` be hoisted?
    else if program.isLocal(d) {
      // Is `d` referring to a local variable that is not yet in scope?
      if let v = program.cast(d, to: VariableDeclaration.self) {
        // The only way to get here is if `v` has not been defined yet.
        let s = insertionContext.anchor!.site
        let t = program.type(assignedTo: v)
        report(.init(.error, "use of '\(program[v].identifier)' before its declaration", at: s))
        return .poison(.lowered(t, isAddress: true))
      }

      fatalError()
    }

    // Is `d` a conformance declaration?
    else if let c = program.cast(d, to: ConformanceDeclaration.self) {
      return _emit(referenceTo: c, applyingNullary: applyNullary)
    }

    // Is `d` a type declaration?
    else if program.isTypeDeclaration(d) {
      let t = program.type(assignedTo: d, assuming: Metatype.self)
      let u = program.types.dealiased(program.types[t].inhabitant)
      return .type(u, program.types.demand(TypeWitness()))
    }

    switch program.tag(of: d) {
    case ConformanceDeclaration.self:
      let e = program.castUnchecked(d, to: ConformanceDeclaration.self)
      return _emit(referenceTo: e, applyingNullary: applyNullary)

    case VariableDeclaration.self:
      // Since `d` wasn't in the local symbol table, we can assume it's a global symbol.
      return _emit(referenceToGlobal: program.castUnchecked(d, to: VariableDeclaration.self))

    default:
      program.unexpected(d)
    }
  }

  /// Generates the IR for referring directly to `d`.
  ///
  /// If `applyNullary` is `true` and `d` refers to a nullary conformance declaration, the result
  /// is an application of corresponding lowered function.
  private mutating func _emit(
    referenceTo d: ConformanceDeclaration.ID, applyingNullary applyNullary: Bool
  ) -> IRValue {
    let f = demandLoweredDeclaration(function: d)
    let v = functionReference(referringTo: f)

    if program[module].ir[f].termParameters.isEmpty && applyNullary {
      return _project(with: v, [])
    } else {
      return v
    }
  }

  /// Generates the IR for referring to the global binding `d`.
  private mutating func _emit(
    referenceToGlobal d: VariableDeclaration.ID
  ) -> IRValue {
    assert(!program.isLocal(d))
    let b = program.bindingDeclaration(containing: d)!

    // Find the path from the root of the allocation to the variable being referred to. Note that
    // we can assume the recursive visit to be short since as global binding declarations usually
    // do not involve deep binding patterns.
    var p: IndexPath? = nil
    program.forEachVariable(introducedBy: b) { (v, q) in
      if d == v { p = q }
    }

    let g = demandLoweredDeclaration(variable: b)
    let x = _global_access(g)
    return _subfield(x, at: p!)
  }

  /// Generates the IR for computing the lvalue referred to by `witness`.
  ///
  /// If `applyNullary` is `true` and `witness` either refers to or is a type application of a
  /// nullary conformance declaration, the corresponding lowered function is applied without any
  /// argument in the result.
  private mutating func _emit(
    witness: WitnessExpression, applyingNullary applyNullary: Bool = true
  ) -> IRValue {
    switch witness.value {
    case .identity(let e):
      return lowered(lvalue: e)

    case .reference(let d):
      return _emit(referenceTo: d, applyingNullary: applyNullary)

    case .termApplication(let f, let a):
      var stack = [_emit(witness: a)]
      var abstraction: WitnessExpression? = f
      while let w = abstraction.take() {
        if case .termApplication(let g, let b) = w.value {
          stack.append(_emit(witness: b))
          abstraction = g
        } else {
          stack.append(_emit(witness: w, applyingNullary: false))
        }
      }

      let (callee, arguments) = stack.reversed().headAndTail!
      return _project(with: callee, Array(arguments))

    case .typeApplication(let f, let a):
      let x = _emit(witness: f, applyingNullary: applyNullary)
      return _type_apply(x, to: a)

    default:
      fatalError()
    }
  }

  /// Generates the IR for casting `source` to a place of type `target`.
  internal mutating func _emitCast(
    _ source: IRValue, to target: AnyTypeIdentity
  ) -> IRValue {
    if target[.hasGenericParameter] {
      return _place_cast(source, as: target)
    } else {
      assert(target == currentFunction.result(of: source)!.type)
      return source
    }
  }

  // Generates the IR for storing `source` into `target`.
  internal mutating func _emitInitialize(_ target: IRValue, to source: IRValue) {
    let x0 = _access([.set], from: target)
    _store(source, to: x0)
    _end(IRAccess.self, openedBy: x0)
  }

  /// Generates the IR for deinitializing `source` and returns `true` iff `source` can be
  /// deinitialized. Otherwise, inserts a trap and returns `false`.
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
  internal mutating func _emitMove(
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
    guard let w = conformanceWitness(of: typeOfSource, is: .movable) else {
      _ = _apply_builtin(.trap, to: [])
      return
    }

    // Does the conformance have any operational semantics.
    if program.isTransitivelySyntheticConformance(w) {
      let x0 = _access([.sink], from: source)
      let x1 = _access([.set], from: target)
      _memory_copy(x0, to: x1)
      _end(IRAccess.self, openedBy: x1)
      _end(IRAccess.self, openedBy: x0)
      return
    }

    let movable = _emit(witness: w)
    let member = program.variant(k, of: program.standardLibraryDeclaration(.movableTakeValue))!
    let t0 = program.types.demand(
      Arrow(
        inputs: [.init(access: k, type: typeOfSource), .init(access: .sink, type: typeOfSource)],
        output: .void))

    let x0 = _alloca(.void)
    let x1 = _access([.sink], from: source)
    let x2 = _access([k], from: target)
    let x3 = _access([.set], from: x0)
    let x4 = _property(.init(member), of: movable, withType: t0.erased)

    _apply(x4, to: [x2, x1], savingResultTo: x3)

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

  private mutating func conformanceWitness(
    of t: AnyTypeIdentity, is p: Program.StandardLibraryEntity
  ) -> WitnessExpression? {
    let goal = program.typeOfWitness(of: t, is: p)
    let scopeOfUse = insertionContext.anchor!.scope
    let candidates = program.withTyper(typing: module) { (tp) in
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

  /// Generates the IR for accessing a run-time witness of `t`, caching results into `witnesses`.
  ///
  /// `witnesses` is a table mapping a type to a place containing a corresponding witness. It is
  /// updated whenever generating a witness for `t` requires new IR. Instructions for allocating
  /// and initializing storage for new witnesses are emitted in the entry of the current function
  /// whereas the return value is always an access emitted at the current insertion point.
  internal mutating func _emitTypeWitness(
    of t: AnyTypeIdentity, reusing witnesses: inout [AnyTypeIdentity: IRValue]
  ) -> IRValue {
    // Trivial if the witness is already available.
    if let a = witnesses[t] {
      return _access([.let], from: a)
    }

    // Instructions for allocating/initializing the witness are emitted in the entry.
    var p: InsertionPoint? = .some(.start(of: currentFunction.entry!))
    swap(&insertionContext.point, &p)

    let ps = program.types.parameters(freeIn: t)

    // If `t` has no free type parameter, then we can just use a constant value.
    if ps.isEmpty {
      let u = program.types.demand(TypeWitness())
      let a = _alloca(u.erased)
      _emitInitialize(a, to: .type(t.erased, u))
      witnesses[t.erased] = a

      swap(&insertionContext.point, &p)
      return _access([.let], from: a)
    }

    // Otherwise, we have to construct a new type witness.
    else {
      let u = program.types.demand(UniversalType(parameters: Array(ps), head: t))
      let v = ps.map({ (p) in _emitTypeWitness(of: p.erased, reusing: &witnesses) })
      let a = _type_witness(u, v)
      witnesses[t.erased] = a

      swap(&insertionContext.point, &p)
      return _access([.let], from: a)
    }
  }

  /// Returns a reference to the given lowered function.
  internal mutating func functionReference(referringTo f: IRFunction.ID) -> IRValue {
    let n = program[module].ir[f].name
    let s = program[module].ir[f].signature()
    let t = program.types.demand(s)
    return .function(n, t)
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

}

/// Indicates an invalid IR operand.
fileprivate func badOperand(file: StaticString = #file, line: UInt = #line) -> Never {
  preconditionFailure("bad operand", file: file, line: line)
}
