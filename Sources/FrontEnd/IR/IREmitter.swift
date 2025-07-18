import Utilities

/// A constructor of Hylo IR.
internal struct IREmitter {

  /// The module being typed.
  public let module: Module.ID

  /// The program containing the module being typed.
  public internal(set) var program: Program

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
    case FunctionDeclaration.self:
      lower(program.castUnchecked(d, to: FunctionDeclaration.self))
    case TraitDeclaration.self:
      lower(program.castUnchecked(d, to: TraitDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Generates the IR of `d`.
  private mutating func lower(_ d: FunctionDeclaration.ID) {
    withClearContext({ $0.lowerAssumingClearContext(d) })
  }

  /// Generates the IR of `d` assuming the insertion context is clear.
  private mutating func lowerAssumingClearContext(_ d: FunctionDeclaration.ID) {
    let f = demandLoweredDeclaration(of: d)

    // Is there a body to lower?
    guard let body = program[d].body else {
      assert(!program.requiresDefinition(.init(d)), "ill-formed syntax")
      // TODO: FFI
      return
    }

    // Did we already lower the function?
    insertionContext.function = program[module][f]
    assert(!insertionContext.function!.isDefined, "function already lowered")

    insertionContext.point = .end(of: insertionContext.function!.addBlock())
    var frame = Frame()
    for (i, p) in program[module][f].termParameters.enumerated() {
      if let local = p.declaration {
        frame[local] = .parameter(i)
      }
    }

    switch within(frame, { $0.lower(body: body) }) {
    case .return(let r):
      lowering(r, { $0._return() })
    case .next:
      lowering(after: body.last!, { $0._return() })
    }

    program[module][f] = insertionContext.function.sink()
  }

  /// Generates the IR of the members in `d` having a default implementation.
  private mutating func lower(_ d: TraitDeclaration.ID) {
    for m in program[d].members { lower(m) }
  }

  /// Generates the IR of `body`, which is the definition of an abstraction.
  private mutating func lower(body: [StatementIdentity]) -> ControlFlow {
    for i in body.indices {
      let e = lower(body[i])
      if case .next = e {
        continue
      } else {
        if (i + 1) < body.count {
          report(.warning, "code will never be executed", about: body[i + 1])
        }
        return e
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
      program.unexpected(s)
    }
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Discard.ID) -> ControlFlow {
    let v = lowered(lvalue: program[s].value)
    lowering(s, { $0._emitDeinitialize(v) })
    return .next
  }

  /// Generates the IR of `s`.
  private mutating func lower(_ s: Return.ID) -> ControlFlow {
    let r = currentReturnRegister
    if let e = program[s].value {
      lower(store: e, to: r)
    } else if currentFunction.type(of: r)?.type == .void {
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
    case NameExpression.self:
      lower(store: program.castUnchecked(e, to: NameExpression.self), to: target)
    case TupleLiteral.self:
      lower(store: program.castUnchecked(e, to: TupleLiteral.self), to: target)
    default:
      program.unexpected(e)
    }
  }

  /// Implements `lower(store:to:)` for call expressions.
  private mutating func lower(store e: Call.ID, to target: IRValue) {
    let callee = loweredCallee(program[e].callee)

    var operands: [IRValue] = .init(minimumCapacity: program[e].arguments.count + 1)
    operands.append(target)

    // Compute lvalues first and query accesses next, so that a mutable accesses passed down to the
    // call are not formed prematurely. This behavior supports calls to mutating methods in which
    // arguments involve the receiver (e.g., `&x.modify(x.read())`).
    for a in program[e].arguments {
      operands.append(lowered(lvalue: a.value))
    }

    assert(operands.count == callee.type.inputs.count + 1)
    lowering(e) { (me) in
      // Form accesses on the parameters.
      operands[0] = me._access([.set], from: operands[0])
      for i in 1 ..< operands.count {
        operands[i] = me._access(.init(callee.type.inputs[i - 1].access), from: operands[i])
      }

      // Do the call.
      me._apply(callee.value, toTypes: callee.typeArguments, toTerms: operands)

      // End accesses on the parameters.
      for o in operands.reversed() {
        me._end(IRAccess.self, openedBy: o)
      }
    }
  }

  /// Implements `lower(store:to:)` for name expressions.
  private mutating func lower(store e: NameExpression.ID, to target: IRValue) {
    let v = lowered(lvalue: e)
    lowering(e, { $0._emitMove([.inout, .set], v, to: target) })
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
      let s = lowering(x.value, { $0._subfield(target, at: [i]) })
      lower(store: x.value, to: s)
    }
  }

  /// The IR value, type, and type arguments of a callee.
  private struct LoweredCallee {

    /// The lowered value of the callee (e.g., a function pointer).
    ///
    /// The callee is generic iff `self.typeArguments` is not empty, in which case `self.value`
    /// denotes a generic function not yet existentialized.
    let value: IRValue

    /// The source-level type of the callee.
    let type: Callable

    /// The type arguments of the callee if it is generic.
    let typeArguments: TypeArguments

  }

  /// Generates the IR for using `e` as a callee.
  private mutating func loweredCallee(
    _ e: ExpressionIdentity
  ) -> LoweredCallee {
    switch program.tag(of: e) {
    case NameExpression.self:
      return loweredCallee(program.castUnchecked(e, to: NameExpression.self))
    case SynthethicExpression.self:
      return loweredCallee(program.castUnchecked(e, to: SynthethicExpression.self))
    default:
      program.unexpected(e)
    }
  }

  /// Implements `loweredCallee(_:)` for name expressions.
  private mutating func loweredCallee(
    _ e: NameExpression.ID, appliedTo a: TypeArguments = .init()
  ) -> LoweredCallee {
    let typeOfCallee = program.types.seenAsCallableAbstraction(program.type(assignedTo: e))!

    // Is the callee referring to a member declared in extension?
    if case .inherited(let w, let m) = program.declaration(referredToBy: e) {
      // The type assigned to the callee should be a callable.
      let p = program.types.pointer(to: typeOfCallee)
      return lowering(e) { (me) in
        let r = me._emit(witness: w)
        return .init(value: me._getter(r, m, withType: p), type: typeOfCallee, typeArguments: a)
      }
    }

    else {
      fatalError()
    }
  }

  /// Implements `loweredCallee(_:)` for synthetic expressions.
  private mutating func loweredCallee(
    _ e: SynthethicExpression.ID
  ) -> LoweredCallee {
    guard case .witness(let w) = program[e].value else { program.unexpected(e) }
    switch w.value {
    case .typeApplication(let f, let a):
      if case .identity(let i) = f.value, let n = program.cast(i, to: NameExpression.self) {
        return loweredCallee(n, appliedTo: a)
      }

    default:
      break
    }

    program.unexpected(e)
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

  /// Returns the identity of the function lowering `d`, declaring it if needed.
  ///
  /// `d` identifies the declaration of a callable abstraction (e.g., a function declaration).
  private mutating func demandLoweredDeclaration<T: Declaration & Scope>(
    of d: T.ID
  ) -> IRFunction.ID {
    let name = IRFunction.Name.lowered(.init(d))
    if let i = program[module].ir.index(forKey: name) {
      return i
    }

    let ps = termParameters(of: d)
    let ts = program.accumulatedGenericParameters(visibleFrom: .init(node: d))
    return program[module].addFunction(
      IRFunction(name: name, typeParameters: ts, termParameters: ps, returnStyle: .register))
  }

  /// Returns the term parameters of `d`'s lowered representation, which includes `d`' explicit
  /// parameters, usings, and captures.
  ///
  /// IR functions can be generic. Type parameters are only lowered to term parameters in
  /// existentialized functions.
  private mutating func termParameters<T: Declaration>(of d: T.ID) -> [IRParameter] {
    let abstraction = program.types.seenAsCallableAbstraction(program.type(assignedTo: d))!
    let parameters = program.parametersAndCaptures(of: d)

    var result: [IRParameter] = []

    // Return register comes first.
    if abstraction.style == .parenthesized {
      let o = loweredType(addressOf: abstraction.output)
      result.append(IRParameter(type: o, access: .set, declaration: nil))
    }

    // Is `d` a trait requirement?
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

    // Using parameters come next.
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

    // TODO
    assert(parameters.captures.isEmpty)

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

  /// The return register of `self.currentFunction`, assuming its return style is `.register`.
  private var currentReturnRegister: IRValue {
    assert(currentFunction.returnStyle == .register)
    return .parameter(0)
  }

  /// Returns the result of calling `action` on a typer configured with `self.module`.
  private mutating func withTyper<T>(_ action: (inout Typer) -> T) -> T {
    withUnsafeMutablePointer(to: &program) { [m = module] (p) in
      var typer = Typer(typing: m, of: p.move())
      defer { p.initialize(to: typer.release()) }
      return action(&typer)
    }
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
      case .start(let b):
        f.prepend(instruction, to: b)
      case .end(let b):
        f.append(instruction, to: b)
      }
      return f.result(of: i)
    }
  }

  /// Inserts an `access` instruction.
  private mutating func _access(_ k: AccessEffectSet, from source: IRValue) -> IRValue {
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
  private mutating func _alloca(
    _ type: AnyTypeIdentity, alignment: IRAlignment? = nil, inEntry: Bool = true
  ) -> IRValue {
    let t = program.types.dealiased(type)
    let a = alignment ?? .align(of: t)
    let i = IRAlloca(storageType: t, alignment: a, anchor: currentAnchor)

    if inEntry {
      return modify(&insertionContext.function!) { (f) in
        let i = f.prepend(i, to: f.entry!)
        return f.result(of: i)!
      }
    } else {
      return insert(i)!
    }
  }

  /// Inserts a `apply` instruction.
  private mutating func _apply(
    _ callee: IRValue,
    toTypes typeArguments: TypeArguments,
    toTerms termArguments: [IRValue]
  ) {
    let a = program.types.dealiased(typeArguments)
    insert(
      IRApply(
        callee: callee, typeArguments: a, termArguments: termArguments, anchor: currentAnchor))
  }

  /// Inserts a `apply_builtin` instruction.
  private mutating func _apply_builtin(
    _ callee: BuiltinFunction, returning returnTypeOfCallee: AnyTypeIdentity,
    to arguments: [IRValue]
  ) -> IRValue {
    let t = program.types.dealiased(returnTypeOfCallee)
    return insert(
      IRApplyBuiltin(
        callee: callee, returnTypeOfCallee: t, arguments: arguments, anchor: currentAnchor))!
  }

  /// INserts a `assume_state` instruction.
  private mutating func _assume_state(_ s: IRValue, initialized: Bool) {
    insert(IRAssumeState(storage: s, initialized: initialized, anchor: currentAnchor))
  }

  /// Inserts an `end` instruction.
  private mutating func _end<T: IRRegionEntry>(_: T.Type, openedBy start: IRValue) {
    assert(currentFunction.instructions[start.register!] is T)
    insert(T.End(start: start, anchor: currentAnchor))
  }

  /// Inserts a `getter` instruction.
  private mutating func _getter(
    _ receiver: IRValue,
    _ property: DeclarationIdentity,
    withType typeOfGetter: FunctionPointer.ID
  ) -> IRValue {
    let s = IRGetter(
      property: property, receiver: receiver, typeOfGetter: typeOfGetter, anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `load` instruction.
  private mutating func _load(_ source: IRValue) -> IRValue {
    assert(currentFunction.isAddress(source))
    return insert(IRLoad(source: source, anchor: currentAnchor))!
  }

  /// Inserts a `move` instruction.
  private mutating func _move(_ source: IRValue, to target: IRValue) {
    assert(currentFunction.isAddress(source))
    assert(currentFunction.isAddress(target))
    insert(IRMove(source: source, target: target, anchor: currentAnchor))
  }

  /// Inserts a `return` instruction.
  private mutating func _return() {
    insert(IRReturn(anchor: currentAnchor))
  }

  /// Inserts a `store` instruction.
  private mutating func _store(_ value: IRValue, to target: IRValue) {
    fatalError()
  }

  /// Inserts a `subfield` instruction.
  private mutating func _subfield(_ base: IRValue, at path: IndexPath) -> IRValue {
    let (root, _) = currentFunction.type(of: base) ?? unreachable("bad address")
    let typeOfSubfield = withTyper({ (tp) in tp.field(of: root, at: path) })
    let s = IRSubfield(
      base: base, path: path, typeOfSubfield: typeOfSubfield!, anchor: currentAnchor)
    return insert(s)!
  }

  /// Inserts a `synthetic_conformance` instruction.
  private mutating func _synthetic_conformance(_ t: AnyTypeIdentity) -> IRValue {
    return insert(IRSyntheticConformance(witness: t, anchor: currentAnchor))!
  }

  /// Generates the IR of `r`, which computes a lvalue.
  private mutating func _emit(reference r: DeclarationReference) -> IRValue {
    switch r {
    case .direct(let d):
      return _emit(directReferenceTo: d)
    default:
      fatalError()
    }
  }

  /// Generates the IR for referring directly to `d`.
  private mutating func _emit(directReferenceTo d: DeclarationIdentity) -> IRValue {
    // Is `d` referring to a local?
    if let s = insertionContext.frames[d] {
      return s
    }

    fatalError()
  }

  /// Generates the IR for computing the lvalue referred to by `w`.
  private mutating func _emit(witness w: WitnessExpression) -> IRValue {
    switch w.value {
    case .identity(let e):
      return lowered(lvalue: e)
    case .reference(let r):
      return _emit(reference: r)
    default:
      fatalError()
    }
  }

  /// Generates the IR for deinitializing `source`.
  private mutating func _emitDeinitialize(_ source: IRValue) {
    let (typeOfSource, _) = currentFunction.type(of: source) ?? unreachable("bad address")

    // Nothing to do for machine types.
    if program.types.tag(of: typeOfSource) == MachineType.self {
      _assume_state(source, initialized: false)
      return
    }

    // Other types need a conformance to `Hylo.Deinitializable`.
    guard let deinitializable = _emitWitness(of: typeOfSource, is: .deinitializable) else {
      return
    }

    let member = program.standardLibraryDeclaration(.deinitializableDeinit)
    let t0 = currentFunction.type(of: deinitializable)!.type
    let t1 = program.types.demand(RemoteType(projectee: t0, access: .let))
    let t2 = program.types.demand(RemoteType(projectee: typeOfSource, access: .sink))
    let fp = program.types.demand(
      FunctionPointer(inputs: [t1.erased, t2.erased], output: .void))

    let x0 = _getter(deinitializable, member, withType: fp)
    let x1 = _alloca(.void)

    let y0 = _access([.set], from: x1)
    let y1 = _access([.let], from: deinitializable)
    let y2 = _access([.sink], from: source)

    _apply(x0, toTypes: .init(), toTerms: [y0, y1, y2])

    _end(IRAccess.self, openedBy: y2)
    _end(IRAccess.self, openedBy: y1)
    _end(IRAccess.self, openedBy: y0)
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
      let (typeOfSource, _) = currentFunction.type(of: source) ?? unreachable("bad address")
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
    let t0 = currentFunction.type(of: movable)!.type
    let t1 = program.types.demand(RemoteType(projectee: t0, access: .let))
    let t2 = program.types.demand(RemoteType(projectee: typeOfSource, access: .sink))
    let fp = program.types.demand(
      FunctionPointer(inputs: [t1.erased, t2.erased, t2.erased], output: .void))

    let x0 = _getter(movable, .init(member), withType: fp)
    let x1 = _alloca(.void)

    let y0 = _access([.set], from: x1)
    let y1 = _access([.let], from: movable)
    let y2 = _access([k], from: source)
    let y3 = _access([.sink], from: source)

    _apply(x0, toTypes: .init(), toTerms: [y0, y1, y2, y3])

    _end(IRAccess.self, openedBy: y3)
    _end(IRAccess.self, openedBy: y2)
    _end(IRAccess.self, openedBy: y1)
    _end(IRAccess.self, openedBy: y0)
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

  private mutating func _emitWitness(
    of t: AnyTypeIdentity, is p: Program.StandardLibraryEntity
  ) -> IRValue? {
    let goal = program.typeOfWitness(of: t, is: p)
    let scopeOfUse = insertionContext.anchor!.scope
    let candidates = withTyper { (tp) in
      tp.summon(goal, in: scopeOfUse)
    }

    if let pick = candidates.uniqueElement {
      return _emit(witness: pick.witness)
    }

    else if withTyper({ (tp) in tp.isDerivable(conformanceTo: p, for: t, in: scopeOfUse) }) {
      return _synthetic_conformance(goal)
    }

    else {
      report(program.noUniqueGivenInstance(of: goal, found: candidates, at: currentAnchor.site))
      _ = _apply_builtin(.trap, returning: .never, to: [])
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
  fileprivate func parametersAndCaptures<T: Declaration>(of d: T.ID) -> ParametersAndCaptures {
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
