import Utilities

extension IRFunction {

  /// Verifies that that `self` does not perform any overlapping access to mutable data.
  internal mutating func upholdExclusivity(
    emittingInto m: Module.ID, using typer: inout Typer
  ) -> Bool {
    var initial = Transfer.Context()
    for (i, t) in termParameters.enumerated() {
      addParameter(t, offset: i, to: &initial)
    }

    var transfer = Transfer(emittingInto: m)
    transfer.fixedPoint(interpreting: &self, startingFrom: initial, using: &typer)

    return !typer.program[m].containsError
  }

  /// Configures `context` with the initial state of `p`, which is the `i`-th parameter of `self`.
  private mutating func addParameter(
    _ p: IRParameter, offset i: Int, to context: inout Transfer.Context
  ) {
    let t = resolved(p.type)!.type
    context.locals[.parameter(i)] = .place(.root(.parameter(i)))
    context.memory[.parameter(i)] = .init(type: t, value: .uniform(.unique))
  }

  /// Returns the access instruction from which `i` reborrows, if any.
  fileprivate func reborrowedSource(_ i: IRAccess.ID) -> IRAccess.ID? {
    var source = at(i).source
    while let r = source.register, let s = cast(r, to: IRSubfield.self) {
      source = at(s).base
    }
    return source.register.flatMap({ (r) in cast(r, to: IRAccess.self) })
  }

  /// Returns `true` iff it is legal to form an immutable access on a place bound by `bs` with an
  /// instruction reborrowing from `s`.
  ///
  /// - Parameters:
  ///   - bs  The instructions having formed an access on the place to bind.
  ///   - s   The access instruction in `bs` from wich the access to form reborrows.
  fileprivate func isValidImmutableAccess(
    reborrowingFrom s: IRAccess.ID?, sharedBy bs: Transfer.Domain.Users
  ) -> Bool {
    if bs.isEmpty || bs.contains(where: { (b) in at(b).capabilities.contains(.let) }) {
      return true
    } else {
      return (bs.count == 1) && (bs[0] == s)
    }
  }
  /// Returns `true` iff it is legal to form an mutable access on a place bound by `bs` with an
  /// instruction reborrowing from `s`.
  ///
  /// - Parameters:
  ///   - bs  The instructions having formed an access on the place to bind.
  ///   - s   The access instruction in `bs` from wich the access to form reborrows.
  fileprivate func isValidMutableAccess(
    reborrowingFrom s: IRAccess.ID?, sharedBy bs: Transfer.Domain.Users
  ) -> Bool {
    if bs.isEmpty {
      return true
    } else {
      return (bs.count == 1) && (bs[0] == s) && !at(s!).capabilities.contains(.let)
    }
  }

}

/// A transfer function for interpreting IR during exclusivity analysis.
private struct Transfer: AbstractTransferFunction {

  /// The module containing the instructions intepreted by this function.
  private let module: Module.ID

  /// A typer for querying type relations and resolve names.
  private var typer: Typer! = nil

  /// The context being updated.
  private var context: Context = .init()

  /// Creates an instance for interpreting the contents of `m`.
  fileprivate init(emittingInto m: Module.ID) {
    self.module = m
  }

  /// The program containing the module being typed.
  private var program: Program {
    get { typer.program }
    _modify { yield &typer.program }
  }

  mutating func apply(
    _ b: IRBlock.ID, from f: inout IRFunction, in c: inout Context,
    precededBy predecessors: SortedDictionary<IRBlock.ID, Context>,
    using typer: inout Typer
  ) -> [IRBlock.ID] {
    self.typer = consume typer
    swap(&context, &c)

    defer {
      typer = self.typer.sink()
      swap(&context, &c)
    }

    var pc = f.blocks[b].first
    while let i = pc {
      switch f.tag(of: i) {
      case IRAccess.self:
        pc = interpret(f.castUnchecked(i, to: IRAccess.self), from: &f)
      case IRAccess.End.self:
        pc = interpret(f.castUnchecked(i, to: IRAccess.End.self), from: &f)
      case IRAlloca.self:
        pc = interpret(f.castUnchecked(i, to: IRAlloca.self), from: &f)
      case IRProject.self:
        pc = interpret(f.castUnchecked(i, to: IRProject.self), from: &f)
      case IRProject.End.self:
        pc = interpret(f.castUnchecked(i, to: IRProject.End.self), from: &f)
      case IRProperty.self:
        pc = interpret(f.castUnchecked(i, to: IRProperty.self), from: &f)
      case IRSubfield.self:
        pc = interpret(f.castUnchecked(i, to: IRSubfield.self), from: &f)
      case IRWitnessTable.self:
        pc = interpret(f.castUnchecked(i, to: IRWitnessTable.self), from: &f)
      default:
        pc = f.instruction(after: i.erased)
      }
    }

    return []
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAccess.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let access = f.at(i)

    let s = f.reborrowedSource(i)
    let a = context.locals[access.source]!.place!
    let d = context.withObject(at: a, computingLayoutWith: &typer) { (o, _) -> Diagnostic? in
      switch access.capabilities.uniqueElement! {
      case .let:
        if f.isValidImmutableAccess(reborrowingFrom: s, sharedBy: borrowers(o.value)) {
          insertBorrower(i, into: &o.value)
          return nil
        } else {
          return .illegalImmutableAccess(at: access.anchor.site)
        }

      case .inout, .set, .sink:
        if f.isBoundImmutably(access.source) {
          return .illegalMutableAccess(at: access.anchor.site)
        }

        if f.isValidMutableAccess(reborrowingFrom: s, sharedBy: borrowers(o.value)) {
          if let former = s { removeBorrower(former, from: &o.value) }
          insertBorrower(i, into: &o.value)
          return nil
        } else {
          return .illegalMutableAccess(at: access.anchor.site)
        }

      case .auto:
        fatalError("invalid IR")
      }
    }

    d.map({ (d) in report(d) })

    context.locals[.register(i.erased)] = context.locals[access.source]!
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAccess.End.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let access = f.start(of: i)

    let a = context.locals[.register(access.erased)]!.place!
    context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      removeBorrower(access, from: &o.value)
      if let s = f.reborrowedSource(access) {
        insertBorrower(s, into: &o.value)
      }
    }

    context.locals[.register(access.erased)] = nil
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAlloca.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    context.declare(i.erased, from: f, initially: .unique)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProject.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    context.declare(i.erased, from: f, initially: .unique)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProject.End.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    context.memory[f.at(i).start] = nil
    context.locals[f.at(i).start] = nil
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProperty.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    context.declare(i.erased, from: f, initially: .unique)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRSubfield.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    let a = context.locals[s.base]!.place!.appending(contentsOf: s.path)
    context.locals[.register(i.erased)] = .place(a)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRWitnessTable.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    context.declare(i.erased, from: f, initially: .unique)
    return f.instruction(after: i.erased)
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// The ownership state of an object or sub-object.
  ///
  /// Instances form a lattice whose supremum is `.unique` and infimum is `.shared(by: s)` where
  /// `s` is the set of all instructions. The meet of two elements denotes the conservative
  /// superposition of two states.
  enum Domain: AbstractDomain {

    /// A set of instructions having consumed or borrowed a value.
    typealias Users = SortedSet<IRAccess.ID>

    /// Object is bound uniquely.
    case unique

    /// Object is rebound one or more times.
    ///
    /// - Requires: The payload is not empty.
    case shared(Users)

    /// Forms a new state by merging `lhs` with `rhs`.
    static func && (lhs: Self, rhs: Self) -> Self {
      switch (lhs, rhs) {
      case (let x, let y) where x == y:
        return x
      case (.unique, _):
        return rhs
      case (_, .unique):
        return lhs
      case (.shared(let a), .shared(let b)):
        return .shared(a.union(b))
      }
    }

    /// Returns a textual representation of `self` using `printer`.
    func show(using printer: inout TreePrinter) -> String {
      switch self {
      case .unique:
        return "◼"
      case .shared(let us):
        return "◻{\(printer.show(us.map({ (r) in IRValue.register(r.erased) })))}"
      }
    }

  }

}

/// Returns the set of instructions borrowing `v` or part thereof.
private func borrowers(_ v: AbstractObject<Transfer.Domain>.Value) -> Transfer.Domain.Users {
  switch v {
  case .uniform(.unique):
    return []
  case .uniform(.shared(let bs)):
    return bs
  case .mixed(let ps):
    return ps.reduce([], { (rs, bs) in rs.union(borrowers(bs)) })
  }
}

/// Adds `b` to the borrowers of `v`, returning `true` iff `b` wasn't already included.
@discardableResult
private func insertBorrower(
  _ b: IRAccess.ID, into v: inout AbstractObject<Transfer.Domain>.Value
) -> Bool {
  switch v {
  case .uniform(.unique):
    v = .uniform(.shared([b]))
    return true

  case .uniform(.shared(var bs)):
    let (inserted, _) = bs.insert(b)
    v = .uniform(.shared(bs))
    return inserted

  case .mixed(var ps):
    var n = 0
    for i in ps.indices where insertBorrower(b, into: &ps[i]) { n += 1 }
    v = (n == ps.count) ? .mixed(ps).canonical : .mixed(ps)
    return n > 0
  }
}

/// Removes `b` from the borrowers of `v`, returning `true` iff `b` wasn't already included.
@discardableResult
private func removeBorrower(
  _ b: IRAccess.ID, from v: inout AbstractObject<Transfer.Domain>.Value
) -> Bool {
  switch v {
  case .uniform(.unique):
    return true

  case .uniform(.shared(var bs)):
    let removed = bs.remove(b) != nil
    v = bs.isEmpty ? .uniform(.unique) : .uniform(.shared(bs))
    return removed

  case .mixed(var ps):
    var r = false
    for i in ps.indices where removeBorrower(b, from: &ps[i]) { r = true }
    return r
  }
}
