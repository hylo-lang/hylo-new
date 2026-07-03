import Archivist
import StableCollections
import Utilities

/// A function in Hylo IR.
public struct IRFunction: Sendable {

  /// The identity of an IR function in a module.
  public typealias ID = Int

  /// The name of an IR function.
  @Archivable
  public enum Name: Hashable, Sendable {

    /// The identity of a function lowered from sources.
    case lowered(DeclarationIdentity)

    /// The identity of a global initializer.
    case initializer(BindingDeclaration.ID)

    /// The identity of a synthesized function.
    case synthesized(DeclarationIdentity, TypeArguments)

    /// The identity of a function implementing a trait requirement.
    case implementation(DeclarationIdentity, ConformanceDeclaration.ID, TypeArguments)

    /// The identity of the existentialiezd form of a polymorphic function.
    indirect case existentialized(IRFunction.Name)

    /// The identity of a slide resulting from subscript decomposition.
    indirect case slide(IRFunction.Name, Int)

    /// The identity of a plateau resulting from subscript decomposition.
    indirect case plateau(IRFunction.Name, Int)

  }

  /// The way in which an IR function returns its result.
  @Archivable
  public enum Output: Hashable, Sendable {

    /// The result is written to an output parameter.
    case indirect

    /// The result is projected.
    case remote(AccessEffect, AnyTypeIdentity, isAddressor: Bool)

    /// The payload of `self` iff it denotes a projection.
    public var remote: (AccessEffect, AnyTypeIdentity, Bool)? {
      if case .remote(let k, let t, let b) = self {
        return (k, t, b)
      } else {
        return nil
      }
    }

  }

  /// A container wrapping an instruction together with additional properties about it.
  public struct Slot: Sendable {

    /// The instruction occupying the slot.
    fileprivate private(set) var instruction: any Instruction

    /// The tag of the instruction occpying the slot.
    fileprivate private(set) var tag: InstructionTag

    /// The basic block containing `instruction`.
    fileprivate var parent: IRBlock.ID

    /// Create an instance wrapping `instruction`, which is in `parent`.
    fileprivate init<T: Instruction>(instruction: T, parent: IRBlock.ID) {
      self.instruction = instruction
      self.tag = .init(T.self)
      self.parent = parent
    }

    /// Assigns the instruction wrapped into `self`.
    fileprivate mutating func assign<T: Instruction>(_ i: T) {
      self.instruction = i
      self.tag = .init(T.self)
    }

  }

  /// The types of an IR function's parameters and return value.
  public struct Signature: Sendable {

    /// The generic type parameters that the function accepts.
    public let context: [GenericParameter.ID]

    /// The types of the term parameters and return value.
    public let head: Arrow

    /// Creates the signature of a function accepting the given parameters and returning results
    /// as described by `output`.
    public init(types: [GenericParameter.ID], terms: [IRParameter], output: Output) {
      self.context = types

      let ps = terms.map({ (p) in Parameter(access: p.access, type: p.type) })
      switch output {
      case .indirect:
        self.head = Arrow(style: .parenthesized, inputs: ps.dropLast(), output: ps.last!.type)
      case .remote(let k, let o, _):
        self.head = Arrow(style: .bracketed, effect: k, inputs: ps, output: o.erased)
      }
    }

  }

  /// The name of the function.
  public let name: Name

  /// The way in which the function returns its result.
  public let output: Output

  /// The generic type parameters of the function.
  public let typeParameters: [GenericParameter.ID]

  /// The parameters of the function.
  public let termParameters: [IRParameter]

  /// A mapping from a source declaration to their its lowered definition.
  private var bindings: BidirectionalDictionary<DeclarationIdentity, IRValue>

  /// The instructions in the function.
  private var slots: List<Slot>

  /// The basic blocks in the function, the first of which being the function's entry.
  public private(set) var blocks: List<IRBlock>

  /// The use chains of the values in this function.
  public private(set) var uses: [IRValue: [Use]]

  /// Creates an instance with the given properties.
  public init(
    name: Name, output: Output,
    typeParameters: [GenericParameter.ID], termParameters: [IRParameter],
  ) {
    self.name = name
    self.output = output
    self.typeParameters = typeParameters
    self.termParameters = termParameters
    self.slots = []
    self.blocks = []
    self.uses = [:]
    self.bindings = [:]
  }

  /// `true` iff the function has an entry.
  public var isDefined: Bool {
    !blocks.isEmpty
  }

  /// `true` iff the function has no generic type parameters.
  public var isMonomorphic: Bool {
    typeParameters.isEmpty
  }

  /// `true` iff the function is a subscript.
  public var isSubscript: Bool {
    output != .indirect
  }

  /// `true` iff the function is an addressor (i.e., a subscript with an empty slide).
  public var isAddressor: Bool {
    if case .remote(_, _, let a) = output {
      return a
    } else {
      return false
    }
  }

   /// `true` iff the function returns a unit value (i.e., an instance of `Hylo.Void`).
  public var isProcedure: Bool {
    returnRegister.flatMap(result(of:))?.type == .void
  }

  /// The register in which the function writes its result, if any.
  public var returnRegister: IRValue? {
    (output == .indirect) ? .parameter(termParameters.count - 1) : nil
  }

  /// The entry block of `self`.
  public var entry: IRBlock.ID? {
    blocks.firstAddress
  }

  /// Returns `true` iff the last instruction of `b` is a terminator.
  public func isTerminated(_ b: IRBlock.ID) -> Bool {
    if let i = blocks[b].last {
      return at(i).isTerminator
    } else {
      return false
    }
  }

  /// Returns `true` iff `v` cannot be used to modify or update a value.
  public func isBoundImmutably(_ v: IRValue) -> Bool {
    switch v {
    case .parameter(let i):
      return termParameters[i].access == .let
    case .register(let i):
      return isBoundImmutably(i)
    default:
      return false
    }
  }

  /// Returns `true` iff the result of `i` cannot be used to modify or update a value.
  public func isBoundImmutably(_ i: AnyInstructionIdentity) -> Bool {
    switch tag(of: i) {
    case IRAlloca.self:
      return false
    case IRAccess.self:
      return (at(i) as! IRAccess).capabilities == [.let]
    case IRProject.self:
      return (at(i) as! IRProject).access == .let
    case IRSubfield.self:
      return isBoundImmutably((at(i) as! IRSubfield).base)
    default:
      return true
    }
  }

  /// Returns `true` iff `v` is a built-in value, using `program` to examine types.
  public func isBuiltinValue(_ v: IRValue, using program: Program) -> Bool {
    if let t = result(of: v) {
      return program.types.isBuiltin(t.type)
    } else {
      return false
    }
  }

  /// Returns the value defining the root of the place on which `i` forms an access.
  public func source(_ i: IRAccess.ID) -> IRValue {
    var s = at(i).source
    while let r = s.register {
      switch tag(of: r) {
      case IRPlaceCast.self:
        s = (at(r) as! IRPlaceCast).source
      case IRSubfield.self:
        s = (at(r) as! IRSubfield).base
      default:
        return s
      }
    }
    return s
  }

  /// Returns the last use of `v` in `b`, if any.
  public func lastUse(of v: IRValue, in b: IRBlock.ID) -> Use? {
    for i in instructions(in: b).reversed() {
      if let n = at(i).operands.lastIndex(of: v) {
        return Use(user: i, index: n)
      }
    }
    return nil
  }

  /// Returns the type of `self`, computing it using `p`.
  public func signature() -> Signature {
    .init(types: typeParameters, terms: termParameters, output: output)
  }

  /// Returns the tag of `i`.
  public func tag<T: InstructionIdentity>(of i: T) -> InstructionTag {
    slots[i.erased.address].tag
  }

  /// Returns `i` if it identifies an instruction of type `U`; otherwise, returns `nil`.
  public func cast<T: InstructionIdentity, U: Instruction>(_ i: T, to: U.Type) -> U.ID? {
    if tag(of: i) == .init(U.self) {
      return .init(uncheckedFrom: i.erased)
    } else {
      return nil
    }
  }

  /// Returns `i` assuming it identifies an instruction of type `U`.
  public func castUnchecked<T: InstructionIdentity, U: Instruction>(
    _ i: T, to: U.Type = U.self
  ) -> U.ID {
    assert(tag(of: i) == .init(U.self))
    return .init(uncheckedFrom: i.erased)
  }

  /// Returns the instruction identified by `i`.
  public func at(_ i: AnyInstructionIdentity) -> any Instruction {
    slots[i.address].instruction
  }

  /// Returns the instruction identified by `i`.
  public func at<T: Instruction>(_ i: T.ID) -> T {
    slots[i.erased.address].instruction as! T
  }

  /// Returns the register assigned by `i`, if any.
  public func definition(_ i: AnyInstructionIdentity) -> IRValue? {
    if at(i).type != .nothing {
      return .register(i)
    } else {
      return nil
    }
  }

  /// Returns the instruction that opens the region closed by `i`.
  public func start<T: IRRegionEntry>(of i: T.End.ID) -> T.ID {
    at(i).start.register.map({ (j) in castUnchecked(j, to: T.self) })!
  }

  /// Returns the basic block in which `i` is defined.
  public func block<T: InstructionIdentity>(defining i: T) -> IRBlock.ID {
    slots[i.erased.address].parent
  }

  /// Returns the basic block in which `v` is defined, if any.
  public func block(defining v: IRValue) -> IRBlock.ID? {
    switch v {
    case .register(let i):
      return block(defining: i)
    case .parameter:
      return entry
    default:
      return nil
    }
  }

  /// Returns the set of basic blocks reachable from `b`, which includes `b`.
  public func blocks(reachableFrom b: IRBlock.ID) -> IRBlockSet {
    var work = [b]
    var reachable = IRBlockSet()
    while let w = work.popLast() {
      reachable.insert(w)
      work.append(contentsOf: successors(of: w).filter({ (s) in !reachable.contains(s) }))
    }
    return reachable
  }

  /// Returns `true` iff `i` and `j` are in the same block and `i` is ordered before `j`.
  public func precedes(_ i: AnyInstructionIdentity, _ j: AnyInstructionIdentity) -> Bool {
    // Relation is irreflexive.
    if i == j { return false }

    let e = blocks[block(defining: i)].last!
    var k = slots.address(after: i.address)
    while true {
      switch k {
      case j.address:
        return true
      case e.address:
        return false
      default:
        k = slots.address(after: i.address)
      }
    }
  }

  /// Returns `true` iff `v` is an `access` instruction supporting k`.
  public func isAccess(_ v: IRValue, _ k: AccessEffect) -> Bool {
    ((v.register >>= at(_:)) as? IRAccess).satisfies({ (s) in s.capabilities.contains(k) })
  }

  /// Returns `true` iff `v` denotes a place.
  public func isPlace(_ v: IRValue) -> Bool {
    result(of: v).map(\.isPlace) ?? false
  }

  /// Returns `true` iff `v` is a parameter with access `k`.
  public func isParameter(_ v: IRValue, _ k: AccessEffect) -> Bool {
    switch v {
    case .parameter(let i):
      return termParameters[i].access == k
    default:
      return false
    }
  }

  /// Returns `true` iff `v` is an `alloca` or a `sink` parameter.
  public func owns(_ v: IRValue) -> Bool {
    switch v {
    case .register(let i):
      return tag(of: i) == IRAlloca.self
    case .parameter(let i):
      return termParameters[i].access == .sink
    default:
      return false
    }
  }

  /// Returns the type of the value computed by `v` or `nil` if `v` doesn't compute any.
  ///
  /// - Requires: `v` is either a constant or an instruction in this function.
  public func result(of v: IRValue) -> (type: AnyTypeIdentity, isPlace: Bool)? {
    switch v {
    case .parameter(let i):
      return resolved(.place(termParameters[i].type))
    case .register(let i):
      return resolved(at(i).type)
    case .integer(_, let t):
      return (t.erased, false)
    case .floatingPoint(_, let t):
      return (t.erased, false)
    case .function(_, let t):
      return (t, true)
    case .bundle(_, let t, _):
      return (t, true)
    case .type(_, let t):
      return (t.erased, false)
    case .poison(let t):
      return resolved(t)
    }
  }

  /// Returns the type of the function computed by `v` if any, using `program` to examine types.
  ///
  /// - Requires: `v` is either a constant or an instruction in this function.
  public func resultAsTermAbstraction(of v: IRValue, in program: Program) -> Arrow.ID? {
    result(of: v).flatMap({ (t, _) in program.types.seenAsTermAbstraction(t) })
  }

  /// Returns `t` without any relative definition.
  ///
  /// - Requires: `v` is either a constant or an instruction in this function.
  public func resolved(_ t: IRType) -> (type: AnyTypeIdentity, isPlace: Bool)? {
    switch t {
    case .place(let u):
      return (u, true)

    case .value(let u):
      return (u, false)

    case .same(let i):
      return result(of: i)

    case .dereferenced(let i):
      if let (u, isPlace) = result(of: i), isPlace {
        return (u, false)
      } else {
        fatalError("ill-formed IR type")
      }

    case .nothing:
      return nil
    }
  }

  /// Returns `true` iff `t` and `u` resolve denote the same type.
  private func areEqual(_ t: IRType, _ u: IRType) -> Bool {
    if let a = resolved(t) {
      return resolved(u).map({ b in a == b }) ?? false
    } else {
      return resolved(u) == nil
    }
  }

  /// Appends a basic block to this function and returns its identity.
  public mutating func addBlock() -> IRBlock.ID {
    blocks.append(.init())
  }

  /// Adds a new basic block, moves the instructions before `i` in that block, preserving relative
  /// order, and returns the new block's identity.
  ///
  /// After calling this method, `i` is the first instruction of the new block and all instructions
  /// preceding `i` are left in their current block, in the same order.
  public mutating func split(before i: AnyInstructionIdentity) -> IRBlock.ID {
    let a = block(defining: i)
    let b = addBlock()

    // Set `i` as the first instruction of the new block.
    blocks[b].setFirst(i)
    blocks[b].setLast(blocks[a].last!)

    // Set the instruction before `i` as the last instruction of the block that got split.
    if let j = instruction(before: i) {
      blocks[a].setLast(j)
    } else {
      blocks[a].clear()
    }

    // Update the parent block of all instructions after `b`
    for i in instructions(in: b) { slots[i.address].parent = b }
    return b
  }

  /// Returns the instruction that follows `i`.
  public func instruction(before i: AnyInstructionIdentity) -> AnyInstructionIdentity? {
    if blocks[block(defining: i)].first != i {
      return slots.address(before: i.address).map(AnyInstructionIdentity.init(address:))
    } else {
      return nil
    }
  }

  /// Returns the instruction that follows `i`.
  public func instruction(after i: AnyInstructionIdentity) -> AnyInstructionIdentity? {
    if blocks[block(defining: i)].last != i {
      return slots.address(after: i.address).map(AnyInstructionIdentity.init(address:))
    } else {
      return nil
    }
  }

  /// Returns the instructions in `self`.
  public func instructions() -> some Collection<AnyInstructionIdentity> {
    slots.addresses.lazy.map(AnyInstructionIdentity.init(address:))
  }

  /// Returns the instructions in `b`.
  public func instructions(in b: IRBlock.ID) -> IRBlock.Iterator {
    .init(slots: slots, last: blocks[b].last, current: blocks[b].first)
  }

  /// Returns the contents of `b` iff it contains exactly one instruction.
  public func uniqueInstruction(in b: IRBlock.ID) -> AnyInstructionIdentity? {
    if !blocks[b].isEmpty && (blocks[b].first == blocks[b].last) {
      return blocks[b].first
    } else {
      return nil
    }
  }

  /// Returns the instructions that follows `i` in the block containing `i`.
  public func instructions(after i: AnyInstructionIdentity) -> IRBlock.Iterator {
    let b = block(defining: i)
    return .init(
      slots: slots,
      last: blocks[b].last,
      current: slots.address(after: i.address).map(AnyInstructionIdentity.init(address:)))
  }

  /// Returns `true` iff `b` contains an instruction of type `T`.
  public func contains<T: Instruction>(in b: IRBlock.ID, _: T.Type) -> Bool {
    instructions(in: b).contains(where: { (i) in tag(of: i) == T.self })
  }

  /// Returns the successors of `b`.
  public func successors(of b: IRBlock.ID) -> [IRBlock.ID] {
    if let i = blocks[b].last, let s = at(i) as? any Terminator {
      return s.successors
    } else {
      return []
    }
  }

  /// Returns the control flow graph of this function.
  public func controlFlow() -> ControlFlowGraph {
    var g = ControlFlowGraph()
    for a in blocks.addresses {
      for b in successors(of: a) {
        g.define(a, predecessorOf: b)
      }
    }
    return g
  }

  /// Adds `instruction` at the end of `b` and returns its identity.
  @discardableResult
  public mutating func append<T: Instruction>(
    _ instruction: T, to b: IRBlock.ID
  ) -> AnyInstructionIdentity {
    assert(!isTerminated(b), "insertion after terminator")
    if let i = blocks[b].last {
      return insert(instruction, after: i)
    } else {
      return insert(instruction) { (me, i) in
        let a = me.slots.append(.init(instruction: i, parent: b))
        let s = AnyInstructionIdentity(address: a)
        me.blocks[b].setLast(s)
        return s
      }
    }
  }

  /// Adds `instruction` at the start of `b` and returns its identity.
  @discardableResult
  public mutating func prepend<T: Instruction>(
    _ instruction: T, to b: IRBlock.ID
  ) -> AnyInstructionIdentity {
    if let i = blocks[b].first {
      return insert(instruction, before: i)
    } else {
      return insert(instruction) { (me, i) in
        let a = me.slots.prepend(.init(instruction: i, parent: b))
        let s = AnyInstructionIdentity(address: a)
        me.blocks[b].setFirst(s)
        return s
      }
    }
  }

  /// Inserts `instruction` immediately before `j` and returns its identity.
  @discardableResult
  public mutating func insert<T: Instruction>(
    _ instruction: T, before j: AnyInstructionIdentity
  ) -> AnyInstructionIdentity {
    insert(instruction) { (me, i) in
      let b = me.block(defining: j)
      let a = me.slots.insert(.init(instruction: i, parent: b), before: j.address)
      let s = AnyInstructionIdentity(address: a)
      if me.blocks[b].first == j {
        me.blocks[b].setFirst(s)
      }
      return s
    }
  }


  /// Inserts `instruction` immediately after `j` and returns its identity.
  @discardableResult
  public mutating func insert<T: Instruction>(
    _ instruction: T, after j: AnyInstructionIdentity
  ) -> AnyInstructionIdentity {
    insert(instruction) { (me, i) in
      let b = me.block(defining: j)
      let a = me.slots.insert(.init(instruction: i, parent: b), after: j.address)
      let s = AnyInstructionIdentity(address: a)
      if me.blocks[b].last == j {
        me.blocks[b].setLast(s)
      }
      return s
    }
  }

  /// Inserts `instruction` at `boundary` and returns its identity.
  @discardableResult
  internal mutating func insert<T: Instruction>(
    _ instruction: T, at boundary: Lifetime.Boundary
  ) -> AnyInstructionIdentity {
    switch boundary {
    case .start(let b):
      return prepend(instruction, to: b)
    case .before(let j):
      return insert(instruction, before: j)
    case .after(let j):
      return insert(instruction, after: j)
    }
  }

  /// Inserts `instruction` with `impl` and returns its identity.
  private mutating func insert<T: Instruction>(
    _ instruction: T, with impl: (inout Self, T) -> AnyInstructionIdentity
  ) -> AnyInstructionIdentity {
    // Insert the instruction.
    let user = impl(&self, instruction)

    // Update the use chains.
    for i in 0 ..< instruction.operands.count {
      uses[instruction.operands[i], default: []].append(Use(user: user, index: i))
    }

    return user
  }

  /// Substitutes `old` with `new`.
  ///
  /// The use chains are updated so that the uses made by `old` are replaced by the uses made by
  /// `new` and all uses of `old` refer to `new`. After the call, `instruction(old) == new`.
  ///
  /// - Requires: The result of `new` has the same type as the result of old.
  internal mutating func replace<T: Instruction>(
    _ old: AnyInstructionIdentity, with new: T
  ) {
    assert(areEqual(at(old).type, new.type))
    removeUses(by: old)
    _ = insert(new) { (me, i) in
      me.slots[old.address].assign(i)
      return old
    }
  }

  /// Substitutes occurrences of `old` with `new` in the successors of `source`, returning `true`
  /// iff `old` was a successor of `source`.
  internal mutating func replaceSuccessor(
    _ old: IRBlock.ID, of source: IRBlock.ID, with new: IRBlock.ID
  ) -> Bool  {
    let l = blocks[source].last!
    if var s = at(l) as? any Terminator, s.replaceSuccessor(old, with: new) {
      slots[l.address].assign(s)
      return true
    } else {
      return false
    }
  }

  /// Removes `i` and updates use chains.
  ///
  /// - Requires: No instruction in `b` is used outside of `b`.
  public mutating func removeBlock(_ b: IRBlock.ID) {
    var a = blocks[b].first
    while let i = a {
      assert(uses[IRValue.register(i), default: []].allSatisfy({ block(defining: $0.user) == b }))
      removeUses(by: i)
      bindings.remove(value: .register(i))
      let n = (i != blocks[b].last) ? slots.address(after: i.address) : nil
      a = n.map(AnyInstructionIdentity.init(address:))
      slots.remove(at: i.address)
    }
    blocks.remove(at: b)
  }

  /// Removes `i` and updates use chains, returning the instruction following `i`, if any.
  ///
  /// - Requires: `i` has no users.
  @discardableResult
  public mutating func remove(_ i: AnyInstructionIdentity) -> AnyInstructionIdentity? {
    assert(uses[.register(i), default: []].isEmpty)
    removeUses(by: i)
    bindings.remove(value: .register(i))

    let p = block(defining: i)
    if i == blocks[p].first {
      if i == blocks[p].last {
        blocks[p] = .init()
      } else {
        blocks[p].setFirst(.init(address: slots.address(after: i.address)!))
      }
    } else if i == blocks[p].last {
      blocks[p].setLast(.init(address: slots.address(before: i.address)!))
    }

    defer { slots.remove(at: i.address) }
    return instruction(after: i)
  }

  /// Removes all instructions that follow `i` from the block containing `i`.
  ///
  /// - Requires: No removed instruction is used outside the block containing `i`.
  public mutating func removeAll(after i: AnyInstructionIdentity) {
    let p = block(defining: i)
    var j = blocks[p].last
    while let k = j, k != i {
      j = slots.address(before: k.address).map(AnyInstructionIdentity.init(address:))
      remove(k)
    }
  }

  /// Removes `i` from the use chains of its operands.
  private mutating func removeUses(by i: AnyInstructionIdentity) {
    for o in at(i).operands {
      uses[o]?.removeAll(where: { $0.user == i })
    }
  }

  /// Updates the bindings in `self` to associate the entity declared by `d` to the value `v`.
  public mutating func associate(_ d: DeclarationIdentity, with v: IRValue) {
    bindings.assignValue(v, forKey: d)
  }

  /// Returns the value representing the entity declared by `d`, if any.
  public func binding(_ d: DeclarationIdentity) -> IRValue? {
    bindings[key: d]
  }

  /// Returns the declaration represented by `v`, if any.
  public func declaration(_ v: IRValue) -> DeclarationIdentity? {
    bindings[value: v]
  }

  /// Returns an instance consuming the definition of `self` but leaving other properties intact.
  ///
  /// This method is similar to a "non-destructive" move extracting the definition of `self` (i.e.,
  /// its instructions) but leaving a valid function declaration behind. The moved definition can
  /// moved back into `self` using `take(definition:)`.
  public mutating func move() -> IRFunction {
    var other = IRFunction(
      name: name, output: output, typeParameters: typeParameters, termParameters: termParameters)

    swap(&self.bindings, &other.bindings)
    swap(&self.slots, &other.slots)
    swap(&self.blocks, &other.blocks)
    swap(&self.uses, &other.uses)
    return other
  }

  /// Assigns the definition of `self` to that of `other`, which has the same signature.
  ///
  /// `other` is the (possibly modified) result of `self.move()` and `self` has not have been
  /// modified in the meantime.
  public mutating func take(definition other: consuming IRFunction) {
    assert((self.name == other.name) && !isDefined)

    swap(&self.bindings, &other.bindings)
    swap(&self.slots, &other.slots)
    swap(&self.blocks, &other.blocks)
    swap(&self.uses, &other.uses)
  }

}

extension IRFunction: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "fun \(printer.show(name))"

    if !typeParameters.isEmpty {
      result.append("<\(printer.show(typeParameters))>")
    }

    result.append("(")
    for (i, p) in termParameters.enumerated() {
      if (i != 0) { result.append(", ") }
      result.append("\(p.access) \(printer.show(IRValue.parameter(i))): \(printer.show(p.type))")
    }
    result.append(")")

    if case .remote(let k, let t, let b) = self.output {
      if b { result = "@addressor\n\(result)" }
      result.append(" \(k) <: \(printer.show(t))")
    }

    if !slots.isEmpty {
      result.append(" {\n")
      for b in blocks.addresses {
        result.append("%b\(b.rawValue):\n")
        for i in instructions(in: b) {
          let r = IRValue.register(i)
          result.append("  \(printer.show(r)) = \(at(i).show(using: &printer))\n")
        }
      }
      result.append("}")
    }

    return result
  }

}

extension IRFunction.Name: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .lowered(let d):
      return printer.program.debugName(of: d)

    case .initializer(let d):
      return "\(printer.program.debugName(of: .init(d)))$init"

    case .synthesized(let d, let a):
      let xs = a.elements.map({ (p, v) in "\(printer.show(p)): \(printer.show(v))" })
      return "\(printer.program.debugName(of: d))<\(list: xs)>"

    case .implementation(let d, _, let a):
      let xs = a.elements.map({ (p, v) in "\(printer.show(p)): \(printer.show(v))" })
      return "\(printer.program.debugName(of: d))<\(list: xs)>"

    case .existentialized(let n):
      return "\(printer.show(n))$existentialized"

    case .slide(let n, let i):
      return "\(printer.show(n))$slide_\(i)"

    case .plateau(let n, let i):
      return "\(printer.show(n))$plateau_\(i)"
    }
  }

}

extension IRBlock {

  /// The contents of a basic block.
  public struct Iterator: IteratorProtocol, Sequence {

    public typealias Element = AnyInstructionIdentity

    /// The instructions containing the subsequence that `self` represents.
    private let slots: List<IRFunction.Slot>

    /// The identity of the last element in `self`.
    private let last: List<IRFunction.Slot>.Address?

    /// The identity of the next element in `self`, if any.
    private var current: List<IRFunction.Slot>.Address?

    /// Creates an instance enumerating the identities of the instructions in `slots` between
    /// `current` and `last`, included.
    fileprivate init(
      slots: List<IRFunction.Slot>, last: AnyInstructionIdentity?, current: AnyInstructionIdentity?
    ) {
      assert((current != nil) || (last == nil))
      self.slots = slots
      self.current = current?.address
      self.last = last?.address
    }

    public mutating func next() -> AnyInstructionIdentity? {
      if let n = current {
        current = (n != last) ? slots.address(after: n) : nil
        return .init(address: n)
      } else {
        return nil
      }
    }

  }

}

extension IRFunction: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    self.name = try archive.read(Name.self, in: &context)
    self.output = try archive.read(Output.self, in: &context)
    self.typeParameters = try archive.read([GenericParameter.ID].self, in: &context)
    self.termParameters = try archive.read([IRParameter].self, in: &context)
    self.slots = []
    self.blocks = []
    self.uses = [:]
    self.bindings = [:]

    /// Read the number of basic blocks in the function.
    let blockCount = try archive.readUnsignedLEB128()

    // Nothing else to do if there aren't any basic blocks.
    if blockCount == 0 { return }

    // Create the basic blocks and populate them.
    for _ in 0 ..< blockCount { _ = addBlock() }
    for b in blocks.addresses {
      let instructionCount = try archive.readUnsignedLEB128()
      for _ in 0 ..< instructionCount {
        let t = try archive.read(InstructionTag.self, in: &context)
        let v = try archive.read(t.value, in: &context)
        append(v, to: b)
      }
    }

    // Read the binding map.
    let bindingCount = try archive.readUnsignedLEB128()
    bindings.reserveCapacity(Int(bindingCount))
    for _ in 0 ..< bindingCount {
      let d = try archive.read(DeclarationIdentity.self, in: &context)
      let v = try archive.read(IRValue.self, in: &context)
      associate(d, with: v)
    }
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(name, in: &context)
    try archive.write(output, in: &context)
    try archive.write(typeParameters, in: &context)
    try archive.write(termParameters, in: &context)

    // Write the number of basic blocks in the function. Note that the function cannot contain any
    // unreachable block at this point.
    archive.write(unsignedLEB128: blocks.count)

    // Nothing else to do if there aren't any basic blocks.
    if !isDefined { return }

    // Prepare a substitution table to compute the canonical form of the function as we go. Basic
    // blocks are renamed with a zero-based offset and serialized in an order guaranteeing that
    // definitions appear before their uses when the archive is deserialized.
    let dominance = DominatorTree(function: self, controlFlow: self.controlFlow())
    let ordered = Array(dominance)
    var table = IRSubstitutionTable()
    for b in ordered {
      table[b] = IRBlock.ID(table.blocks.count)
    }
    assert(blocks.count == table.blocks.count)

    // Write the contents of the function to the archive, visiting its basic blocks in such a way
    // that they can be deserialized in a single forward pass.
    var registers = 0
    for b in ordered {
      // Write the number of instructions in the block.
      let all = Array(instructions(in: b))
      archive.write(unsignedLEB128: all.count)

      for i in all {
        // Create a copy of the instruction in which references to registers and basic blocks have
        // been replaced with their corresponding values in the archive.
        let s = at(i)
        let t = type(of: s)
        let c = t.init(s, substituting: table)!

        // Does the instruction define a register that may be referred to?
        if c.type != .nothing {
          table[.register(i)] = .register(.init(address: .init(registers)))
        }

        // Write the instruction.
        try archive.write(InstructionTag(t), in: &context)
        try archive.write(c, in: &context)

        registers += 1
      }
    }

    // Write the binding map.
    try archive.write(contentsOf: bindings.sorted(by: \.key), in: &context) { (x, a, c) in
      try x.key.write(to: &a, in: &c)
      try x.value.write(to: &a, in: &c)
    }
  }

}
