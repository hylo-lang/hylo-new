import StableCollections
import Utilities

/// A function in Hylo IR.
public struct IRFunction: Sendable {

  /// The identity of an IR function in a module.
  public typealias ID = Int

  /// The name of an IR function.
  public enum Name: Hashable, Sendable {

    /// The identity of a function lowered from sources.
    case lowered(DeclarationIdentity)

  }

  /// The way in which an IR function returns its result.
  public enum Result: Hashable, Sendable {

    /// The result is returned in register.
    case register

    /// The result is projected.
    case projection(AnyTypeIdentity)

    /// The payload of `self` iff it denotes a projection.
    public var projection: AnyTypeIdentity? {
      if case .projection(let t) = self {
        return t
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
    fileprivate let parent: IRBlock.ID

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

  /// The name of the function.
  public let name: Name

  /// The way in which the function returns its result.
  public let result: Result

  /// The generic type parameters of the function.
  public let typeParameters: [GenericParameter.ID]

  /// The parameters of the function.
  public let termParameters: [IRParameter]

  /// The instructions in the function.
  private var slots: List<Slot> = []

  /// The basic blocks in the function, the first of which being the function's entry.
  public private(set) var blocks: List<IRBlock> = []

  /// The use chains of the values in this function.
  public private(set) var uses: [IRValue: [Use]] = [:]

  /// Creates an instance with the given properties.
  public init(
    name: Name, result: Result,
    typeParameters: [GenericParameter.ID], termParameters: [IRParameter],
  ) {
    self.name = name
    self.result = result
    self.typeParameters = typeParameters
    self.termParameters = termParameters
    self.slots = []
    self.blocks = []
  }

  /// `true` iff the function has an entry.
  public var isDefined: Bool {
    !blocks.isEmpty
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

  /// Returns the instructions of `b`.
  public func contents(of b: IRBlock.ID) -> some Sequence<AnyInstructionIdentity> {
    var next = blocks[b].first?.address
    let last = blocks[b].last?.address
    return AnyIterator {
      if let n = next {
        next = (n != last) ? slots.address(after: n) : nil
        return AnyInstructionIdentity(address: n)
      } else {
        return nil
      }
    }
  }

  /// Returns the last use of `v` in `b`, if any.
  public func lastUse(of v: IRValue, in b: IRBlock.ID) -> Use? {
    for i in contents(of: b).reversed() {
      if let n = at(i).operands.lastIndex(of: v) {
        return Use(user: i, index: n)
      }
    }
    return nil
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

  /// Returns the register asssigned by `i`, if any.
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
  public func block(defining i: AnyInstructionIdentity) -> IRBlock.ID {
    slots[i.address].parent
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

  /// Returns `true` iff `v` denotes an address.
  public func isAddress(_ v: IRValue) -> Bool {
    result(of: v).map(\.isAddress) ?? false
  }

  /// Returns the type of the value computed by `v` or `nil` if `v` doesn't compute any.
  ///
  /// - Requires: `v` is either a constant or an instruction in this function.
  public func result(of v: IRValue) -> (type: AnyTypeIdentity, isAddress: Bool)? {
    switch v {
    case .parameter(let i):
      return resolved(termParameters[i].type)
    case .register(let i):
      return resolved(at(i).type)
    case .integer(_, let t):
      return (t.erased, false)
    case .function(_, let t):
      return (t.erased, true)
    }
  }

  /// Returns `t` without any relative definition.
  ///
  /// - Requires: `v` is either a constant or an isntruction in this function.
  public func resolved(_ t: IRType) -> (type: AnyTypeIdentity, isAddress: Bool)? {
    switch t {
    case .lowered(let u, let isAddress):
      return (u, isAddress)

    case .same(let i):
      return result(of: i)

    case .dereferenced(let i):
      if let (u, isAddress) = result(of: i), isAddress {
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
    .init(slots: slots, current: blocks[b].first, last: blocks[b].last)
  }

  /// Returns the successors of `b`.
  public func successors(of b: IRBlock.ID) -> [IRBlock.ID] {
    if let i = blocks[b].last, let s = at(i) as? any Terminator {
      return s.successors
    } else {
      return []
    }
  }

  /// Returns the identities encoded in `bs`.
  public func decode(_ bs: IRBlockSet) -> some Sequence<IRBlock.ID> {
    bs.elements.lazy.compactMap(blocks.address(rawValue:))
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
    return insert(instruction) { (me, i) in
      let a = me.slots.append(.init(instruction: i, parent: b))
      let s = AnyInstructionIdentity(address: a)
      me.blocks[b].setLast(s)
      return s
    }
  }

  /// Adds `instruction` at the start of `b` and returns its identity.
  @discardableResult
  public mutating func prepend<T: Instruction>(
    _ instruction: T, to b: IRBlock.ID
  ) -> AnyInstructionIdentity {
    insert(instruction) { (me, i) in
      let a = me.slots.prepend(.init(instruction: i, parent: b))
      let s = AnyInstructionIdentity(address: a)
      me.blocks[b].setFirst(s)
      return s
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

  /// Substitutes `old` for `new`.
  ///
  /// The use chains are updated so that the uses made by `old` are replaced by the uses made by
  /// `new` and all uses of `old` refer to `new`. After the call, `instruction(old) == new`.
  ///
  /// - Requires: The result of `new` has the same type as the result of old.
  internal mutating func replace<T: Instruction>(
    _ old: AnyInstructionIdentity, for new: T
  ) {
    assert(areEqual(at(old).type, new.type))
    removeUses(by: old)
    _ = insert(new) { (me, i) in
      me.slots[old.address].assign(i)
      return old
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
      let n = (i != blocks[b].last) ? slots.address(after: i.address) : nil
      a = n.map(AnyInstructionIdentity.init(address:))
    }
    blocks.remove(at: b)
  }

  /// Removes `i` and updates use chains.
  ///
  /// - Requires: `i` has no users.
  public mutating func remove(_ i: AnyInstructionIdentity) {
    assert(uses[.register(i), default: []].isEmpty)
    removeUses(by: i)

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

    slots.remove(at: i.address)
  }

  /// Removes `i` from the use chains of its operands.
  private mutating func removeUses(by i: AnyInstructionIdentity) {
    for o in at(i).operands {
      uses[o]?.removeAll(where: { $0.user == i })
    }
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
      result.append("\(printer.show(IRValue.parameter(i))): \(printer.show(p.type))")
    }
    result.append(")")

    if case .projection(let t) = self.result {
      result.append(" -> \(printer.show(t))")
    }

    if !slots.isEmpty {
      result.append(" {\n")
      for b in blocks.addresses {
        result.append("%b\(b.rawValue):\n")
        for i in contents(of: b) {
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
      printer.program.debugName(of: d)
    }
  }

}

extension IRBlock {

  /// The contents of a basic block.
  public struct Iterator: IteratorProtocol, Sequence {

    public typealias Element = AnyInstructionIdentity

    /// The instructions containing the subsequence that `self` represents.
    private let slots: List<IRFunction.Slot>

    /// The identity of the next element in `self`, if any.
    private var current: List<IRFunction.Slot>.Address?

    /// The identity of the last element in `self`.
    private let last: List<IRFunction.Slot>.Address?

    /// Creates an instance enumerating the identities of the instructions in `slots` between
    /// `current` and `last`, included.
    fileprivate init(
      slots: List<IRFunction.Slot>, current: AnyInstructionIdentity?, last: AnyInstructionIdentity?
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
