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
  public enum ReturnStyle: Hashable, Sendable {

    /// The result is returned in register.
    case register

    /// The result is projected.
    case projection

  }

  /// The name of the function.
  public let name: Name

  /// The generic type parameters of the function.
  public let typeParameters: [GenericParameter.ID]

  /// The parameters of the function.
  public let termParameters: [IRParameter]

  /// The way in which the function returns its result.
  public let returnStyle: ReturnStyle

  /// The basic blocks in the function, the first of which being the function's entry.
  public private(set) var blocks: List<IRBlock>

  /// The instructions in the function.
  public private(set) var instructions: List<AnyInstruction>

  /// The def-use chains of the values in this function.
  private var uses: [IRValue: [Use]] = [:]

  /// Creates an instance with the given properties.
  public init(
    name: Name, typeParameters: [GenericParameter.ID], termParameters: [IRParameter],
    returnStyle: ReturnStyle
  ) {
    self.name = name
    self.typeParameters = typeParameters
    self.termParameters = termParameters
    self.returnStyle = returnStyle
    self.blocks = []
    self.instructions = []
  }

  /// `true` iff the function has an entry.
  public var isDefined: Bool {
    !blocks.isEmpty
  }

  /// The entry block of `self`.
  public var entry: IRBlock.ID? {
    blocks.firstAddress
  }

  /// Returns the last instruction of `b`, if any.
  public func last(of b: IRBlock.ID) -> AnyInstruction? {
    blocks[b].last.map({ (i) in instructions[i] })
  }

  /// Returns the instructions of `b`.
  public func contents(of b: IRBlock.ID) -> some Sequence<AnyInstructionIdentity> {
    var next = blocks[b].first
    let last = blocks[b].last
    return AnyIterator {
      if let n = next {
        next = (n != last) ? instructions.address(after: n) : nil
        return n
      } else {
        return nil
      }
    }
  }

  /// Returns the register asssigned by `i`, if any.
  public func result(of i: AnyInstructionIdentity) -> IRValue? {
    if instructions[i].type != .nothing {
      return .register(i)
    } else {
      return nil
    }
  }

  /// Returns `true` iff `v` denotes an address.
  public func isAddress(_ v: IRValue) -> Bool {
    type(of: v).map(\.isAddress) ?? false
  }

  /// Returns the type of the value computed by `v` or `nil` if `v` doesn't compute any.
  ///
  /// - Requires: `v` is either a constant or an instruction in this function.
  public func type(of v: IRValue) -> (type: AnyTypeIdentity, isAddress: Bool)? {
    switch v {
    case .parameter(let i):
      return resolved(termParameters[i].type)
    case .register(let i):
      return resolved(instructions[i].type)
    case .word(_, let t):
      return (t.erased, false)
    case .function(_, let t):
      return (t.erased, true)
    }
  }

  /// Returns the type of the value computed without any relative definition.
  ///
  /// - Requires: `v` is either a constant or an isntruction in this function.
  private func resolved(_ t: IRType) -> (type: AnyTypeIdentity, isAddress: Bool)? {
    switch t {
    case .lowered(let u, let isAddress):
      return (u, isAddress)

    case .same(let i):
      return type(of: i)

    case .dereferenced(let i):
      if let (u, isAddress) = type(of: i), isAddress {
        return (u, false)
      } else {
        fatalError("ill-formed IR type")
      }

    case .nothing:
      return nil
    }
  }

  /// Appends a basic block to this function and returns its identity.
  public mutating func addBlock() -> IRBlock.ID {
    blocks.append(.init())
  }

  /// Adds `instruction` at the end of `b` and returns its identity.
  @discardableResult
  public mutating func append<T: Instruction>(
    _ instruction: T, to b: IRBlock.ID
  ) -> AnyInstructionIdentity {
    assert(!(last(of: b)?.isTerminator ?? false), "insertion after terminator")
    return insert(instruction) { (me, i) in
      let id = me.instructions.append(i)
      me.blocks[b].setLast(id)
      return id
    }
  }

  /// Adds `instruction` at the start of `b` and returns its identity.
  @discardableResult
  public mutating func prepend<T: Instruction>(
    _ instruction: T, to b: IRBlock.ID
  ) -> AnyInstructionIdentity {
    insert(instruction) { (me, i) in
      let id = me.instructions.prepend(i)
      me.blocks[b].setFirst(id)
      return id
    }
  }

  /// Inserts `instruction` with `impl` and returns its identity.
  private mutating func insert<T: Instruction>(
    _ instruction: T, with impl: (inout Self, T) -> AnyInstructionIdentity
  ) -> AnyInstructionIdentity {
    // Insert the instruction.
    let user = impl(&self, instruction)

    // Update the def-use chains.
    for i in 0 ..< instruction.operands.count {
      uses[instruction.operands[i], default: []].append(Use(user: user, index: i))
    }

    return user
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

    if !instructions.isEmpty {
      result.append(" {\n")
      for b in blocks.addresses {
        result.append("%b\(b.rawValue):\n")
        for i in contents(of: b) {
          let r = IRValue.register(i)
          result.append("  \(printer.show(r)) = \(instructions[i].show(using: &printer))\n")
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
      printer.program.nameOrTag(of: d)
    }
  }

}
