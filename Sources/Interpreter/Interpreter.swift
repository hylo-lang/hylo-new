import FrontEnd
import Utilities

/// The position of an instruction in the program.
private struct InstructionPointer {

  /// The function containing the instruction.
  public let container: GlobalFunctionIdentity

  /// The instruction designated by `self`, relative to `container`.
  var position: AnyInstructionIdentity

  /// Creates an instance pointing to `i` in `f`.
  ///
  /// - Precondition: `f` is defined.
  public init(_ i: AnyInstructionIdentity, in f: GlobalFunctionIdentity) {
    container = f
    position = i
  }

  /// Creates an instance pointing to the first instruction of `f`, which is defined in `p`.
  public init(interpreting f: GlobalFunctionIdentity, definedIn p: Program) {
    precondition(p[f.module].functions[f.function].isDefined)
    let i = p.firstInstruction(f)
    self = .init(i, in: f)
  }

}

/// A unique function in a `Program`.
private struct GlobalFunctionIdentity {

  /// The module containing `self`.
  public let module: Module.ID

  /// The function in `module` indicated by `self`.
  public let function: IRFunction.ID

}

extension Program {

  /// Returns the first instruction of `f`.
  ///
  /// - Precondition: `self` is sufficiently lowered for interpretation.
  fileprivate func firstInstruction(_ f: GlobalFunctionIdentity) -> AnyInstructionIdentity {
    let fn = self[f.module].functions[f.function]
    return fn.blocks[fn.entry!].first!
  }

}

/// A value manipulated by the IR.
private struct Value {

  /// The underlying type-erased representation of value.
  private var storage: Any

  /// Creates an instance storing `x`.
  init(_ x: Any) {
    storage = x
  }

  /// The memory location pointed to by `self`, if any.
  public var location: Memory.TypedAddress? {
    if let a = storage as? Access<Memory.TypedAddress> {
      a.location
    } else if let a = storage as? Memory.TypedAddress {
      a
    } else {
      nil
    }
  }

  /// `self` if it is a `T`, or `nil` otherwise.
  public func callAsFunction<T>(as: T.Type) -> T? { storage as? T }

}

/// The part of one instruction's execution that follows any memory and I/O effects.
///
/// Each instruction ends by either initializing a constant register associated
/// with the instruction's address and current stack frame, or transfer control
/// to another instruction.
private enum InstructionEpilogue {

  /// Store
  case initializeRegister(to: Value)

  /// Control is transferred to the given instruction.
  case jump(to: InstructionPointer)

  /// Control is transferred back to the caller.
  case `return`

}

/// The ephemeral (or non-`Memory`) execution state of a function call.
private struct StackFrame {

  /// The allocations in this stack frame.
  var allocations: [Memory.Address] = []

  /// The results of instructions.
  public var registers: [AnyInstructionIdentity: Value] = [:]

  /// The next instruction to execute.
  public var currentStep: InstructionPointer

  /// Location of values passed to the function.
  var parameters: [Access<Memory.TypedAddress>]

}

/// A thread's call stack.
private struct Stack {

  /// Local variables, parameters, and return addresses.
  private var frames: [StackFrame] = []

  /// Adds a frame for a call to `f`, defined in `p`, with parameters `ps`.
  public mutating func enter(
    _ f: GlobalFunctionIdentity,
    definedIn p: Program,
    withParameters ps: [Access<Memory.TypedAddress>]
  ) {
    let s = InstructionPointer(interpreting: f, definedIn: p)
    let f = StackFrame(currentStep: s, parameters: ps)
    frames.append(f)
  }

  /// Removes the top frame.
  public mutating func pop() {
    precondition(!isEmpty)
    frames.removeLast()
  }

  /// The top stack frame.
  public var top: StackFrame {
    get {
      precondition(!isEmpty)
      return frames[frames.count - 1]
    }
    _modify {
      precondition(!isEmpty)
      yield &frames[frames.count - 1]
    }
  }

  /// The depth of call stack.
  public var count: Int {
    frames.count
  }

  /// `true` iff there is at least 1 stack frame.
  public var isEmpty: Bool {
    frames.isEmpty
  }

}

/// A virtual machine that executes Hylo's in-memory IR representation.
public struct Interpreter {

  /// The stack- and dynamically-allocated memory in use.
  fileprivate var memory: Memory

  /// The program being executed.
  fileprivate var program: Program { memory.program }

  /// The next instruction to execute.
  private var programCounter: InstructionPointer {
    get { topOfStack.currentStep }
    set { topOfStack.currentStep = newValue }
  }

  /// `true` iff the program is still running.
  public var isRunning: Bool { !callStack.isEmpty }

  /// Local variables, parameters and return address.
  private var callStack = Stack()

  /// The top stack frame.
  fileprivate private(set) var topOfStack: StackFrame {
    get {
      callStack.top
    }
    _modify {
      yield &callStack.top
    }
  }

  /// The instruction at which the program counter points.
  ///
  /// - Precondition: the program is running.
  public var currentInstruction: any Instruction {
    program[programCounter.container.module]
      .functions[programCounter.container.function]
      .at(programCounter.position)
  }

  /// An instance executing `p`.
  ///
  /// - Precondition: `p.entry != nil`
  public init(_ p: Program) {
    memory = Memory(forRunning: p, on: UnrealABI())

    // `main` takes a `set` access to a `Void` value, so create the
    // corresponding storage and access.
    let l = memory.allocate(storageFor: .void)
    let a = Access(to: l.asTypedAddress(.void), effect: .set)
    callStack.enter(p.entry, definedIn: p, withParameters: [a])
  }

  /// Executes a single instruction.
  public mutating func step() throws {
    switch try applyCurrentInstruction() {
    case .jump(let pc): programCounter = pc
    case .return: callStack.pop()
    case .initializeRegister(let v):
      topOfStack.registers[programCounter.position] = v
      try advanceProgramCounter()
    }
  }

  /// Applies the `Memory` and I/O effects of the current instruction and returns its epilogue.
  private mutating func applyCurrentInstruction() throws -> InstructionEpilogue {
    switch currentInstruction {
    case let x as IRAccess:
      // TODO: add a real implementation, validating new access in memory and
      // storing the access into register.
      let p = address(of: x.source)
      let a = Access(to: p, effect: x.finalCapability)
      return initializeRegister(to: a)
    case is IRRegionEnd<IRAccess>:
      // TODO: add a real implementation, validating if it is safe to end the access.
      return initializeRegister(to: ())
    case let x as IRAlloca:
      if x.witness != nil {
        unimplemented("dynamically sized stack allocation is not supported yet.")
      }
      let p = allocate(storageFor: x.storage)
      return initializeRegister(to: p)
    case let x as IRApply:
      _ = x
    case let x as IRApplyBuiltin:
      let v = try call(x.callee, passing: x.arguments)
      return initializeRegister(to: v)
    case is IRAssumeState:
      // TODO: add a real implementation, updating state of composed regions.
      return initializeRegister(to: ())
    case let x as IRBranch:
      return .jump(to: start(x.target))
    case let x as IRConditionalBranch:
      let c = try self[x.condition].asBool
      if c {
        return .jump(to: start(x.onSuccess))
      } else {
        return .jump(to: start(x.onFailure))
      }
    case let x as IRGlobalAccess:
      _ = x
    case let x as IRLoad:
      let v = try load(from: x.source)
      return initializeRegister(to: v)
    case let x as IRMemoryCopy:
      try copy(x.source, to: x.target)
      return initializeRegister(to: ())
    case let x as IRMove:
      _ = x
    case let x as IRPartialApply:
      _ = x
    case let x as IRPlaceCast:
      _ = x
    case let x as IRProject:
      _ = x
    case let x as IRRegionEnd<IRProject>:
      _ = x
    case let x as IRProperty:
      let l = x.record.location(ofField: x.property, in: &self)
      return initializeRegister(to: l)
    case is IRReturn:
      for a in topOfStack.allocations.reversed() {
        try memory.deallocate(a)
      }
      return .return
    case let x as IRStore:
      try store(x.value, at: x.target)
      return initializeRegister(to: ())
    case let x as IRSubfield:
      let l = x.base.location(ofPart: x.path, in: &self)
      return initializeRegister(to: l)
    case let x as IRTypeApply:
      _ = x
    case let x as IRTypeWitness:
      _ = x
    case let x as IRUnreachable:
      _ = x
    case let x as IRWitnessTable:
      _ = x
    case let x as IRYield:
      _ = x
    default:
      fatalError("Interpreter: unimplemented instruction")
    }
    unreachable("Unimplemented processing of instruction")

  }

  /// Moves the program counter to the next instruction.
  private mutating func advanceProgramCounter() throws {
    guard
      let i = program[programCounter.container.module]
        .functions[programCounter.container.function]
        .instruction(after: programCounter.position)
    else { throw IRError() }
    programCounter.position = i
  }

  /// Returns an epilogue that initializes the instruction's register to `v`.
  private func initializeRegister(to v: Any) -> InstructionEpilogue {
    return .initializeRegister(to: .init(v))
  }

  /// Allocates storage on `callStack` for a value of type `t`, ready to be initialized,
  /// and returns its address.
  ///
  /// - Precondition: `t` is a monomorphic type.
  private mutating func allocate(storageFor t: AnyTypeIdentity) -> Memory.TypedAddress {
    let a = memory.allocate(storageFor: t)
    topOfStack.allocations.append(a)
    return a.asTypedAddress(t)
  }

  /// Returns the value stored at address `p`.
  private mutating func load(from p: IRValue) throws -> RuntimeValue {
    try memory.read(from: access(of: p))
  }

  /// Stores `v` at the address `p`.
  private mutating func store(_ v: IRValue, at p: IRValue) throws {
    try memory.store(self[v], at: access(of: p))
  }

  /// Copies the bytes of object at address `source` to `destination`.
  ///
  /// - Precondition: `source` and `destination` are non-overlapping.
  private mutating func copy(_ source: IRValue, to destination: IRValue) throws {
    let s = access(of: source)
    let d = access(of: destination)
    try memory.copy(s, to: d)
  }

  /// Returns the value corresponding to `v` in the current execution state.
  ///
  /// - Precondition: `v` is a runtime value or a place obtained from an
  ///   access instruction.
  private subscript(_ v: IRValue) -> RuntimeValue {
    mutating get throws {
      switch v {
      case .register(let r):
        if let v = topOfStack.registers[r]!(as: RuntimeValue.self) {
          return v
        }

        if let p = topOfStack.registers[r]!(as: Access<Memory.TypedAddress>.self) {
          return try memory.read(from: p)
        }

        preconditionFailure("\(program.show(v)) is not a RuntimeValue.")
      case .parameter(let i):
        return try memory.read(from: topOfStack.parameters[i])
      case .integer(let n, let t):
        let l = memory.layout(t)
        return .init(integer: n, bitWidth: l.size * 8, alignment: l.alignment)
      default:
        preconditionFailure("\(program.show(v)) is not a RuntimeValue.")
      }
    }
  }

  /// Returns the memory location pointed to by `v` in the current execution context.
  ///
  /// - Precondition: `v` is a place.
  fileprivate func address(of v: IRValue) -> Memory.TypedAddress {
    switch v {
    case .parameter(let i):
      topOfStack.parameters[i].location
    case .register(let r):
      topOfStack.registers[r]!.location!
    default:
      preconditionFailure("\(program.show(v)) is not a Memory.TypedAddress.")
    }
  }

  /// Returns the memory location pointed to by `v`, together with its
  /// permissions and obligations, in the current execution state.
  ///
  /// - Precondition: `v` is a place computed by `access` instruction.
  private func access(of v: IRValue) -> Access<Memory.TypedAddress> {
    switch v {
    case .parameter(let i):
      topOfStack.parameters[i]
    case .register(let r):
      topOfStack.registers[r]!(as: Access<Memory.TypedAddress>.self)!
    default:
      preconditionFailure("\(program.show(v)) is not an Access<Memory.TypedAddress>.")
    }
  }

  /// Returns the pointer to the first instruction of `b`.
  ///
  /// - Precondition: `b` is a basic block in `programCounter.container`.
  private func start(_ b: IRBlock.ID) -> InstructionPointer {
    let m = programCounter.container.module
    let f = programCounter.container.function
    let i = program[m].functions[f].blocks[b].first!
    return .init(i, in: programCounter.container)
  }

  /// Returns the result of calling `f` with `arguments`.
  private mutating func call(
    _ f: BuiltinFunction,
    passing arguments: [IRValue]
  ) throws -> RuntimeValue {
    switch f {
    case .trap: throw Trap()
    case .icmp(let p, let t):
      let w = memory.layout(t).size * 8
      let lhs = try self[arguments[0]]
      let rhs = try self[arguments[1]]
      let r = p(lhs, rhs, bitWidth: w)
      return .init(bool: r)
    case .zeroinitializer(let t):
      let l = memory.layout(t)
      let u = program.types[t]
      return switch u {
      case .i(_): .init(integer: 0, bitWidth: l.size * 8, alignment: l.alignment)
      case .word: .init(integer: 0, bitWidth: l.size * 8, alignment: l.alignment)
      default: unimplemented("zero-initializer is not yet implemented for \(program.show(u)).")
      }
    default: unimplemented("\(program.show(f)) is not implemented yet.")
    }
  }

}

extension IRValue {

  /// Returns the address of part `p` in the address pointed by `self`
  /// in the context of `executor`.
  ///
  /// - Precondition: `self` contains a place.
  fileprivate func location(
    ofPart p: IndexPath,
    in executor: inout Interpreter
  ) -> Memory.TypedAddress {
    let a = executor.address(of: self)
    return executor.memory.location(p, in: a)
  }

  /// Returns the address of field `f` in `self`, in the current execution
  /// state of `executor`.
  ///
  /// - Precondition: `self` contains a place.
  fileprivate func location(
    ofField f: DeclarationIdentity,
    in executor: inout Interpreter
  ) -> Memory.TypedAddress {
    let a = executor.address(of: self)
    let n = executor.program.name(of: f)!.identifier
    return executor.memory.location(ofField: n, in: a)
  }

}

extension Program {
  /// The function whose invocation executes the whole program.
  fileprivate var entry: GlobalFunctionIdentity {
    let entryModule = identity(module: "Main")!
    let entryFunctionDeclaration = cast(
      select(
        from: entryModule, .and(.tag(FunctionDeclaration.self), .name("main"))
      ).first!, to: FunctionDeclaration.self)!
    let entryFunction = self[entryModule].functions.firstIndex {
      $0.name == IRFunction.Name.lowered(.init(entryFunctionDeclaration))
    }!
    return .init(module: entryModule, function: entryFunction)
  }
}

extension IRAccess {

  /// The associated permissions and obligations.
  var finalCapability: AccessEffect {
    // Because IR analysis should ensure single effect.
    // See: Sources/FrontEnd/IR/Instructions/IRAccess.swift.
    capabilities.uniqueElement!
  }

}

extension Interpreter {

  /// An error in `Interpreter`.
  public protocol Error: Swift.Error, Regular {}

  /// A trap occurred during program execution.
  public struct Trap: Error {
    public init() {}
  }

}

/// An indication of malformed IR.
struct IRError: Error {}
