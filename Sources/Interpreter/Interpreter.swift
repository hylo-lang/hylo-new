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
      let p = x.source.asTypedAddress(in: self)
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
      _ = x
    case is IRAssumeState:
      // TODO: add a real implementation, updating state of composed regions.
      return initializeRegister(to: ())
    case let x as IRBranch:
      _ = x
    case let x as IRConditionalBranch:
      _ = x
    case let x as IRGlobalAccess:
      _ = x
    case let x as IRLoad:
      _ = x
    case let x as IRMemoryCopy:
      _ = x
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
      _ = x
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

  /// Stores the value carried by `v` at the location pointed by the address `p`.
  private mutating func store(_ v: IRValue, at p: IRValue) throws {
    try memory.store(v.asRuntimeValue(in: &self), at: p.asAccess(in: self))
  }

}

extension IRValue {

  /// Returns the memory location pointed to by `self` in the current execution
  /// state of `executor`.
  ///
  /// - Precondition: `self` contains a place.
  fileprivate func asTypedAddress(in executor: Interpreter) -> Memory.TypedAddress {
    switch self {
    case .parameter(let i):
      executor.topOfStack.parameters[i].location
    case .register(let r):
      executor.topOfStack.registers[r]!.location!
    default:
      preconditionFailure("\(executor.program.show(self)) is not a Memory.TypedAddress.")
    }
  }

  /// Returns the memory location pointed to by `self`, together with its
  /// permissions and obligations, in the current execution state of `executor`.
  ///
  /// - Precondition: `v` contains a place computed by `access` instruction.
  fileprivate func asAccess(in executor: Interpreter) -> Access<Memory.TypedAddress> {
    switch self {
    case .parameter(let i):
      executor.topOfStack.parameters[i]
    case .register(let r):
      executor.topOfStack.registers[r]!(as: Access<Memory.TypedAddress>.self)!
    default:
      preconditionFailure("\(executor.program.show(self)) is not an Access<Memory.TypedAddress>.")
    }
  }

  /// Returns the value in the interpreted program corresponding to `self` in the
  /// current execution state of `executor`.
  fileprivate func asRuntimeValue(in executor: inout Interpreter) -> RuntimeValue {
    switch self {
    case .register(let r):
      return executor.topOfStack.registers[r]!(as: RuntimeValue.self)!
    case .integer(let n, let t):
      let l = executor.memory.layout(t)
      return .init(integer: n, size: l.size, alignment: l.alignment)
    default:
      preconditionFailure("\(executor.program.show(self)) is not a RuntimeValue.")
    }
  }

  /// Returns the address of part `p` in the address pointed by `self`
  /// in the context of `executor`.
  ///
  /// - Precondition: `self` contains a place.
  fileprivate func location(
    ofPart p: IndexPath,
    in executor: inout Interpreter
  ) -> Memory.TypedAddress {
    let a = asTypedAddress(in: executor)
    return executor.memory.location(p, in: a)
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

/// An indication of malformed IR.
struct IRError: Error {}
