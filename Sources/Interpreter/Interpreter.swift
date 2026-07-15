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
  public var storage: Any
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

  // TODO: add local variables and parameters, which require `Memory`.

  /// The results of instructions.
  public var registers: [AnyInstructionIdentity: Value] = [:]

  /// The next instruction to execute.
  public var currentStep: InstructionPointer

}

/// A thread's call stack.
private struct Stack {

  /// Local variables, parameters, and return addresses.
  private var frames: [StackFrame] = []

  /// Adds a frame for a call to `f`, a nullary function defined in `p`.
  public mutating func enter(_ f: GlobalFunctionIdentity, definedIn p: Program) {
    // TODO: support parameters.
    let s = InstructionPointer(interpreting: f, definedIn: p)
    let f = StackFrame(currentStep: s)
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

  /// The program being executed.
  private let program: Program

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
  private var topOfStack: StackFrame {
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
    program = p
    callStack.enter(p.entry, definedIn: p)
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
    case is IRAccess:
      // TODO: add a real implementation, validating new access in memory and
      // storing the access into register.
      return .initializeRegister(to: .init(storage: ()))
    case is IRRegionEnd<IRAccess>:
      // TODO: add a real implementation, validating if it is safe to end the access.
      return .initializeRegister(to: .init(storage: ()))
    case let x as IRAlloca:
      _ = x
    case let x as IRApply:
      _ = x
    case let x as IRApplyBuiltin:
      _ = x
    case is IRAssumeState:
      // TODO: add a real implementation, updating state of composed regions.
      return .initializeRegister(to: .init(storage: ()))
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
      return .return
    case let x as IRStore:
      _ = x
    case let x as IRSubfield:
      _ = x
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

/// An indication of malformed IR.
struct IRError: Error {}
