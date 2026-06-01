import FrontEnd
import Utilities

/// The position of an instruction in the program.
private struct CodePointer {
  /// The module containing `self`.
  var module: Module.ID

  /// The function in `module` indicated by `self`.
  var functionInModule: IRFunction.ID

  /// The position relative to `functionInModule` indicated by `self`.
  var instructionInFunction: AnyInstructionIdentity

}

/// A value manipulated by the IR.
private struct Value {
  /// The underlying type-erased representation of value.
  public var payload: Any
}

/// The value produced by executing an instruction.
private enum InstructionResult {

  /// Produces a value.
  ///
  /// Execution continues at the next instruction in sequence.
  case value(Value)

  /// Transfer control to specific instruction.
  case jump(CodePointer)

}

/// The local variables, parameters, and return address for a function
/// call.
private struct StackFrame {

  /// The results of instructions.
  public var registers: [AnyInstructionIdentity: Value] = [:]

  /// The program counter to which execution should return when
  /// popping this frame.
  public var returnAddress: CodePointer

}

/// A thread's call stack.
private struct Stack {

  /// Local variables, parameters, and return addresses.
  private var frames: [StackFrame] = []

  /// Adds a new frame on top with the given `returnAddress` and `parameters`.
  public mutating func push(returnAddress: CodePointer) {
    let f = StackFrame(returnAddress: returnAddress)
    frames.append(f)
  }

  /// Removes the top frame and returns its `returnAddress`.
  public mutating func pop() -> CodePointer {
    let f = frames.last!
    defer {
      frames.removeLast()
    }
    return f.returnAddress
  }

  /// The top stack frame.
  public var top: StackFrame {
    _read {
      precondition(!isEmpty)
      yield frames[frames.count - 1]
    }
    _modify {
      precondition(!isEmpty)
      yield &frames[frames.count - 1]
    }
  }

  /// Boolean indicating whether stack contains atleast 1 stack frame.
  public var isEmpty: Bool {
    frames.isEmpty
  }

}

/// A virtual machine that executes Hylo's in-memory IR representation.
public struct Interpreter {

  /// The program to be executed.
  private let program: Program

  /// Identity of the next instruction to be executed.
  private var programCounter: CodePointer

  /// True iff the program is still running.
  public private(set) var isRunning: Bool = true

  /// Local variables, parameters and return address.
  private var callStack = Stack()

  /// The top stack frame.
  private var topOfStack: StackFrame {
    _read {
      yield callStack.top
    }
    _modify {
      yield &callStack.top
    }
  }

  /// The instruction at which the program counter points.
  ///
  /// - Precondition: the program is running.
  public var currentInstruction: any Instruction {
    _read {
      yield program[programCounter.module]
        .functions[programCounter.functionInModule]
        .at(programCounter.instructionInFunction)
    }
  }

  /// An instance executing `p`.
  ///
  /// - Precondition: `p.entry != nil`
  public init(_ p: Program) {
    program = p
    let e = program.entry
    let f = program[e.module].functions[e.function]
    let i = f.blocks[f.entry!].first!
    programCounter = .init(
      module: e.module,
      functionInModule: e.function,
      instructionInFunction: i
    )

    // The return address of the bottom-most frame will never be used,
    // so we fill it with something arbitrary.
    callStack.push(returnAddress: programCounter)
  }

  /// Executes a single instruction.
  public mutating func step() throws {
    let r = try stepResult()

    switch r {
    case .value(let v):
      topOfStack.registers[programCounter.instructionInFunction] = v
    case .jump(let pc):
      programCounter = pc
      if callStack.isEmpty {
        isRunning = false
      }
      return
    case nil:
      try advanceProgramCounter()
    }

  }

  /// Executes a single instruction without recording its result.
  private mutating func stepResult() throws -> InstructionResult? {
    print(currentInstruction)
    switch currentInstruction {
    case let x as IRAccess:
      _ = x
    case let x as IRRegionEnd<IRAccess>:
      _ = x
    case let x as IRAlloca:
      _ = x
    case let x as IRAllocx:
      _ = x
    case let x as IRApply:
      _ = x
    case let x as IRApplyBuiltin:
      _ = x
    case let x as IRAssumeState:
      _ = x
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
      return .jump(popStackFrame())
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

  /// Removes topmost stack frame and return code pointer to next instruction of any
  /// previous stack frame.
  ///
  /// - Precondition: the program is running.
  private mutating func popStackFrame() -> CodePointer {
    // precondition(topOfStack.allocations.isEmpty,
    //     "All local variables allocations for function must be deallocated before returning.")
    return callStack.pop()
  }

  /// Moves the program counter to the next instruction.
  mutating func advanceProgramCounter() throws {
    guard
      let i = program[programCounter.module]
        .functions[programCounter.functionInModule]
        .instruction(after: programCounter.instructionInFunction)
    else { throw IRError() }
    programCounter.instructionInFunction = i
  }
}

extension Program {
  /// Entry module and entry function.
  fileprivate var entry: (module: Module.ID, function: IRFunction.ID) {
    let entryModule = identity(module: "Main")!
    let entryFunctionDeclaration = cast(
      select(
        from: entryModule, .and(.tag(FunctionDeclaration.self), .name("main"))
      ).first!, to: FunctionDeclaration.self)!
    let entryFunction = self[entryModule].functions.firstIndex {
      $0.name == IRFunction.Name.lowered(.init(entryFunctionDeclaration))
    }!
    return (module: entryModule, function: entryFunction)
  }
}

/// An indication of malformed IR.
struct IRError: Error {}
