import FrontEnd
import SwiftyLLVM

/// This file implements the bulk of the logic related to "subscript decomposition", which is a
/// transformation governing the compilation of subscripts and subscript calls.
///
/// Subscripts are compiled into a "ramp" and `n` "slides", where `n` is the number of `yield`
/// instructions occurring in the subscript. The ramp implements the part of the subscript that
/// computes the value being projected. Its interface is the same as an ordinary function except
/// that it does not return any value. Instead, it accepts two extra parameters representing a
/// closure, called a "plateau", that abstracts over the way callers may use the projected value.
/// A slide implements the code following one specific `yield` point. It is expected to be called
/// by the pleateau, once the value being projected is no longer used. Pointers to values defined
/// in a ramp that are used in a slide are stored into a local array that is piped through the
/// plateau. These values are identified conservatively by enumerating the definitions that
/// dominate the `yield` instruction corresponding of a specific slide.
///
/// A similar transformation occurs at the call site to form plateaus. One complication is that
/// subscript applications may overlap without nesting. This issue is addressed by using the set
/// of all basic blocks dominated by a `project` instruction to form a plateau rather than trying
/// to keep it small, in a manner reminiscent of continuation passing style. This strategy ensures
/// that all definitions formed within the lifetime of a projection and used after, including other
/// projections, are covered by the plateau corresponding to that projection. Further, because code
/// following a loop is not dominated by that loop's body, this strategy also ensures that values
/// used in a loop do not accumulate on the stack, unlike with traditional continuation passing.
///
/// Since a plateau does not always contain the entire continuation of a subscript application, it
/// must also specify where control-flow is transferred when the subscript eventually returns. To
/// that end, the plateau returns an integer identifying a basic block in the caller that is used
/// as the scrutinee of a switch instruction.

/// Information about the definitions that dominate a region of a Hylo IR function.
fileprivate struct RegionPrologue {

  /// The instruction at the start of the region of which `self` is the prologue.
  ///
  /// This property identifies either a `project` or a `yield` instruction. The prologue is defined
  /// for a plateau in the former case and for a slide otherwise.
  fileprivate let boundary: FrontEnd.AnyInstructionIdentity

  /// How the parameters of the Hylo IR function are mapped.
  fileprivate let inputs: [Prototype.Parameter]

  /// The definitions dominating the region.
  fileprivate let definitions: [FrontEnd.IRValue]

  /// The indices of the elements of `definitions` that should be captured in frames and plateaus.
  fileprivate let captures: [Int]

  /// The type of the data structure storing the captures made by this prologue.
  fileprivate let captureFrame: SwiftyLLVM.StructType.UnsafeReference

  /// Returns the index of `d` in the array of captures made by this prologue.
  fileprivate func captureIndex(of d: FrontEnd.IRValue) -> Int? {
    captures.firstIndex(where: { (c) in definitions[c] == d })
  }

}

extension FunctionGenerationContext {

  /// Returns the parameters and definitions that dominate `y`, which is an instruction in the
  /// function being compiled.
  ///
  /// The result is a collection composed of the parameters of the function being compiled along
  /// with all instructions that dominate `y`. These values must be defined by the time `y` is
  /// evaluated, on any code path. The collection is ordered so that, for each element `v`, all
  /// uses of `v` are defined by an element occurring before `v`.
  fileprivate mutating func prologue(dominating y: AnyInstructionIdentity) -> RegionPrologue {
    let definingBlock = ir.block(defining: y)
    var definitions: [FrontEnd.IRValue] = []

    // Collect non-erased parameters.
    let prototype = module.functionMetadata[ir.name]!.prototype
    for (i, p) in prototype.mapping.inputs.enumerated() where p.convention != .erased {
      definitions.append(.parameter(i))
    }
    if let r = ir.returnRegister {
      definitions.append(r)
    }

    // All non-erased parameters are captured.
    var captures = Array(definitions.indices)

    // Collect dominating instructions and determine those that are captured.
    for b in dominance.dominators(of: definingBlock).reversed() {
      for i in ir.instructions(in: b) {
        // Nothing more to collect from `y`.
        if i == y { break }

        switch ir.relevanceInSlideOrPlateau(i) {
        case .captured:
          captures.append(definitions.count)
          definitions.append(.register(i))

        case .redefined:
          definitions.append(.register(i))

        case .none:
          continue
        }
      }
    }

    let t = startsProjectionInRamp(y) ? module.plateauCallback.t : module.empty.t
    let u = module.llvm.arrayType(captures.count, module.llvm.ptr).t
    let v = module.llvm.structType([t, u])
    return .init(
      boundary: y, inputs: result.prototype.mapping.inputs, definitions: definitions,
      captures: captures, captureFrame: v)
  }

  /// Returns `true` iff `y` is starts a projection in a ramp.
  private func startsProjectionInRamp(_ y: FrontEnd.AnyInstructionIdentity) -> Bool {
    (ir.tag(of: y) == IRProject.self) && result.isRamp
  }

  /// Allocates a buffer of pointers, initialized with the values of all captures in `prologue`.
  fileprivate mutating func saveCaptures(_ prologue: RegionPrologue) -> LLVMValue {
    let frame = module.llvm.insertAlloca(prologue.captureFrame, atEntryOf: llvm).v

    // If the prologue is that of a projection called from a ramp, allocate extra storage to
    // capture the plateau and its environment *before* other definitions.
    if startsProjectionInRamp(prologue.boundary) {
      var v = module.llvm.poisonValue(of: module.plateauCallback.t).v
      if result.isPlateau {
        let (f, e) = insertExtractPlateau()
        v = module.llvm.insertInsertValue(f, at: 0, into: v, at: insertionPoint!).v
        v = module.llvm.insertInsertValue(e, at: 1, into: v, at: insertionPoint!).v
      } else {
        let ps = llvm.unsafe[].parameters
        v = module.llvm.insertInsertValue(ps[toLast: 1].v, at: 0, into: v, at: insertionPoint!).v
        v = module.llvm.insertInsertValue(ps[toLast: 0].v, at: 1, into: v, at: insertionPoint!).v
      }
      let x = module.llvm.insertGetStructElementPointer(
        of: frame, typed: prologue.captureFrame, index: 0, at: insertionPoint!)
      module.llvm.insertStore(v, to: x, at: insertionPoint!)
    }

    // Store captured definitions.
    for (i, c) in prologue.captures.enumerated() {
      let d = prologue.definitions[c]
      let x = module.llvm.insertGetElementPointerInBounds(
        of: frame, typed: prologue.captureFrame, indices: [0, 1, i], indexType: module.llvm.i32,
        at: insertionPoint!)
      if isBareProject(d) {
        saveBareProject(to: x)
      } else {
        module.llvm.insertStore(value[d]!, to: x, at: insertionPoint!)
      }
    }

    return frame
  }

  /// Returns `true` iff  `d` is a `project` instruction represented in the parameters of the
  /// function being compiled, which is a plateau.
  private func isBareProject(_ d: FrontEnd.IRValue) -> Bool {
    if let i = d.register, ir.tag(of: i) == IRProject.self {
      return value[d] == llvm.unsafe[].parameters.first?.v
    } else {
      return false
    }
  }

  /// Stores to `slot` the address of a triple describing arguments of the plateau being compiled
  /// that relate to the projection associated with that plateau.
  ///
  /// `slot` is a pointer to a pointer. This method assigns the pointee to the address of a triple
  /// allocated on the stack, which is initialized with the addresses of the projected value, the
  /// corresponding slide, and its environment.
  private mutating func saveBareProject(
    to slot: SwiftyLLVM.AnyInstruction.UnsafeReference
  ) {
    let parameters = llvm.unsafe[].parameters
    let project = module.llvm.insertAlloca(module.nestedProject, atEntryOf: llvm)

    var v = module.llvm.poisonValue(of: module.nestedProject).v
    v = module.llvm.insertInsertValue(parameters[0], at: 0, into: v, at: insertionPoint!).v
    v = module.llvm.insertInsertValue(parameters[2], at: 1, into: v, at: insertionPoint!).v
    v = module.llvm.insertInsertValue(parameters[3], at: 2, into: v, at: insertionPoint!).v
    module.llvm.insertStore(v, to: project, at: insertionPoint!)
    module.llvm.insertStore(project, to: slot, at: insertionPoint!)
  }

  /// Returns the first instruction in `b` that is strictly dominated by `y`.
  ///
  /// Let `a` be the block defining `y`. If `a` is equal to `b`, then the result is the instruction
  /// immediately after `y` in the same block, unless there is none. If `a` is different from `b`,
  /// `b` is dominated by `a` and the result is the first instruction in `b`, unless there is none.
  fileprivate func firstInstruction<T: InstructionIdentity>(
    in b: IRBlock.ID, dominatedBy y: T
  ) -> AnyInstructionIdentity? {
    if b == ir.block(defining: y) {
      return ir.instruction(after: y.erased)
    } else {
      return ir.blocks[b].first
    }
  }

}

extension Program {

  /// Returns the closure implementing the slide starting immediately after `y`.
  ///
  /// The result is a pair `(f, e)` where `f` is a lifted closure and `e` is its environment. The
  /// implementation of `f` includes all possible code paths starting from `y`.
  internal mutating func defineSlide(
    dominatedBy y: IRYield.ID, in ctx: inout FunctionGenerationContext
  ) -> (FunctionMetadata, LLVMValue) {
    let name = IRFunction.Name.slide(ctx.ir.name, ctx.ir.block(defining: y).rawValue)
    let n = mangled(name)
    let f = ctx.module.llvm.declareFunction(n, ctx.module.slide)
    let u = metadata(of: .void, in: &ctx.module)

    let m = Prototype.Mapping(inputs: [], output: .init(type: u, convention: .erased))
    let p = Prototype(signature: FunctionType.UnsafeReference(f.unsafe[].valueType)!, mapping: m)
    let slide = FunctionMetadata(prototype: p, value: f, isRamp: false)
    ctx.module.llvm.setLinkage(.private, for: slide.value)

    // Save pointers to the parameters and allocations dominating `y`.
    let prologue = ctx.prologue(dominating: y.erased)
    let captures = ctx.saveCaptures(prologue)

    incorporateContentsOfSlide(
      dominatedBy: prologue, from: ctx.ir, into: slide, queryingDominanceWith: ctx.dominance,
      in: &ctx.module)
    return (slide, captures)
  }

  /// Compiles into `result` the contents of the slide starting immediately after `prologue`, which
  /// is an instruction in `source` dominated by all the definitions in `prologue`.
  ///
  /// The contents of `source` that are compiled into `result` includes all instructions sequenced
  /// after `prologue.boundary`.
  ///
  /// - Parameters:
  ///   - prologue: The region dominating part of `source` that is incorporated.
  ///   - source: The Hylo function whose contents is being compiled.
  ///   - result: The declaration of a slide whose body has not been defined yet.
  ///   - dominance: the dominator tree of `source`.
  private mutating func incorporateContentsOfSlide(
    dominatedBy prologue: RegionPrologue, from source: IRFunction, into result: FunctionMetadata,
    queryingDominanceWith dominance: DominatorTree,
    in ctx: inout ModuleGenerationContext
  ) {
    let entryInSource = source.block(defining: prologue.boundary)

    // Initialize the code generation context.
    var nested = FunctionGenerationContext(
      compiling: source, within: dominance, into: result, in: ctx)
    let slideEntry = nested.demandBasicBlock(entryInSource)
    nested.insertionPoint = nested.module.llvm.endOf(slideEntry)

    let p = nested.llvm.unsafe[].parameters[0]
    setupDominatingDefinitions(prologue, capturedIn: p, inRamp: false, in: &nested)

    let reachable = nested.ir.blocks(reachableFrom: entryInSource)
    for b in nested.dominance where reachable.contains(b) && !nested.factoredOut.contains(b) {
      let i = nested.firstInstruction(in: b, dominatedBy: prologue.boundary)!
      incorporate(from: i, in: &nested)
    }

    ctx = nested.release()
  }

  /// Returns the closure implementing the plateau starting immediately after `y`.
  ///
  /// The result is a triple `(f, e, c)` where `f` is a lifted closure, `e` is its environment, and
  /// `c` is the set of basic blocks whose contents have been compiled into `f`.
  internal mutating func definePlateau(
    dominatedBy y: IRProject.ID, in ctx: inout FunctionGenerationContext
  ) -> (FunctionMetadata, LLVMValue, IRBlockSet) {
    let name = IRFunction.Name.plateau(ctx.ir.name, y.erased.address.rawValue)
    let n = mangled(name)
    let f = ctx.module.llvm.declareFunction(n, ctx.module.plateau)

    let m = Prototype.Mapping(inputs: [], output: nil)
    let p = Prototype(signature: FunctionType.UnsafeReference(f.unsafe[].valueType)!, mapping: m)
    let plateau = FunctionMetadata(prototype: p, value: f, isRamp: ctx.result.isRamp)
    ctx.module.llvm.setLinkage(.private, for: plateau.value)

    // Save pointers to the parameters and allocations dominating `y`.
    let prologue = ctx.prologue(dominating: y.erased)
    let captures = ctx.saveCaptures(prologue)

    let covered = incorporateContentsOfPlateau(
      dominatedBy: prologue, inRamp: ctx.result.isRamp, from: ctx.ir, into: plateau,
      queryingDominanceWith: ctx.dominance,
      in: &ctx.module)
    ctx.factoredOut.formUnion(covered)

    return (plateau, captures, covered)
  }

  /// Compiles into `result` the contents of the plateau starting immediately after `prologue`,
  /// which is an instruction in `source` dominated by all the definitions in `prologue`.
  ///
  /// The contents of `source` that are compiled into `result` includes all instructions sequenced
  /// after `prologue.boundary`.
  ///
  /// - Parameters:
  ///   - prologue: The region dominating part of `source` that is incorporated.
  ///   - isRamp: `true` iff the prologue is that of a projection called from a ramp.
  ///   - source: The Hylo function whose contents is being compiled.
  ///   - result: The declaration of a plateau whose body has not been defined yet.
  ///   - dominance: The dominator tree of `source`.
  /// - Returns: The set of basic blocks whose contents have been incorporated.
  private mutating func incorporateContentsOfPlateau(
    dominatedBy prologue: RegionPrologue, inRamp isRamp: Bool,
    from source: IRFunction, into result: FunctionMetadata,
    queryingDominanceWith dominance: DominatorTree,
    in ctx: inout ModuleGenerationContext
  ) -> IRBlockSet {
    let entryInSource = source.block(defining: prologue.boundary)

    // Initialize the code generation context.
    var nested = FunctionGenerationContext(
      compiling: source, within: dominance, into: result, in: ctx)
    let slideEntry = nested.demandBasicBlock(entryInSource)
    nested.insertionPoint = nested.module.llvm.endOf(slideEntry)

    let v = IRValue.register(prologue.boundary.erased)
    nested.value[v] = nested.llvm.unsafe[].parameters[0].v
    let p = nested.llvm.unsafe[].parameters[1]
    setupDominatingDefinitions(prologue, capturedIn: p, inRamp: isRamp, in: &nested)

    var covered = IRBlockSet()
    var coveredYield = false
    var work = nested.dominance.region(dominatedBy: entryInSource)
    while let b = work.next() {
      if nested.factoredOut.contains(b) { continue }

      let v = nested.demandBasicBlock(b)
      nested.insertionPoint = nested.module.llvm.endOf(v)

      var next = nested.firstInstruction(in: b, dominatedBy: prologue.boundary)
      while let i = next {
        next = incorporate(i, dominatedBy: prologue, in: &nested)
      }

      covered.insert(b)
      coveredYield = coveredYield || source.contains(in: b, IRYield.self)
    }

    ctx = nested.release()

    // If a yield statement was covered, then all blocks reachable from the boundary have been
    // covered in the silde following that statement.
    if coveredYield {
      return source.blocks(reachableFrom: entryInSource)
    } else {
      return covered
    }
  }

  /// Generates the LLVM IR code corresponding to `i`, which is the end of a projection occurring
  /// in the plateau dominated by `p`.
  private mutating func incorporate(
    _ i: AnyInstructionIdentity, dominatedBy p: RegionPrologue,
    in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    func cast<T: Instruction>(_: T.Type) -> T.ID { ctx.ir.castUnchecked(i) }

    switch ctx.ir.tag(of: i) {
    case IRBranch.self:
      return incorporate(cast(IRBranch.self), dominatedBy: p, in: &ctx)
    case IRConditionalBranch.self:
      return incorporate(cast(IRConditionalBranch.self), dominatedBy: p, in: &ctx)
    case IRProject.End.self:
      return incorporate(cast(IRProject.End.self), dominatedBy: p, in: &ctx)
    case IRReturn.self:
      return incorporate(cast(IRReturn.self), dominatedBy: p, in: &ctx)
    default:
      return incorporate(i, in: &ctx)
    }
  }

  /// Generates the LLVM IR code corresponding to `i`, which is the end of a projection occurring
  /// in the plateau dominated by `p`.
  private mutating func incorporate(
    _ i: IRBranch.ID, dominatedBy p: RegionPrologue,
    in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    if ctx.dominance.dominates(ctx.ir.block(defining: p.boundary), s.target) {
      return incorporate(i, in: &ctx)
    } else {
      let t = ctx.module.llvm.i32
      let v = t.unsafe[].constant(s.target.rawValue)
      ctx.module.llvm.insertReturn(v, at: ctx.insertionPoint!)
      return nil
    }
  }

  /// Generates the LLVM IR code corresponding to `i`, which is the end of a projection occurring
  /// in the plateau dominated by `p`.
  private mutating func incorporate(
    _ i: IRConditionalBranch.ID, dominatedBy p: RegionPrologue,
    in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    _ = incorporate(i, in: &ctx)

    let s = ctx.ir.at(i)
    let a = ctx.demandBasicBlock(s.onSuccess)
    let b = ctx.demandBasicBlock(s.onFailure)
    let t = ctx.module.llvm.i32

    if !ctx.dominance.dominates(ctx.ir.block(defining: p.boundary), s.onSuccess) {
      let v = t.unsafe[].constant(s.onSuccess.rawValue)
      ctx.module.llvm.insertReturn(v, at: ctx.module.llvm.endOf(a))
    }
    if !ctx.dominance.dominates(ctx.ir.block(defining: p.boundary), s.onFailure) {
      let v = t.unsafe[].constant(s.onFailure.rawValue)
      ctx.module.llvm.insertReturn(v, at: ctx.module.llvm.endOf(b))
    }
    return nil
  }

  /// Generates the LLVM IR code corresponding to `i`, which is the end of a projection occurring
  /// in the plateau dominated by `p`.
  private func incorporate(
    _ i: IRProject.End.ID, dominatedBy p: RegionPrologue,
    in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    func insertCall(_ f: LLVMValue, _ e: LLVMValue) {
      _ = ctx.module.llvm.insertCall(
        f, typed: ctx.module.slide.t, on: [e],
        at: ctx.insertionPoint!)
    }

    let s = ctx.ir.at(i)

    // Is the start of the projection at the top of the plateau?
    if case .register(p.boundary) = s.start {
      let f = ctx.llvm.unsafe[].parameters[2]
      let e = ctx.llvm.unsafe[].parameters[3]
      insertCall(f.v, e.v)
    }

    // The start of the projection has been captured.
    else if let c = p.captureIndex(of: s.start) {
      let x0 = ctx.llvm.unsafe[].parameters[1]
      let x1 = ctx.module.llvm.insertGetElementPointerInBounds(
        of: x0, typed: p.captureFrame, indices: [0, 1, c], indexType: ctx.module.llvm.i32,
        at: ctx.insertionPoint!)
      let x2 = ctx.module.llvm.insertLoad(
        ctx.module.llvm.ptr.t, from: x1.v,
        at: ctx.insertionPoint!)
      let x3 = ctx.module.llvm.insertLoad(
        ctx.module.nestedProject, from: x2,
        at: ctx.insertionPoint!)
      let f = ctx.module.llvm.insertExtractValue(from: x3, at: 1, at: ctx.insertionPoint!)
      let e = ctx.module.llvm.insertExtractValue(from: x3, at: 2, at: ctx.insertionPoint!)
      insertCall(f.v, e.v)
    }

    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`, which is the end of a projection occurring
  /// in the plateau dominated by `p`.
  private func incorporate(
    _ i: IRReturn.ID, dominatedBy p: RegionPrologue,
    in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let zero = ctx.module.llvm.i32.unsafe[].constant(0)
    ctx.module.llvm.insertReturn(zero, at: ctx.insertionPoint!)
    return nil
  }

  /// Extends `ctx` to map each dominating definition in `prologue` to its value in `captures`,
  /// which is the environment of the lifted lambda being compiled.
  ///
  /// `isRamp` is `true` iff the prologue is that of a projection called from a ramp.
  private mutating func setupDominatingDefinitions(
    _ prologue: RegionPrologue, capturedIn captures: SwiftyLLVM.Parameter.UnsafeReference,
    inRamp isRamp: Bool,
    in ctx: inout FunctionGenerationContext
  ) {
    let ptr = ctx.module.llvm.ptr

    // The captures are stored in an array referred to by the slide's first parameter. This array
    // can be used to define the context in which the instructions of the slide are compiled.
    if !prologue.captures.isEmpty {
      let x0 = ctx.module.llvm.insertGetElementPointerInBounds(
        of: captures, typed: prologue.captureFrame,
        indices: [0, 1], indexType: ctx.module.llvm.i32,
        at: ctx.insertionPoint!)
      let x1 = ctx.module.llvm.insertLoad(
        prologue.captureFrame.unsafe[].fields[1], from: x0, at: ctx.insertionPoint!)

      for (i, c) in prologue.captures.enumerated() {
        let d = prologue.definitions[c]
        let v = ctx.module.llvm.insertExtractValue(from: x1, at: i, at: ctx.insertionPoint!)

        // If the capture is a project, the i-th position of the captures is a pointer to a triple
        // containing a pointer to the projected value along with the corresponding slide.
        if let i = d.register, ctx.ir.tag(of: i) == IRProject.self {
          let u0 = ctx.module.llvm.insertGetStructElementPointer(
            of: v, typed: ctx.module.nestedProject, index: 0, at: ctx.insertionPoint!)
          let u1 = ctx.module.llvm.insertLoad(ptr, from: u0, at: ctx.insertionPoint!)
          ctx.value[d] = u1.v
        }

        // Otherwise, the i-th position is a pointer to the capture.
        else { ctx.value[d] = v.v }
      }
    }

    // Erased parameters must be redefined.
    for i in prologue.inputs.indices where prologue.inputs[i].convention == .erased {
      let x = ctx.module.llvm.insertAlloca(ctx.module.empty, at: ctx.insertionPoint!)
      ctx.value[.parameter(i)] = x.v
    }

    // Other dominating definitions may have to be redefined as well.
    for v in prologue.definitions {
      guard let i = v.register else { continue }
      switch ctx.ir.tag(of: i) {
      case IRAlloca.self, IRProject.self:
        assert(ctx.value[v] != nil, "instruction should have been redefined")
      default:
        _ = incorporate(i, in: &ctx)
      }
    }
  }

}

extension IRFunction {

  /// How relevant is an instruction defined in a prologue for compiling the region that it
  /// dominates in a different function.
  fileprivate enum InstructionRelevance {

    /// The instruction defines a value that should be captured.
    case captured

    /// The instruction defines a value that should be redefined.
    case redefined

    /// The instruction can be ignored.
    case none

  }

  /// Returns the relevance of `i`, which is an instruction in the prologue of a slide or plateau.
  fileprivate func relevanceInSlideOrPlateau(_ i: AnyInstructionIdentity) -> InstructionRelevance {
    switch tag(of: i) {
    case IRAlloca.self, IRProject.self:
      return .captured
    case IRAccess.self, IRGlobalAccess.self, IRPlaceCast.self, IRSubfield.self:
      return .redefined
    default:
      return .none
    }
  }

}
