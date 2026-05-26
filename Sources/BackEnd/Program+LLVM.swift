import BigInt
import FrontEnd
import SwiftyLLVM
import Utilities

extension Program {

  // Most methods in this extension accept a `XXXGenerationContext`, which represents the state
  // of the code generation algorithm, threaded to each sub-operation.

  /// Compiles the IR of `m` for target `t`.
  ///
  /// - Requires: `m` has been lowered and all required passes have been run.
  public mutating func compileToLLVM(
    _ m: FrontEnd.Module.ID, target t: consuming TargetMachine
  ) throws -> SwiftyLLVM.Module {
    // var context = CodeGenerationContext(compiling: m)
    let product = SwiftyLLVM.Module(self[m].name, targetMachine: t)
    var context = ModuleGenerationContext(compiling: m, into: product)

    for f in self[m].ir.functions.values.indices {
      incorporate(f, in: &context)
    }

    return context.release()
  }

  /// Declares `f` and, if necessary, compiles its definition into the LLVM module being built.
  private mutating func incorporate(
    _ f: IRFunction.ID, in context: inout ModuleGenerationContext
  ) {
    // Don't compile generic functions.
    if !function(f, in: context).isMonomorphic { return }
    // Don't re-compile functions.
    if !context.compiled.insert(f).inserted { return }

    // Get the declaraiton of LLVM function corresponding to `f`. It is possible that this function
    // has already been declared if it is referred to by some code that was compiled first.
    let result = demandFunction(f, in: &context)
    incorporate(contentsOf: f, into: result, in: &context)

    // If `f` is the module's entry, define a "main" function that just applies it.
    if isEntry(f, of: context.hylo) {
      context.llvm.setLinkage(.private, for: result.llvm)
      defineMain(calling: result, in: &context)
    }
  }

  /// Compiles the contents of `source` into `result`.
  private mutating func incorporate(
    contentsOf source: IRFunction.ID, into result: FunctionMetadata,
    in context: inout ModuleGenerationContext
  ) {
    let ir = function(source, in: context)

    // Nothing to do for functions having no definition.
    guard let entryOfSource = ir.entry else { return }

    // Initialize the code generation context.
    var subcontext = FunctionGenerationContext(compiling: ir, into: result, in: context)
    let e = demandBasicBlock(entryOfSource, in: &subcontext)
    subcontext.insertionPoint = subcontext.module.llvm.endOf(e)

    // Configure the code generation context.
    setupParameterOrReturnValue(result.output, at: result.inputs.count, in: &subcontext)
    for (i, p) in result.inputs.enumerated() {
      setupParameterOrReturnValue(p, at: i, in: &subcontext)
    }

    // Translate the instructions of the Hylo function to LLVM.
    for b in ir.blocks.addresses {
      let v = demandBasicBlock(b, in: &subcontext)
      subcontext.insertionPoint = .some(subcontext.module.llvm.endOf(v))

      var pc = ir.blocks[b].first
      while let i = pc {
        switch ir.tag(of: i) {
        case IRAccess.self:
          incorporate(ir.castUnchecked(i, to: IRAccess.self), in: &subcontext)
        case IRAccess.End.self:
          break
        case IRAlloca.self:
          incorporate(ir.castUnchecked(i, to: IRAlloca.self), in: &subcontext)
        case IRApply.self:
          incorporate(ir.castUnchecked(i, to: IRApply.self), in: &subcontext)
        case IRAssumeState.self:
          break
        case IRMemoryCopy.self:
          incorporate(ir.castUnchecked(i, to: IRMemoryCopy.self), in: &subcontext)
        case IRReturn.self:
          incorporate(ir.castUnchecked(i, to: IRReturn.self), in: &subcontext)
        case IRStore.self:
          incorporate(ir.castUnchecked(i, to: IRStore.self), in: &subcontext)
        case IRSubfield.self:
          incorporate(ir.castUnchecked(i, to: IRSubfield.self), in: &subcontext)
        case let s:
          fatalError("unexpected instruction \(s)")
        }
        pc = ir.instruction(after: i.erased)
      }
    }

    context = subcontext.release()
  }

  /// Configures `context` with so that code generation can handle uses of `p`, which is the `i`-th
  /// parameter of the function being compiled to LLVM.
  ///
  /// This method extends `context.value` so that it maps the representation of `p` in Hylo IR to
  /// its corresponding representation in LLVM IR. There are three cases to handle:
  ///
  /// * `p` has been erased, in which case it should map to a 0-byte alloca.
  /// * `p` is passed by value, in which case it should map to an alloca containing that value.
  /// * `p` is passed by reference, in which case it can be mapped directly.
  ///
  /// Instructions necessary to setup the mapping are inserted at the current entry point, which
  /// is assumed to be in the entry of the function being built.
  private func setupParameterOrReturnValue(
    _ p: FunctionMetadata.Parameter, at i: Int, in context: inout FunctionGenerationContext
  ) {
    let v = FrontEnd.IRValue.parameter(i)

    switch p.convention {
    case .erased:
      // `p` has been erased and can thus be represented by a 0-byte alloca.
      let x = context.module.llvm.insertAlloca(context.module.empty, at: context.insertionPoint!)
      context.value[v] = x.erased

    case .byValue(let j):
      // The argument to `p` is passed by value. Store it into an alloca so that it can be read
      // from memory in subsequent operations. Memory to register promotion (mem2reg) will get rid
      // of needless load/stores later.
      let t = (j >= 0) ? context.result.inputs[j].type : context.result.output.type
      let x = context.module.llvm.insertAlloca(t.llvm, at: context.insertionPoint!)
      context.module.llvm.setAlignment(t.layout.alignment, for: x)
      if j >= 0 {
        context.module.llvm.insertStore(
          context.llvm.unsafe[].parameters[j].erased, to: x, at: context.insertionPoint!)
        // TODO: Alignment
      }
      context.value[v] = x.erased

    case .byReference(let j):
      // The argument to `p` is passed by reference. It is already in memory.
      context.value[v] = context.llvm.unsafe[].parameters[j].erased
    }
  }

  /// Generates the LLVM IR code corresponding to `i`.
  private mutating func incorporate(
    _ i: IRAccess.ID, in context: inout FunctionGenerationContext
  ) {
    let s = context.ir.at(i)
    let v = FrontEnd.IRValue.register(i.erased)
    context.value[v] = context.value[s.source]
  }

  /// Generates the LLVM IR code corresponding to `i`.
  private mutating func incorporate(
    _ i: IRAlloca.ID, in context: inout FunctionGenerationContext
  ) {
    let s = context.ir.at(i)
    let t = metadata(of: s.storage, in: &context.module)
    let x = context.module.llvm.insertAlloca(t.llvm, atEntryOf: context.llvm)
    context.module.llvm.setAlignment(t.layout.alignment, for: x)

    let v = IRValue.register(i.erased)
    context.value[v] = x.erased
  }

  /// Generates the LLVM IR code corresponding to `i`.
  private mutating func incorporate(
    _ i: IRApply.ID, in context: inout FunctionGenerationContext
  ) {
    let s = context.ir.at(i)

    switch s.callee {
    case .function(let n, _, _):
      let callee = demandFunction(n, in: &context.module)

      var arguments: [SwiftyLLVM.AnyValue.UnsafeReference] = []
      for (p, a) in zip(callee.inputs, s.arguments) {
        let l = codegen(a, in: &context)

        switch p.convention {
        case .erased:
          continue
        case .byValue:
          let x = context.module.llvm.insertLoad(p.type.llvm, from: l, at: context.insertionPoint!)
          // TODO: alignment
          arguments.append(x.erased)
        case .byReference:
          arguments.append(l)
        }
      }

      switch callee.output.convention {
      case .erased:
        _ = context.module.llvm.insertCall(
          callee.llvm, on: arguments, at: context.insertionPoint!)

      case .byValue:
        let x = context.module.llvm.insertCall(
          callee.llvm, on: arguments, at: context.insertionPoint!)
        let o = codegen(s.result, in: &context)
        context.module.llvm.insertStore(x, to: o, at: context.insertionPoint!)
        // TODO: Alignment

      case .byReference:
        let o = codegen(s.result, in: &context)
        arguments.append(o)
        _ = context.module.llvm.insertCall(
          callee.llvm, on: arguments, at: context.insertionPoint!)
      }

    default:
      // TODO: Obtain function metadata from other values.
      fatalError()
    }
  }

  /// Generates the LLVM IR code corresponding to `i`.
  private mutating func incorporate(
    _ i: IRMemoryCopy.ID, in context: inout FunctionGenerationContext
  ) {
    let s = context.ir.at(i)
    let t = metadata(of: context.ir.result(of: s.source)!.type, in: &context.module)

    let ptr = context.module.llvm.ptr
    let i32 = context.module.llvm.i32
    let memcpy = context.module.llvm.intrinsic(
      named: IntrinsicFunction.llvm.memcpy, for: [ptr.erased, ptr.erased, i32.erased])!

    let x0 = codegen(s.target, in: &context)
    let x1 = codegen(s.source, in: &context)
    let x2 = i32.unsafe[].constant(t.layout.size)
    let x3 = context.module.llvm.i1.unsafe[].constant(0)
    _ = context.module.llvm.insertCall(
      memcpy, on: [x0.erased, x1.erased, x2.erased, x3.erased],
      at: context.insertionPoint!)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  ///
  /// If the return value of the function being built is passed by output parameter, this method
  /// assumes that this value has already been stored in the memory referred to that parameter it
  /// inserts `ret void`. Otherwise, the return value is loaded from its corresponding alloca
  /// before being returned.
  private mutating func incorporate(
    _ i: IRReturn.ID, in context: inout FunctionGenerationContext
  ) {
    switch context.result.output.convention {
    case .erased, .byReference:
      context.module.llvm.insertReturn(at: context.insertionPoint!)

    case .byValue:
      let t = context.result.output.type.llvm
      let x = context.value[context.ir.returnRegister!]!
      let y = context.module.llvm.insertLoad(t, from: x, at: context.insertionPoint!)
      // TODO: alignment
      context.module.llvm.insertReturn(y, at: context.insertionPoint!)
    }
  }

  /// Generates the LLVM IR code corresponding to `i`.
  private mutating func incorporate(
    _ i: IRStore.ID, in context: inout FunctionGenerationContext
  ) {
    let s = context.ir.at(i)
    let x = codegen(s.value, in: &context)
    let y = context.value[s.target]!
    // TODO: alignment
    context.module.llvm.insertStore(x, to: y, at: context.insertionPoint!)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  private mutating func incorporate(
    _ i: IRSubfield.ID, in context: inout FunctionGenerationContext
  ) {
    let s = context.ir.at(i)
    let t = context.ir.result(of: s.base)!.type

    let i32 = context.module.llvm.i32
    var indices = [i32.unsafe[].constant(0).erased]
    var u = t
    for p in s.path {
      let m = metadata(of: u, in: &context.module)
      indices.append(i32.unsafe[].constant(m.layout.propertyToField[p]).erased)
      u = storage(of: u, visibleFrom: context.module.hylo)![p]
    }

    let b = context.value[s.base]!
    let m = metadata(of: t, in: &context.module)
    let x = context.module.llvm.insertGetElementPointerInBounds(
      of: b, typed: m.llvm, indices: indices, at: context.insertionPoint!)

    let v = IRValue.register(i.erased)
    context.value[v] = x.erased
  }

  /// Returns the LLVM function corresponding to `f`, declaring it if necessary.
  ///
  /// - Requires: `f` does not implement a subscript.
  private mutating func demandFunction(
    _ f: IRFunction.ID, in context: inout ModuleGenerationContext
  ) -> FunctionMetadata {
    let ir = function(f, in: context)
    let name = llvmName(of: f, in: context)
    let signature = ir.signature()
    let maxFootprint = context.llvm.layout.pointerSize

    // There should be no subscript at this point.
    precondition(signature.head.style == .parenthesized, "unexpected subscript during codegen")

    var parameters: [SwiftyLLVM.AnyType.UnsafeReference] = []
    var inputs: [FunctionMetadata.Parameter] = .init(
      minimumCapacity: signature.head.inputs.count + 1)
    for p in signature.head.inputs {
      let t = metadata(of: p.type, in: &context)

      // Parameters of size 0 are simply ignored.
      if t.layout.size == 0 {
        inputs.append(.init(type: t, convention: .erased))
      }

      // `let` and `sink` with a small footprint are passed into registers. Other parameters are
      // passed by reference.
      else if (t.layout.size <= maxFootprint) && AccessEffectSet.functional.contains(p.access) {
        inputs.append(.init(type: t, convention: .byValue(parameters.count)))
        parameters.append(t.llvm)
      } else {
        inputs.append(.init(type: t, convention: .byReference(parameters.count)))
        parameters.append(context.llvm.ptr.erased)
      }
    }

    let o = metadata(of: signature.head.output, in: &context)

    // Can the result be erased?
    if o.layout.size == 0 {
      let t = context.llvm.functionType(from: parameters)
      let v = context.llvm.declareFunction(name, t)
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: o, convention: .erased))
    }

    // Can the result be returned by value?
    else if o.layout.size <= maxFootprint {
      let t = context.llvm.functionType(from: parameters, to: o.llvm)
      let v = context.llvm.declareFunction(name, t)
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: o, convention: .byValue(-1)))
    }

    // The result is returned by output parameter.
    else {
      let t = context.llvm.functionType(from: parameters + [o.llvm])
      let v = context.llvm.declareFunction(name, t)
      let n = parameters.count
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: o, convention: .byReference(n)))
    }
  }

  /// Returns the LLVM basic block corresponding to `b`, creating it if necessary.
  private mutating func demandBasicBlock(
    _ b: IRBlock.ID, in context: inout FunctionGenerationContext
  ) -> SwiftyLLVM.BasicBlock.UnsafeReference {
    if let r = context.block[b] {
      return r
    } else {
      let v = context.module.llvm.appendBlock(to: context.llvm)
      context.block[b] = v
      return v
    }
  }

  /// Defines a "main" function calling `f`, which is the module's entry point.
  ///
  /// This method creates a function named "main" acting as a program entry point. This function
  /// wraps a call to `f`, which represents the entry point of an executable Hylo module, and
  /// returns the exit status of the program.
  ///
  /// `f` is a function linked privately in the module, taking no parameter and returning either
  /// `Hylo.Int32` or `Hylo.Void`. In the former case, the main function returns the result of `f`.
  /// Otherwise, it returns 0. Note that `f` may terminate the execution of the program before
  /// returning to the main function (e.g., due to a trap).
  private mutating func defineMain(
    calling f: FunctionMetadata, in context: inout ModuleGenerationContext
  ) {
    let i32 = context.llvm.i32
    let m = context.llvm.declareFunction("main", context.llvm.functionType(from: [], to: i32))
    let e = context.llvm.appendBlock(to: m)
    let p = context.llvm.endOf(e)
    let r = context.llvm.insertCall(f.llvm, on: [], at: p)

    // `f` returns an exit status iff its return type has a non-zero size, in which case we can
    // assume it is an instance of `Hylo.Int32`.
    if f.output.type.layout.size > 0 {
      let v = context.llvm.insertExtractValue(from: r, at: 0, at: p)
      context.llvm.insertReturn(v, at: p)
    } else {
      context.llvm.insertReturn(i32.unsafe[].zero, at: p)
    }
  }

  /// Returns the value of the Hylo function identified by `f`.
  private func function(
    _ f: IRFunction.ID, in context: borrowing ModuleGenerationContext
  ) -> IRFunction {
    self[context.hylo].ir[f]
  }

  /// Returns the name of the function corresponding to `f` in LLVM IR.
  private func llvmName(
    of f: IRFunction.ID, in context: borrowing ModuleGenerationContext
  ) -> String {
    let v = function(f, in: context).name
    if case .lowered(let d) = v, let n = externName(of: d) {
      return n
    } else {
      return mangled(f, of: context.hylo)
    }
  }

  /// Returns the representation of `v` in LLVM IR.
  private mutating func codegen(
    _ v: FrontEnd.IRValue, in context: inout FunctionGenerationContext
  ) -> SwiftyLLVM.AnyValue.UnsafeReference {
    switch v {
    case .integer(let n, let t):
      return codegen(integer: n, instanceOf: t, in: &context.module)
    case .register:
      return context.value[v]!
    default:
      fatalError("no LLVM representation of type '\(show(v))'")
    }
  }

  /// Returns a LLVM IR constant equivalent to `n`, which is an instance of an integer type `t`.
  private mutating func codegen(
    integer n: BigInt, instanceOf t: MachineType.ID, in context: inout ModuleGenerationContext
  ) -> SwiftyLLVM.AnyValue.UnsafeReference {
    let u = metadata(of: t, in: &context)
    let v = IntegerType.UnsafeReference(u.llvm)!.unsafe[]
      .constant(words: n.words.map({ (i) in UInt64(i) }))
    return v.erased
  }

  /// Returns the LLVM type corresponding to the Hylo type `t`, using `compute` to determine its
  /// properties if necessary.
  ///
  /// `compute` accepts projections of this method's arguments along with the mangled name of `t`,
  /// and it returns the metadata of `t`. This result is memoized and returned for all subsequent
  /// calls to this method with the same type and context.
  private mutating func metadata<T: TypeIdentity>(
    of t: T, in context: inout ModuleGenerationContext,
    computedWith compute: (inout Self, inout ModuleGenerationContext, T, String) -> TypeMetadata
  ) -> TypeMetadata {
    let n = mangled(t)
    if let memoized = context.typeMetadata[n] {
      return memoized
    } else {
      let result = compute(&self, &context, t, n)
      context.typeMetadata[n] = result
      return result
    }
  }

  /// Returns the LLVM type corresponding of the Hylo type `t`.
  private mutating func metadata(
    of t: AnyTypeIdentity, in context: inout ModuleGenerationContext
  ) -> TypeMetadata {
    switch types.tag(of: t) {
    case MachineType.self:
      metadata(of: types.castUnchecked(t, to: MachineType.self), in: &context)
    case Struct.self:
      metadata(of: types.castUnchecked(t, to: Struct.self), in: &context)
    case Tuple.self:
      metadata(of: types.castUnchecked(t, to: Tuple.self), in: &context)
    default:
      unimplemented("no LLVM representation of type '\(show(t))'")
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: MachineType.ID, in context: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &context) { (program, ctx, t, n) in
      let v = switch program.types[t] {
      case .i(let width):
        ctx.llvm.integerType(Int(width)).erased
      case .word:
        ctx.llvm.iptr.erased
      case .ptr:
        ctx.llvm.ptr.erased
      default:
        unimplemented("no LLVM representation of type '\(program.show(t))'")
      }

      let s = ctx.llvm.layout.storageSize(of: v)
      let a = ctx.llvm.layout.preferredAlignment(of: v)
      let l = ConcreteLayout(fields: [], propertyToField: [], size: s, alignment: a)
      return TypeMetadata(llvm: v, layout: l)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Struct.ID, in context: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &context) { (program, ctx, t, n) in
      // TODO: Resilience
      let m = program.types[t].declaration.module
      let properties = program.storage(of: t.erased, visibleFrom: m)!
      return program.metadata(record: n, rows: properties, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Tuple.ID, in context: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &context) { (program, ctx, t, n) in
      let (properties, isOpenEnded) = program.types.members(of: t)
      precondition(!isOpenEnded, "no LLVM representation of type '\(program.show(t))'")
      return program.metadata(record: n, rows: properties, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of a record type having the given name and rows.
  private mutating func metadata(
    record name: String, rows: [AnyTypeIdentity], in context: inout ModuleGenerationContext
  ) -> TypeMetadata {
    let layout = record(rows: rows, in: &context)
    let definition = context.llvm.structType(named: name, layout.fields, packed: true).erased

    assert(context.llvm.layout.storageSize(of: definition) <= layout.size)
    assert(context.llvm.layout.abiAlignment(of: definition) <= layout.alignment)
    return TypeMetadata(llvm: definition, layout: layout)
  }

  /// Returns the standard layout of a record type having the given rows.
  private mutating func record(
    rows: [AnyTypeIdentity], in context: inout ModuleGenerationContext
  ) -> ConcreteLayout {
    let rs = rows.map({ (u) in metadata(of: u, in: &context) })
    let ps = rows.indices.sorted { (a, b) in
      let lhs = rs[a].layout.alignment
      let rhs = rs[b].layout.alignment
      return (rhs < lhs) || ((lhs == rhs) && (a < b))
    }

    var fields: [SwiftyLLVM.AnyType.UnsafeReference] = []
    var rowToField = Array(repeating: -1, count: rs.count)
    var size = 0

    for p in ps where rs[p].layout.size > 0 {
      // There should be no need for padding bits.
      assert(size.rounded(upToNearestMultipleOf: rs[p].layout.alignment) == size)

      rowToField[p] = fields.count
      fields.append(rs[p].llvm)
      size += rs[p].layout.size
    }

    let a = rs.last?.layout.alignment ?? 1
    return ConcreteLayout(fields: fields, propertyToField: rowToField, size: size, alignment: a)
  }

}
