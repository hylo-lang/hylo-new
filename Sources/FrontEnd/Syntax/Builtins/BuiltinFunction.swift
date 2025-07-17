import Archivist

/// A function in the `Builtin` module.
///
/// Built-in functions implement the basis operations on machine types such as `Builtin.i64`, and
/// are implemented by a single IR instruction.
///
/// Only a few built-in functions, such as `Builtin.address(of:)`, are truly generic. Others are
/// parameterized by a bounded selection of types and flags, resulting in a family *non-generic*
/// Hylo functions having the same base name. The full name of these functions is a concatenation
/// of the base name with the value of each parameter separated by underscores. For example,
/// `Builtin.add_i32` and `Builtin.add_i64` denote integer addition for 32-bit and 64-bit machine
/// integer values, respectively.
///
/// Some flags have default values (e.g., `OverflowBehavior.ignored`), which are omitted from
/// builtin function names. For example:
///
/// | Hylo spelling               | Swift representation     |
/// |:----------------------------|:-------------------------|
/// | `Builtin.add_i64`           | `.add(.ignored, .i(64))` |
/// | `Builtin.icmp_ne_i32`       | `.icmp(.ne, .i(32))`     |
/// | `Builtin.fmul_fast_float64` | `.fmul(.fast, .float64)` |
///
/// Most built-in functions have the same semantics as the LLVM instruction having the same base
/// name. Other cases have documentation describing their semantics and Hylo signature. Supported
/// LLVM operations include all arithmetic and comparison instructions on built-in integral and
/// floating-point numbers as well as conversions from and to these types.
@Archivable
public enum BuiltinFunction: Hashable, Sendable {

  // MARK: Functions unique to Hylo

  /// Stops the execution of the program.
  ///
  /// This function abstracts over the `trap` instruction of the target.
  case trap

  /// `Builtin.address<T>(of v: T) -> Builtin.ptr`
  ///
  /// Returns a pointer to the storage of the argument.
  ///
  /// The resulting pointer is dereferenceable only for the lifetime of the argument; additional
  /// measures may be needed to keep the argument alive during the pointer's use.
  case addressOf

  /// `Builtin.mark_uninitialized<T>(_ v: sink T) -> Void`
  ///
  /// Marks `v` as being uninitialized.
  case markUninitialized

  // MARK: Functions with a counterpart LLVM instruction.

  case add(OverflowBehavior, MachineType.ID)

  case sub(OverflowBehavior, MachineType.ID)

  case mul(OverflowBehavior, MachineType.ID)

  //  case shl(OverflowBehavior, MachineType.ID)
  //
  //  case udiv(exact: Bool, MachineType.ID)
  //
  //  case sdiv(exact: Bool, MachineType.ID)
  //
  //  case lshr(exact: Bool, MachineType.ID)
  //
  //  case ashr(exact: Bool, MachineType.ID)
  //
  //  case urem(MachineType.ID)
  //
  //  case srem(MachineType.ID)

  case and(MachineType.ID)

  case or(MachineType.ID)

  case xor(MachineType.ID)

  /// In LLVM: `sadd.with.overflow`
  case signedAdditionWithOverflow(MachineType.ID)

  /// In LLVM: `uadd.with.overflow`
  case unsignedAdditionWithOverflow(MachineType.ID)

  /// In LLVM: `ssub.with.overflow`
  case signedSubtractionWithOverflow(MachineType.ID)

  /// In LLVM: `usub.with.overflow`
  case unsignedSubtractionWithOverflow(MachineType.ID)

  /// In LLVM: `smul.with.overflow`
  case signedMultiplicationWithOverflow(MachineType.ID)

  /// In LLVM: `umul.with.overflow`
  case unsignedMultiplicationWithOverflow(MachineType.ID)

  case icmp(IntegerPredicate, MachineType.ID)

  //  case trunc(MachineType.ID, MachineType.ID)
  //
  //  case zext(MachineType.ID, MachineType.ID)
  //
  //  case sext(MachineType.ID, MachineType.ID)
  //
  //  case uitofp(MachineType.ID, MachineType.ID)
  //
  //  case sitofp(MachineType.ID, MachineType.ID)
  //
  //  case inttoptr(MachineType.ID)
  //
  //  case ptrtoint(MachineType.ID)
  //
  //  case fadd(MathFlags, MachineType.ID)
  //
  //  case fsub(MathFlags, MachineType.ID)
  //
  //  case fmul(MathFlags, MachineType.ID)
  //
  //  case fdiv(MathFlags, MachineType.ID)
  //
  //  case frem(MathFlags, MachineType.ID)
  //
  //  case fcmp(MathFlags, FloatingPointPredicate, MachineType.ID)
  //
  //  case fptrunc(MachineType.ID, MachineType.ID)
  //
  //  case fpext(MachineType.ID, MachineType.ID)
  //
  //  case fptoui(MachineType.ID, MachineType.ID)
  //
  //  case fptosi(MachineType.ID, MachineType.ID)
  //
  //  case ctpop(MachineType.ID)
  //
  //  case ctlz(MachineType.ID)
  //
  //  case cttz(MachineType.ID)

  case zeroinitializer(MachineType.ID)

  //  // Corresponding LLVM instruction: get_elementptr_inbounds.
  //  case advancedByBytes(byteOffset: MachineType.ID)
  //
  //  case atomic_store_relaxed(MachineType.ID)
  //
  //  case atomic_store_release(MachineType.ID)
  //
  //  case atomic_store_seqcst(MachineType.ID)
  //
  //  case atomic_load_relaxed(MachineType.ID)
  //
  //  case atomic_load_acquire(MachineType.ID)
  //
  //  case atomic_load_seqcst(MachineType.ID)
  //
  //  case atomic_swap_relaxed(MachineType.ID)
  //
  //  case atomic_swap_acquire(MachineType.ID)
  //
  //  case atomic_swap_release(MachineType.ID)
  //
  //  case atomic_swap_acqrel(MachineType.ID)
  //
  //  case atomic_swap_seqcst(MachineType.ID)
  //
  //  case atomic_add_relaxed(MachineType.ID)
  //
  //  case atomic_add_acquire(MachineType.ID)
  //
  //  case atomic_add_release(MachineType.ID)
  //
  //  case atomic_add_acqrel(MachineType.ID)
  //
  //  case atomic_add_seqcst(MachineType.ID)
  //
  //  case atomic_fadd_relaxed(MachineType.ID)
  //
  //  case atomic_fadd_acquire(MachineType.ID)
  //
  //  case atomic_fadd_release(MachineType.ID)
  //
  //  case atomic_fadd_acqrel(MachineType.ID)
  //
  //  case atomic_fadd_seqcst(MachineType.ID)
  //
  //  case atomic_sub_relaxed(MachineType.ID)
  //
  //  case atomic_sub_acquire(MachineType.ID)
  //
  //  case atomic_sub_release(MachineType.ID)
  //
  //  case atomic_sub_acqrel(MachineType.ID)
  //
  //  case atomic_sub_seqcst(MachineType.ID)
  //
  //  case atomic_fsub_relaxed(MachineType.ID)
  //
  //  case atomic_fsub_acquire(MachineType.ID)
  //
  //  case atomic_fsub_release(MachineType.ID)
  //
  //  case atomic_fsub_acqrel(MachineType.ID)
  //
  //  case atomic_fsub_seqcst(MachineType.ID)
  //
  //  case atomic_max_relaxed(MachineType.ID)
  //
  //  case atomic_max_acquire(MachineType.ID)
  //
  //  case atomic_max_release(MachineType.ID)
  //
  //  case atomic_max_acqrel(MachineType.ID)
  //
  //  case atomic_max_seqcst(MachineType.ID)
  //
  //  case atomic_umax_relaxed(MachineType.ID)
  //
  //  case atomic_umax_acquire(MachineType.ID)
  //
  //  case atomic_umax_release(MachineType.ID)
  //
  //  case atomic_umax_acqrel(MachineType.ID)
  //
  //  case atomic_umax_seqcst(MachineType.ID)
  //
  //  case atomic_fmax_relaxed(MachineType.ID)
  //
  //  case atomic_fmax_acquire(MachineType.ID)
  //
  //  case atomic_fmax_release(MachineType.ID)
  //
  //  case atomic_fmax_acqrel(MachineType.ID)
  //
  //  case atomic_fmax_seqcst(MachineType.ID)
  //
  //  case atomic_min_relaxed(MachineType.ID)
  //
  //  case atomic_min_acquire(MachineType.ID)
  //
  //  case atomic_min_release(MachineType.ID)
  //
  //  case atomic_min_acqrel(MachineType.ID)
  //
  //  case atomic_min_seqcst(MachineType.ID)
  //
  //  case atomic_umin_relaxed(MachineType.ID)
  //
  //  case atomic_umin_acquire(MachineType.ID)
  //
  //  case atomic_umin_release(MachineType.ID)
  //
  //  case atomic_umin_acqrel(MachineType.ID)
  //
  //  case atomic_umin_seqcst(MachineType.ID)
  //
  //  case atomic_fmin_relaxed(MachineType.ID)
  //
  //  case atomic_fmin_acquire(MachineType.ID)
  //
  //  case atomic_fmin_release(MachineType.ID)
  //
  //  case atomic_fmin_acqrel(MachineType.ID)
  //
  //  case atomic_fmin_seqcst(MachineType.ID)
  //
  //  case atomic_and_relaxed(MachineType.ID)
  //
  //  case atomic_and_acquire(MachineType.ID)
  //
  //  case atomic_and_release(MachineType.ID)
  //
  //  case atomic_and_acqrel(MachineType.ID)
  //
  //  case atomic_and_seqcst(MachineType.ID)
  //
  //  case atomic_nand_relaxed(MachineType.ID)
  //
  //  case atomic_nand_acquire(MachineType.ID)
  //
  //  case atomic_nand_release(MachineType.ID)
  //
  //  case atomic_nand_acqrel(MachineType.ID)
  //
  //  case atomic_nand_seqcst(MachineType.ID)
  //
  //  case atomic_or_relaxed(MachineType.ID)
  //
  //  case atomic_or_acquire(MachineType.ID)
  //
  //  case atomic_or_release(MachineType.ID)
  //
  //  case atomic_or_acqrel(MachineType.ID)
  //
  //  case atomic_or_seqcst(MachineType.ID)
  //
  //  case atomic_xor_relaxed(MachineType.ID)
  //
  //  case atomic_xor_acquire(MachineType.ID)
  //
  //  case atomic_xor_release(MachineType.ID)
  //
  //  case atomic_xor_acqrel(MachineType.ID)
  //
  //  case atomic_xor_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchg_relaxed_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchg_relaxed_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchg_relaxed_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchg_acquire_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchg_acquire_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchg_acquire_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchg_release_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchg_release_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchg_release_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchg_acqrel_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchg_acqrel_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchg_acqrel_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchg_seqcst_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchg_seqcst_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchg_seqcst_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_relaxed_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_relaxed_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_relaxed_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_acquire_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_acquire_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_acquire_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_release_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_release_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_release_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_acqrel_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_acqrel_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_acqrel_seqcst(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_seqcst_relaxed(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_seqcst_acquire(MachineType.ID)
  //
  //  case atomic_cmpxchgweak_seqcst_seqcst(MachineType.ID)
  //
  //  case atomic_fence_acquire
  //
  //  case atomic_fence_release
  //
  //  case atomic_fence_acqrel
  //
  //  case atomic_fence_seqcst
  //
  //  case atomic_singlethreadfence_acquire
  //
  //  case atomic_singlethreadfence_release
  //
  //  case atomic_singlethreadfence_acqrel
  //
  //  case atomic_singlethreadfence_seqcst

}

extension BuiltinFunction {

  /// Returns the type of the function, calling `freshVariable` to create fresh type variables.
  public func type(uniquingTypesWith s: inout TypeStore) -> Arrow.ID {
    let i1 = s.demand(MachineType.i(1))

    switch self {
    case .trap:
      let t0 = s.never().erased
      return s.demand(Arrow(inputs: [], output: t0))

    case .addressOf:
      let t0 = s.fresh().erased
      let t1 = s.demand(RemoteType(projectee: t0, access: .let)).erased
      let t2 = s.demand(MachineType.ptr).erased
      return s.demand(Arrow(inputs: [.init(label: "of", access: .let, type: t1)], output: t2))

    case .markUninitialized:
      let t0 = s.fresh().erased
      return s.demand(Arrow(inputs: [.init(label: nil, access: .sink, type: t0)], output: .void))

    case .add(_, let t):
      return s.demand(Arrow(t, t, to: t))
    case .sub(_, let t):
      return s.demand(Arrow(t, t, to: t))
    case .mul(_, let t):
      return s.demand(Arrow(t, t, to: t))
    //    case .shl(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .udiv(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .sdiv(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .lshr(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .ashr(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .urem(let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .srem(let t):
    //      return .init(^t, ^t, to: ^t)
    case .and(let t):
      return s.demand(Arrow(t, t, to: t))
    case .or(let t):
      return s.demand(Arrow(t, t, to: t))
    case .xor(let t):
      return s.demand(Arrow(t, t, to: t))
    case .signedAdditionWithOverflow(let t):
      let u = s.demand(Tuple(t.erased, i1.erased))
      return s.demand(Arrow(t, t, to: u))
    case .unsignedAdditionWithOverflow(let t):
      let u = s.demand(Tuple(t.erased, i1.erased))
      return s.demand(Arrow(t, t, to: u))
    case .signedSubtractionWithOverflow(let t):
      let u = s.demand(Tuple(t.erased, i1.erased))
      return s.demand(Arrow(t, t, to: u))
    case .unsignedSubtractionWithOverflow(let t):
      let u = s.demand(Tuple(t.erased, i1.erased))
      return s.demand(Arrow(t, t, to: u))
    case .signedMultiplicationWithOverflow(let t):
      let u = s.demand(Tuple(t.erased, i1.erased))
      return s.demand(Arrow(t, t, to: u))
    case .unsignedMultiplicationWithOverflow(let t):
      let u = s.demand(Tuple(t.erased, i1.erased))
      return s.demand(Arrow(t, t, to: u))
    case .icmp(_, let t):
      return s.demand(Arrow(t, t, to: i1))
    //    case .trunc(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .zext(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .sext(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .uitofp(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .sitofp(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .inttoptr(let t):
    //      return .init(^t, to: .builtin(.ptr))
    //    case .ptrtoint(let t):
    //      return .init(.builtin(.ptr), to: ^t)
    //    case .fadd(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .fsub(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .fmul(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .fdiv(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .frem(_, let t):
    //      return .init(^t, ^t, to: ^t)
    //    case .fcmp(_, _, let t):
    //      return .init(^t, ^t, to: .builtin(.i(1)))
    //    case .fptrunc(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .fpext(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .fptoui(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .fptosi(let s, let d):
    //      return .init(^s, to: ^d)
    //    case .ctpop(let t):
    //      return .init(^t, to: ^t)
    //    case .ctlz(let t):
    //      return .init(^t, to: ^t)
    //    case .cttz(let t):
    //      return .init(^t, to: ^t)
    case .zeroinitializer(let t):
      return s.demand(Arrow(inputs: [], output: t.erased))
    //    case .advancedByBytes(let byteOffset):
    //      return .init(.builtin(.ptr), ^byteOffset, to: .builtin(.ptr))
    //    case .atomic_store_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: .void)
    //    case .atomic_store_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: .void)
    //    case .atomic_store_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: .void)
    //    case .atomic_load_relaxed(let t):
    //      return .init(.builtin(.ptr), to: ^t)
    //    case .atomic_load_acquire(let t):
    //      return .init(.builtin(.ptr), to: ^t)
    //    case .atomic_load_seqcst(let t):
    //      return .init(.builtin(.ptr), to: ^t)
    //    case .atomic_swap_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_swap_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_swap_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_swap_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_swap_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_add_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_add_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_add_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_add_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_add_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fadd_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fadd_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fadd_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fadd_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fadd_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_sub_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_sub_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_sub_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_sub_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_sub_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fsub_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fsub_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fsub_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fsub_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fsub_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_max_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_max_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_max_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_max_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_max_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umax_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umax_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umax_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umax_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umax_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmax_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmax_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmax_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmax_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmax_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_min_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_min_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_min_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_min_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_min_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umin_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umin_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umin_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umin_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_umin_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmin_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmin_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmin_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmin_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_fmin_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_and_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_and_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_and_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_and_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_and_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_nand_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_nand_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_nand_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_nand_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_nand_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_or_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_or_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_or_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_or_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_or_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_xor_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_xor_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_xor_release(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_xor_acqrel(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_xor_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, to: ^t)
    //    case .atomic_cmpxchg_relaxed_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_relaxed_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_relaxed_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_acquire_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_acquire_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_acquire_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_release_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_release_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_release_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_acqrel_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_acqrel_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_acqrel_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_seqcst_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_seqcst_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchg_seqcst_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_relaxed_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_relaxed_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_relaxed_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_acquire_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_acquire_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_acquire_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_release_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_release_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_release_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_acqrel_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_acqrel_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_acqrel_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_seqcst_relaxed(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_seqcst_acquire(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_cmpxchgweak_seqcst_seqcst(let t):
    //      return .init(.builtin(.ptr), ^t, ^t, to: ^TupleType(types: [^t, .builtin(.i(1))]))
    //    case .atomic_fence_acquire:
    //      return .init(to: .void)
    //    case .atomic_fence_release:
    //      return .init(to: .void)
    //    case .atomic_fence_acqrel:
    //      return .init(to: .void)
    //    case .atomic_fence_seqcst:
    //      return .init(to: .void)
    //    case .atomic_singlethreadfence_acquire:
    //      return .init(to: .void)
    //    case .atomic_singlethreadfence_release:
    //      return .init(to: .void)
    //    case .atomic_singlethreadfence_acqrel:
    //      return .init(to: .void)
    //    case .atomic_singlethreadfence_seqcst:
    //      return .init(to: .void)
    }
  }

}

extension BuiltinFunction: Showable {

  /// Returns the part of the name of this function that comes before the parentheses.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .trap:
      return "trap"
    case .addressOf:
      return "address"
    case .markUninitialized:
      return "mark_uninitialized"
    case .add(let p, let t):
      return printer.format((p != .ignore) ? "add_\(p)_%T" : "add_%T", [t.erased])
    case .sub(let p, let t):
      return printer.format((p != .ignore) ? "sub_\(p)_%T" : "sub_%T", [t.erased])
    case .mul(let p, let t):
      return printer.format((p != .ignore) ? "mul_\(p)_%T" : "mul_%T", [t.erased])
    //    case .shl(let p, let t):
    //      return (p != .ignore) ? "shl_\(p)_\(t)" : "shl_\(t)"
    //    case .udiv(let e, let t):
    //      return e ? "udiv_exact_\(t)" : "udiv_\(t)"
    //    case .sdiv(let e, let t):
    //      return e ? "sdiv_exact_\(t)" : "sdiv_\(t)"
    //    case .lshr(let e, let t):
    //      return e ? "lshr_exact_\(t)" : "lshr_\(t)"
    //    case .ashr(let e, let t):
    //      return e ? "ashr_exact_\(t)" : "ashr_\(t)"
    //    case .urem(let t):
    //      return "urem_\(t)"
    //    case .srem(let t):
    //      return "srem_\(t)"
    case .and(let t):
      return printer.format("and_%T", [t.erased])
    case .or(let t):
      return printer.format("or_%T", [t.erased])
    case .xor(let t):
      return printer.format("xor_%T", [t.erased])
    case .signedAdditionWithOverflow(let t):
      return printer.format("sadd_with_overflow_%T", [t.erased])
    case .unsignedAdditionWithOverflow(let t):
      return printer.format("uadd_with_overflow_%T", [t.erased])
    case .signedSubtractionWithOverflow(let t):
      return printer.format("ssub_with_overflow_%T", [t.erased])
    case .unsignedSubtractionWithOverflow(let t):
      return printer.format("usub_with_overflow_%T", [t.erased])
    case .signedMultiplicationWithOverflow(let t):
      return printer.format("smul_with_overflow_%T", [t.erased])
    case .unsignedMultiplicationWithOverflow(let t):
      return printer.format("umul_with_overflow_%T", [t.erased])
    case .icmp(let p, let t):
      return printer.format("icmp_\(p)_%T", [t.erased])
    //    case .trunc(let l, let r):
    //      return "trunc_\(l)_\(r)"
    //    case .zext(let l, let r):
    //      return "zext_\(l)_\(r)"
    //    case .sext(let l, let r):
    //      return "sext_\(l)_\(r)"
    //    case .uitofp(let l, let r):
    //      return "uitofp_\(l)_\(r)"
    //    case .sitofp(let l, let r):
    //      return "sitofp_\(l)_\(r)"
    //    case .inttoptr(let t):
    //      return "inttoptr_\(t)"
    //    case .ptrtoint(let t):
    //      return "ptrtoint_\(t)"
    //    case .fadd(let f, let t):
    //      return f.isEmpty ? "fadd_\(t)" : "fadd_\(f)_\(t)"
    //    case .fsub(let f, let t):
    //      return f.isEmpty ? "fsub_\(t)" : "fsub_\(f)_\(t)"
    //    case .fmul(let f, let t):
    //      return f.isEmpty ? "fmul_\(t)" : "fmul_\(f)_\(t)"
    //    case .fdiv(let f, let t):
    //      return f.isEmpty ? "fdiv_\(t)" : "fdiv_\(f)_\(t)"
    //    case .frem(let f, let t):
    //      return f.isEmpty ? "frem_\(t)" : "frem_\(f)_\(t)"
    //    case .fcmp(let f, let p, let t):
    //      return f.isEmpty ? "fcmp_\(p)_\(t)" : "fcmp_\(f)_\(p)_\(t)"
    //    case .fptrunc(let l, let r):
    //      return "fptrunc_\(l)_\(r)"
    //    case .fpext(let l, let r):
    //      return "fpext_\(l)_\(r)"
    //    case .fptoui(let l, let r):
    //      return "fptoui_\(l)_\(r)"
    //    case .fptosi(let l, let r):
    //      return "fptosi_\(l)_\(r)"
    //    case .ctpop(let t):
    //      return "ctpop_\(t)"
    //    case .ctlz(let t):
    //      return "ctlz_\(t)"
    //    case .cttz(let t):
    //      return "cttz_\(t)"
    case .zeroinitializer(let t):
      return printer.format("zeroinitializer_%T", [t.erased])
    //    case .advancedByBytes(let t):
    //      return "advanced_by_bytes_\(t)"
    //    case .atomic_store_relaxed(let t):
    //      return "atomic_store_relaxed_\(t)"
    //    case .atomic_store_release(let t):
    //      return "atomic_store_release_\(t)"
    //    case .atomic_store_seqcst(let t):
    //      return "atomic_store_seqcst_\(t)"
    //    case .atomic_load_relaxed(let t):
    //      return "atomic_load_relaxed_\(t)"
    //    case .atomic_load_acquire(let t):
    //      return "atomic_load_acquire_\(t)"
    //    case .atomic_load_seqcst(let t):
    //      return "atomic_load_seqcst_\(t)"
    //    case .atomic_swap_relaxed(let t):
    //      return "atomic_swap_relaxed_\(t)"
    //    case .atomic_swap_acquire(let t):
    //      return "atomic_swap_acquire_\(t)"
    //    case .atomic_swap_release(let t):
    //      return "atomic_swap_release_\(t)"
    //    case .atomic_swap_acqrel(let t):
    //      return "atomic_swap_acqrel_\(t)"
    //    case .atomic_swap_seqcst(let t):
    //      return "atomic_swap_seqcst_\(t)"
    //    case .atomic_add_relaxed(let t):
    //      return "atomic_add_relaxed_\(t)"
    //    case .atomic_add_acquire(let t):
    //      return "atomic_add_acquire_\(t)"
    //    case .atomic_add_release(let t):
    //      return "atomic_add_release_\(t)"
    //    case .atomic_add_acqrel(let t):
    //      return "atomic_add_acqrel_\(t)"
    //    case .atomic_add_seqcst(let t):
    //      return "atomic_add_seqcst_\(t)"
    //    case .atomic_fadd_relaxed(let t):
    //      return "atomic_fadd_relaxed_\(t)"
    //    case .atomic_fadd_acquire(let t):
    //      return "atomic_fadd_acquire_\(t)"
    //    case .atomic_fadd_release(let t):
    //      return "atomic_fadd_release_\(t)"
    //    case .atomic_fadd_acqrel(let t):
    //      return "atomic_fadd_acqrel_\(t)"
    //    case .atomic_fadd_seqcst(let t):
    //      return "atomic_fadd_seqcst_\(t)"
    //    case .atomic_sub_relaxed(let t):
    //      return "atomic_sub_relaxed_\(t)"
    //    case .atomic_sub_acquire(let t):
    //      return "atomic_sub_acquire_\(t)"
    //    case .atomic_sub_release(let t):
    //      return "atomic_sub_release_\(t)"
    //    case .atomic_sub_acqrel(let t):
    //      return "atomic_sub_acqrel_\(t)"
    //    case .atomic_sub_seqcst(let t):
    //      return "atomic_sub_seqcst_\(t)"
    //    case .atomic_fsub_relaxed(let t):
    //      return "atomic_fsub_relaxed_\(t)"
    //    case .atomic_fsub_acquire(let t):
    //      return "atomic_fsub_acquire_\(t)"
    //    case .atomic_fsub_release(let t):
    //      return "atomic_fsub_release_\(t)"
    //    case .atomic_fsub_acqrel(let t):
    //      return "atomic_fsub_acqrel_\(t)"
    //    case .atomic_fsub_seqcst(let t):
    //      return "atomic_fsub_seqcst_\(t)"
    //    case .atomic_max_relaxed(let t):
    //      return "atomic_max_relaxed_\(t)"
    //    case .atomic_max_acquire(let t):
    //      return "atomic_max_acquire_\(t)"
    //    case .atomic_max_release(let t):
    //      return "atomic_max_release_\(t)"
    //    case .atomic_max_acqrel(let t):
    //      return "atomic_max_acqrel_\(t)"
    //    case .atomic_max_seqcst(let t):
    //      return "atomic_max_seqcst_\(t)"
    //    case .atomic_umax_relaxed(let t):
    //      return "atomic_umax_relaxed_\(t)"
    //    case .atomic_umax_acquire(let t):
    //      return "atomic_umax_acquire_\(t)"
    //    case .atomic_umax_release(let t):
    //      return "atomic_umax_release_\(t)"
    //    case .atomic_umax_acqrel(let t):
    //      return "atomic_umax_acqrel_\(t)"
    //    case .atomic_umax_seqcst(let t):
    //      return "atomic_umax_seqcst_\(t)"
    //    case .atomic_fmax_relaxed(let t):
    //      return "atomic_fmax_relaxed_\(t)"
    //    case .atomic_fmax_acquire(let t):
    //      return "atomic_fmax_acquire_\(t)"
    //    case .atomic_fmax_release(let t):
    //      return "atomic_fmax_release_\(t)"
    //    case .atomic_fmax_acqrel(let t):
    //      return "atomic_fmax_acqrel_\(t)"
    //    case .atomic_fmax_seqcst(let t):
    //      return "atomic_fmax_seqcst_\(t)"
    //    case .atomic_min_relaxed(let t):
    //      return "atomic_min_relaxed_\(t)"
    //    case .atomic_min_acquire(let t):
    //      return "atomic_min_acquire_\(t)"
    //    case .atomic_min_release(let t):
    //      return "atomic_min_release_\(t)"
    //    case .atomic_min_acqrel(let t):
    //      return "atomic_min_acqrel_\(t)"
    //    case .atomic_min_seqcst(let t):
    //      return "atomic_min_seqcst_\(t)"
    //    case .atomic_umin_relaxed(let t):
    //      return "atomic_umin_relaxed_\(t)"
    //    case .atomic_umin_acquire(let t):
    //      return "atomic_umin_acquire_\(t)"
    //    case .atomic_umin_release(let t):
    //      return "atomic_umin_release_\(t)"
    //    case .atomic_umin_acqrel(let t):
    //      return "atomic_umin_acqrel_\(t)"
    //    case .atomic_umin_seqcst(let t):
    //      return "atomic_umin_seqcst_\(t)"
    //    case .atomic_fmin_relaxed(let t):
    //      return "atomic_fmin_relaxed_\(t)"
    //    case .atomic_fmin_acquire(let t):
    //      return "atomic_fmin_acquire_\(t)"
    //    case .atomic_fmin_release(let t):
    //      return "atomic_fmin_release_\(t)"
    //    case .atomic_fmin_acqrel(let t):
    //      return "atomic_fmin_acqrel_\(t)"
    //    case .atomic_fmin_seqcst(let t):
    //      return "atomic_fmin_seqcst_\(t)"
    //    case .atomic_and_relaxed(let t):
    //      return "atomic_and_relaxed_\(t)"
    //    case .atomic_and_acquire(let t):
    //      return "atomic_and_acquire_\(t)"
    //    case .atomic_and_release(let t):
    //      return "atomic_and_release_\(t)"
    //    case .atomic_and_acqrel(let t):
    //      return "atomic_and_acqrel_\(t)"
    //    case .atomic_and_seqcst(let t):
    //      return "atomic_and_seqcst_\(t)"
    //    case .atomic_nand_relaxed(let t):
    //      return "atomic_nand_relaxed_\(t)"
    //    case .atomic_nand_acquire(let t):
    //      return "atomic_nand_acquire_\(t)"
    //    case .atomic_nand_release(let t):
    //      return "atomic_nand_release_\(t)"
    //    case .atomic_nand_acqrel(let t):
    //      return "atomic_nand_acqrel_\(t)"
    //    case .atomic_nand_seqcst(let t):
    //      return "atomic_nand_seqcst_\(t)"
    //    case .atomic_or_relaxed(let t):
    //      return "atomic_or_relaxed_\(t)"
    //    case .atomic_or_acquire(let t):
    //      return "atomic_or_acquire_\(t)"
    //    case .atomic_or_release(let t):
    //      return "atomic_or_release_\(t)"
    //    case .atomic_or_acqrel(let t):
    //      return "atomic_or_acqrel_\(t)"
    //    case .atomic_or_seqcst(let t):
    //      return "atomic_or_seqcst_\(t)"
    //    case .atomic_xor_relaxed(let t):
    //      return "atomic_xor_relaxed_\(t)"
    //    case .atomic_xor_acquire(let t):
    //      return "atomic_xor_acquire_\(t)"
    //    case .atomic_xor_release(let t):
    //      return "atomic_xor_release_\(t)"
    //    case .atomic_xor_acqrel(let t):
    //      return "atomic_xor_acqrel_\(t)"
    //    case .atomic_xor_seqcst(let t):
    //      return "atomic_xor_seqcst_\(t)"
    //    case .atomic_cmpxchg_relaxed_relaxed(let t):
    //      return "atomic_cmpxchg_relaxed_relaxed_\(t)"
    //    case .atomic_cmpxchg_relaxed_acquire(let t):
    //      return "atomic_cmpxchg_relaxed_acquire_\(t)"
    //    case .atomic_cmpxchg_relaxed_seqcst(let t):
    //      return "atomic_cmpxchg_relaxed_seqcst_\(t)"
    //    case .atomic_cmpxchg_acquire_relaxed(let t):
    //      return "atomic_cmpxchg_acquire_relaxed_\(t)"
    //    case .atomic_cmpxchg_acquire_acquire(let t):
    //      return "atomic_cmpxchg_acquire_acquire_\(t)"
    //    case .atomic_cmpxchg_acquire_seqcst(let t):
    //      return "atomic_cmpxchg_acquire_seqcst_\(t)"
    //    case .atomic_cmpxchg_release_relaxed(let t):
    //      return "atomic_cmpxchg_release_relaxed_\(t)"
    //    case .atomic_cmpxchg_release_acquire(let t):
    //      return "atomic_cmpxchg_release_acquire_\(t)"
    //    case .atomic_cmpxchg_release_seqcst(let t):
    //      return "atomic_cmpxchg_release_seqcst_\(t)"
    //    case .atomic_cmpxchg_acqrel_relaxed(let t):
    //      return "atomic_cmpxchg_acqrel_relaxed_\(t)"
    //    case .atomic_cmpxchg_acqrel_acquire(let t):
    //      return "atomic_cmpxchg_acqrel_acquire_\(t)"
    //    case .atomic_cmpxchg_acqrel_seqcst(let t):
    //      return "atomic_cmpxchg_acqrel_seqcst_\(t)"
    //    case .atomic_cmpxchg_seqcst_relaxed(let t):
    //      return "atomic_cmpxchg_seqcst_relaxed_\(t)"
    //    case .atomic_cmpxchg_seqcst_acquire(let t):
    //      return "atomic_cmpxchg_seqcst_acquire_\(t)"
    //    case .atomic_cmpxchg_seqcst_seqcst(let t):
    //      return "atomic_cmpxchg_seqcst_seqcst_\(t)"
    //    case .atomic_cmpxchgweak_relaxed_relaxed(let t):
    //      return "atomic_cmpxchgweak_relaxed_relaxed_\(t)"
    //    case .atomic_cmpxchgweak_relaxed_acquire(let t):
    //      return "atomic_cmpxchgweak_relaxed_acquire_\(t)"
    //    case .atomic_cmpxchgweak_relaxed_seqcst(let t):
    //      return "atomic_cmpxchgweak_relaxed_seqcst_\(t)"
    //    case .atomic_cmpxchgweak_acquire_relaxed(let t):
    //      return "atomic_cmpxchgweak_acquire_relaxed_\(t)"
    //    case .atomic_cmpxchgweak_acquire_acquire(let t):
    //      return "atomic_cmpxchgweak_acquire_acquire_\(t)"
    //    case .atomic_cmpxchgweak_acquire_seqcst(let t):
    //      return "atomic_cmpxchgweak_acquire_seqcst_\(t)"
    //    case .atomic_cmpxchgweak_release_relaxed(let t):
    //      return "atomic_cmpxchgweak_release_relaxed_\(t)"
    //    case .atomic_cmpxchgweak_release_acquire(let t):
    //      return "atomic_cmpxchgweak_release_acquire_\(t)"
    //    case .atomic_cmpxchgweak_release_seqcst(let t):
    //      return "atomic_cmpxchgweak_release_seqcst_\(t)"
    //    case .atomic_cmpxchgweak_acqrel_relaxed(let t):
    //      return "atomic_cmpxchgweak_acqrel_relaxed_\(t)"
    //    case .atomic_cmpxchgweak_acqrel_acquire(let t):
    //      return "atomic_cmpxchgweak_acqrel_acquire_\(t)"
    //    case .atomic_cmpxchgweak_acqrel_seqcst(let t):
    //      return "atomic_cmpxchgweak_acqrel_seqcst_\(t)"
    //    case .atomic_cmpxchgweak_seqcst_relaxed(let t):
    //      return "atomic_cmpxchgweak_seqcst_relaxed_\(t)"
    //    case .atomic_cmpxchgweak_seqcst_acquire(let t):
    //      return "atomic_cmpxchgweak_seqcst_acquire_\(t)"
    //    case .atomic_cmpxchgweak_seqcst_seqcst(let t):
    //      return "atomic_cmpxchgweak_seqcst_seqcst_\(t)"
    //    case .atomic_fence_acquire:
    //      return "atomic_fence_acquire"
    //    case .atomic_fence_release:
    //      return "atomic_fence_release"
    //    case .atomic_fence_acqrel:
    //      return "atomic_fence_acqrel"
    //    case .atomic_fence_seqcst:
    //      return "atomic_fence_seqcst"
    //    case .atomic_singlethreadfence_acquire:
    //      return "atomic_singlethreadfence_acquire"
    //    case .atomic_singlethreadfence_release:
    //      return "atomic_singlethreadfence_release"
    //    case .atomic_singlethreadfence_acqrel:
    //      return "atomic_singlethreadfence_acqrel"
    //    case .atomic_singlethreadfence_seqcst:
    //      return "atomic_singlethreadfence_seqcst"
    }
  }

}

// MARK: Parsing

extension BuiltinFunction {

  /// An instance whose name—up to the open parenthesis—is `n`, or `nil` if no such
  /// built-in function exists.
  public init?(_ n: String, uniquingTypesWith s: inout TypeStore) {
    var tokens = n.split(separator: "_")[...]

    // The first token is the LLVM instruction name.
    guard let head = tokens.popFirst() else { return nil }
    switch head {
    case "trap":
      self = .trap
    case "address":
      if !tokens.isEmpty { return nil }
      self = .addressOf
    case "mark":
      if tokens != ["uninitialized"] { return nil }
      self = .markUninitialized

    //    case "advanced":
    //      guard let ((_, _), t) = (exactly("by") ++ exactly("bytes") ++ machineType)(&tokens)
    //      else { return nil }
    //      self = .advancedByBytes(byteOffset: t)

    case "add":
      guard let (p, t) = integerArithmeticTail(&tokens) else { return nil }
      self = .add(p, s.demand(t))
    case "sub":
      guard let (p, t) = integerArithmeticTail(&tokens) else { return nil }
      self = .sub(p, s.demand(t))
    case "mul":
      guard let (p, t) = integerArithmeticTail(&tokens) else { return nil }
      self = .mul(p, s.demand(t))

    //    case "shl":
    //      guard let (p, t) = integerArithmeticTail(&tokens) else { return nil }
    //      self = .shl(p, t)
    //
    //    case "udiv":
    //      guard let (p, t) = (maybe("exact") ++ machineType)(&tokens) else { return nil }
    //      self = .udiv(exact: p != nil, t)
    //
    //    case "sdiv":
    //      guard let (p, t) = (maybe("exact") ++ machineType)(&tokens) else { return nil }
    //      self = .sdiv(exact: p != nil, t)
    //
    //    case "lshr":
    //      guard let (p, t) = (maybe("exact") ++ machineType)(&tokens) else { return nil }
    //      self = .lshr(exact: p != nil, t)
    //
    //    case "ashr":
    //      guard let (p, t) = (maybe("exact") ++ machineType)(&tokens) else { return nil }
    //      self = .ashr(exact: p != nil, t)
    //
    //    case "urem":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .urem(t)
    //
    //    case "srem":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .srem(t)

    case "and":
      guard let t = machineType(&tokens) else { return nil }
      self = .and(s.demand(t))
    case "or":
      guard let t = machineType(&tokens) else { return nil }
      self = .or(s.demand(t))
    case "xor":
      guard let t = machineType(&tokens) else { return nil }
      self = .xor(s.demand(t))
    case "sadd":
      guard let t = integerArithmeticWithOverflowTail(&tokens) else { return nil }
      self = .signedAdditionWithOverflow(s.demand(t))
    case "uadd":
      guard let t = integerArithmeticWithOverflowTail(&tokens) else { return nil }
      self = .unsignedAdditionWithOverflow(s.demand(t))
    case "ssub":
      guard let t = integerArithmeticWithOverflowTail(&tokens) else { return nil }
      self = .signedSubtractionWithOverflow(s.demand(t))
    case "usub":
      guard let t = integerArithmeticWithOverflowTail(&tokens) else { return nil }
      self = .unsignedSubtractionWithOverflow(s.demand(t))
    case "smul":
      guard let t = integerArithmeticWithOverflowTail(&tokens) else { return nil }
      self = .signedMultiplicationWithOverflow(s.demand(t))
    case "umul":
      guard let t = integerArithmeticWithOverflowTail(&tokens) else { return nil }
      self = .unsignedMultiplicationWithOverflow(s.demand(t))
    case "icmp":
      guard let (p, t) = integerComparisonTail(&tokens) else { return nil }
      self = .icmp(p, s.demand(t))

    //    case "trunc":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .trunc(s, d)
    //
    //    case "zext":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .zext(s, d)
    //
    //    case "sext":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .sext(s, d)
    //
    //    case "uitofp":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .uitofp(s, d)
    //
    //    case "sitofp":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .sitofp(s, d)
    //
    //    case "inttoptr":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .inttoptr(t)
    //
    //    case "ptrtoint":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .ptrtoint(t)
    //
    //    case "fadd":
    //      guard let (p, t) = floatingPointArithmeticTail(&tokens) else { return nil }
    //      self = .fadd(p, t)
    //
    //    case "fsub":
    //      guard let (p, t) = floatingPointArithmeticTail(&tokens) else { return nil }
    //      self = .fsub(p, t)
    //
    //    case "fmul":
    //      guard let (p, t) = floatingPointArithmeticTail(&tokens) else { return nil }
    //      self = .fmul(p, t)
    //
    //    case "fdiv":
    //      guard let (p, t) = floatingPointArithmeticTail(&tokens) else { return nil }
    //      self = .fdiv(p, t)
    //
    //    case "frem":
    //      guard let (p, t) = floatingPointArithmeticTail(&tokens) else { return nil }
    //      self = .frem(p, t)
    //
    //    case "fcmp":
    //      guard let (p, t) = floatingPointComparisonTail(&tokens) else { return nil }
    //      self = .fcmp(p.0, p.1, t)
    //
    //    case "fptrunc":
    //      guard let (s, d) = (builtinType ++ builtinType)(&tokens) else { return nil }
    //      self = .fptrunc(s, d)
    //
    //    case "fpext":
    //      guard let (s, d) = (builtinType ++ builtinType)(&tokens) else { return nil }
    //      self = .fpext(s, d)
    //
    //    case "fptoui":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .fptoui(s, d)
    //
    //    case "fptosi":
    //      guard let (s, d) = (machineType ++ machineType)(&tokens) else { return nil }
    //      self = .fptosi(s, d)
    //
    //    case "ctpop":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .ctpop(t)
    //
    //    case "ctlz":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .ctlz(t)
    //
    //    case "cttz":
    //      guard let t = machineType(&tokens) else { return nil }
    //      self = .cttz(t)

    case "zeroinitializer":
      guard let t = machineType(&tokens) else { return nil }
      self = .zeroinitializer(s.demand(t))
    //
    //    case "atomic":
    //      if let t = tokens.first, t.contains("fence") {
    //        self.init(fence: n)
    //      } else {
    //        self.init(atomic: n)
    //      }

    default:
      return nil
    }
  }
  //
  //  /// An atomic fence function whose name—up to the open parenthesis—is `n`, or `nil` if no such
  //  /// built-in function exists.
  //  private init?(fence n: String) {
  //    precondition(n.starts(with: "atomic_"))
  //    switch n {
  //    case "atomic_fence_acquire":
  //      self = .atomic_fence_acquire
  //    case "atomic_fence_release":
  //      self = .atomic_fence_release
  //    case "atomic_fence_acqrel":
  //      self = .atomic_fence_acqrel
  //    case "atomic_fence_seqcst":
  //      self = .atomic_fence_seqcst
  //    case "atomic_singlethreadfence_acquire":
  //      self = .atomic_singlethreadfence_acquire
  //    case "atomic_singlethreadfence_release":
  //      self = .atomic_singlethreadfence_release
  //    case "atomic_singlethreadfence_acqrel":
  //      self = .atomic_singlethreadfence_acqrel
  //    case "atomic_singlethreadfence_seqcst":
  //      self = .atomic_singlethreadfence_seqcst
  //    default:
  //      return nil
  //    }
  //  }
  //
  //  /// An atomic non-fence function whose name—up to the open parenthesis—is `n`, or `nil` if no such
  //  /// built-in function exists.
  //  private init?(atomic n: String) {
  //    // The type of all atomics (except fences) is mentioned at the end.
  //    let m = n.split(atLastIndexOf: "_")
  //    guard let t = MachineType.ID(m.tail.dropFirst()) else { return nil }
  //
  //    switch m.head {
  //    case "atomic_store_relaxed":
  //      self = .atomic_store_relaxed(t)
  //    case "atomic_store_release":
  //      self = .atomic_store_release(t)
  //    case "atomic_store_seqcst":
  //      self = .atomic_store_seqcst(t)
  //    case "atomic_load_relaxed":
  //      self = .atomic_load_relaxed(t)
  //    case "atomic_load_acquire":
  //      self = .atomic_load_acquire(t)
  //    case "atomic_load_seqcst":
  //      self = .atomic_load_seqcst(t)
  //    case "atomic_swap_relaxed":
  //      self = .atomic_swap_relaxed(t)
  //    case "atomic_swap_acquire":
  //      self = .atomic_swap_acquire(t)
  //    case "atomic_swap_release":
  //      self = .atomic_swap_release(t)
  //    case "atomic_swap_acqrel":
  //      self = .atomic_swap_acqrel(t)
  //    case "atomic_swap_seqcst":
  //      self = .atomic_swap_seqcst(t)
  //    case "atomic_add_relaxed":
  //      self = .atomic_add_relaxed(t)
  //    case "atomic_add_acquire":
  //      self = .atomic_add_acquire(t)
  //    case "atomic_add_release":
  //      self = .atomic_add_release(t)
  //    case "atomic_add_acqrel":
  //      self = .atomic_add_acqrel(t)
  //    case "atomic_add_seqcst":
  //      self = .atomic_add_seqcst(t)
  //    case "atomic_fadd_relaxed":
  //      self = .atomic_fadd_relaxed(t)
  //    case "atomic_fadd_acquire":
  //      self = .atomic_fadd_acquire(t)
  //    case "atomic_fadd_release":
  //      self = .atomic_fadd_release(t)
  //    case "atomic_fadd_acqrel":
  //      self = .atomic_fadd_acqrel(t)
  //    case "atomic_fadd_seqcst":
  //      self = .atomic_fadd_seqcst(t)
  //    case "atomic_sub_relaxed":
  //      self = .atomic_sub_relaxed(t)
  //    case "atomic_sub_acquire":
  //      self = .atomic_sub_acquire(t)
  //    case "atomic_sub_release":
  //      self = .atomic_sub_release(t)
  //    case "atomic_sub_acqrel":
  //      self = .atomic_sub_acqrel(t)
  //    case "atomic_sub_seqcst":
  //      self = .atomic_sub_seqcst(t)
  //    case "atomic_fsub_relaxed":
  //      self = .atomic_fsub_relaxed(t)
  //    case "atomic_fsub_acquire":
  //      self = .atomic_fsub_acquire(t)
  //    case "atomic_fsub_release":
  //      self = .atomic_fsub_release(t)
  //    case "atomic_fsub_acqrel":
  //      self = .atomic_fsub_acqrel(t)
  //    case "atomic_fsub_seqcst":
  //      self = .atomic_fsub_seqcst(t)
  //    case "atomic_max_relaxed":
  //      self = .atomic_max_relaxed(t)
  //    case "atomic_max_acquire":
  //      self = .atomic_max_acquire(t)
  //    case "atomic_max_release":
  //      self = .atomic_max_release(t)
  //    case "atomic_max_acqrel":
  //      self = .atomic_max_acqrel(t)
  //    case "atomic_max_seqcst":
  //      self = .atomic_max_seqcst(t)
  //    case "atomic_umax_relaxed":
  //      self = .atomic_umax_relaxed(t)
  //    case "atomic_umax_acquire":
  //      self = .atomic_umax_acquire(t)
  //    case "atomic_umax_release":
  //      self = .atomic_umax_release(t)
  //    case "atomic_umax_acqrel":
  //      self = .atomic_umax_acqrel(t)
  //    case "atomic_umax_seqcst":
  //      self = .atomic_umax_seqcst(t)
  //    case "atomic_fmax_relaxed":
  //      self = .atomic_fmax_relaxed(t)
  //    case "atomic_fmax_acquire":
  //      self = .atomic_fmax_acquire(t)
  //    case "atomic_fmax_release":
  //      self = .atomic_fmax_release(t)
  //    case "atomic_fmax_acqrel":
  //      self = .atomic_fmax_acqrel(t)
  //    case "atomic_fmax_seqcst":
  //      self = .atomic_fmax_seqcst(t)
  //    case "atomic_min_relaxed":
  //      self = .atomic_min_relaxed(t)
  //    case "atomic_min_acquire":
  //      self = .atomic_min_acquire(t)
  //    case "atomic_min_release":
  //      self = .atomic_min_release(t)
  //    case "atomic_min_acqrel":
  //      self = .atomic_min_acqrel(t)
  //    case "atomic_min_seqcst":
  //      self = .atomic_min_seqcst(t)
  //    case "atomic_umin_relaxed":
  //      self = .atomic_umin_relaxed(t)
  //    case "atomic_umin_acquire":
  //      self = .atomic_umin_acquire(t)
  //    case "atomic_umin_release":
  //      self = .atomic_umin_release(t)
  //    case "atomic_umin_acqrel":
  //      self = .atomic_umin_acqrel(t)
  //    case "atomic_umin_seqcst":
  //      self = .atomic_umin_seqcst(t)
  //    case "atomic_fmin_relaxed":
  //      self = .atomic_fmin_relaxed(t)
  //    case "atomic_fmin_acquire":
  //      self = .atomic_fmin_acquire(t)
  //    case "atomic_fmin_release":
  //      self = .atomic_fmin_release(t)
  //    case "atomic_fmin_acqrel":
  //      self = .atomic_fmin_acqrel(t)
  //    case "atomic_fmin_seqcst":
  //      self = .atomic_fmin_seqcst(t)
  //    case "atomic_and_relaxed":
  //      self = .atomic_and_relaxed(t)
  //    case "atomic_and_acquire":
  //      self = .atomic_and_acquire(t)
  //    case "atomic_and_release":
  //      self = .atomic_and_release(t)
  //    case "atomic_and_acqrel":
  //      self = .atomic_and_acqrel(t)
  //    case "atomic_and_seqcst":
  //      self = .atomic_and_seqcst(t)
  //    case "atomic_nand_relaxed":
  //      self = .atomic_nand_relaxed(t)
  //    case "atomic_nand_acquire":
  //      self = .atomic_nand_acquire(t)
  //    case "atomic_nand_release":
  //      self = .atomic_nand_release(t)
  //    case "atomic_nand_acqrel":
  //      self = .atomic_nand_acqrel(t)
  //    case "atomic_nand_seqcst":
  //      self = .atomic_nand_seqcst(t)
  //    case "atomic_or_relaxed":
  //      self = .atomic_or_relaxed(t)
  //    case "atomic_or_acquire":
  //      self = .atomic_or_acquire(t)
  //    case "atomic_or_release":
  //      self = .atomic_or_release(t)
  //    case "atomic_or_acqrel":
  //      self = .atomic_or_acqrel(t)
  //    case "atomic_or_seqcst":
  //      self = .atomic_or_seqcst(t)
  //    case "atomic_xor_relaxed":
  //      self = .atomic_xor_relaxed(t)
  //    case "atomic_xor_acquire":
  //      self = .atomic_xor_acquire(t)
  //    case "atomic_xor_release":
  //      self = .atomic_xor_release(t)
  //    case "atomic_xor_acqrel":
  //      self = .atomic_xor_acqrel(t)
  //    case "atomic_xor_seqcst":
  //      self = .atomic_xor_seqcst(t)
  //    case "atomic_cmpxchg_relaxed_relaxed":
  //      self = .atomic_cmpxchg_relaxed_relaxed(t)
  //    case "atomic_cmpxchg_relaxed_acquire":
  //      self = .atomic_cmpxchg_relaxed_acquire(t)
  //    case "atomic_cmpxchg_relaxed_seqcst":
  //      self = .atomic_cmpxchg_relaxed_seqcst(t)
  //    case "atomic_cmpxchg_acquire_relaxed":
  //      self = .atomic_cmpxchg_acquire_relaxed(t)
  //    case "atomic_cmpxchg_acquire_acquire":
  //      self = .atomic_cmpxchg_acquire_acquire(t)
  //    case "atomic_cmpxchg_acquire_seqcst":
  //      self = .atomic_cmpxchg_acquire_seqcst(t)
  //    case "atomic_cmpxchg_release_relaxed":
  //      self = .atomic_cmpxchg_release_relaxed(t)
  //    case "atomic_cmpxchg_release_acquire":
  //      self = .atomic_cmpxchg_release_acquire(t)
  //    case "atomic_cmpxchg_release_seqcst":
  //      self = .atomic_cmpxchg_release_seqcst(t)
  //    case "atomic_cmpxchg_acqrel_relaxed":
  //      self = .atomic_cmpxchg_acqrel_relaxed(t)
  //    case "atomic_cmpxchg_acqrel_acquire":
  //      self = .atomic_cmpxchg_acqrel_acquire(t)
  //    case "atomic_cmpxchg_acqrel_seqcst":
  //      self = .atomic_cmpxchg_acqrel_seqcst(t)
  //    case "atomic_cmpxchg_seqcst_relaxed":
  //      self = .atomic_cmpxchg_seqcst_relaxed(t)
  //    case "atomic_cmpxchg_seqcst_acquire":
  //      self = .atomic_cmpxchg_seqcst_acquire(t)
  //    case "atomic_cmpxchg_seqcst_seqcst":
  //      self = .atomic_cmpxchg_seqcst_seqcst(t)
  //    case "atomic_cmpxchgweak_relaxed_relaxed":
  //      self = .atomic_cmpxchgweak_relaxed_relaxed(t)
  //    case "atomic_cmpxchgweak_relaxed_acquire":
  //      self = .atomic_cmpxchgweak_relaxed_acquire(t)
  //    case "atomic_cmpxchgweak_relaxed_seqcst":
  //      self = .atomic_cmpxchgweak_relaxed_seqcst(t)
  //    case "atomic_cmpxchgweak_acquire_relaxed":
  //      self = .atomic_cmpxchgweak_acquire_relaxed(t)
  //    case "atomic_cmpxchgweak_acquire_acquire":
  //      self = .atomic_cmpxchgweak_acquire_acquire(t)
  //    case "atomic_cmpxchgweak_acquire_seqcst":
  //      self = .atomic_cmpxchgweak_acquire_seqcst(t)
  //    case "atomic_cmpxchgweak_release_relaxed":
  //      self = .atomic_cmpxchgweak_release_relaxed(t)
  //    case "atomic_cmpxchgweak_release_acquire":
  //      self = .atomic_cmpxchgweak_release_acquire(t)
  //    case "atomic_cmpxchgweak_release_seqcst":
  //      self = .atomic_cmpxchgweak_release_seqcst(t)
  //    case "atomic_cmpxchgweak_acqrel_relaxed":
  //      self = .atomic_cmpxchgweak_acqrel_relaxed(t)
  //    case "atomic_cmpxchgweak_acqrel_acquire":
  //      self = .atomic_cmpxchgweak_acqrel_acquire(t)
  //    case "atomic_cmpxchgweak_acqrel_seqcst":
  //      self = .atomic_cmpxchgweak_acqrel_seqcst(t)
  //    case "atomic_cmpxchgweak_seqcst_relaxed":
  //      self = .atomic_cmpxchgweak_seqcst_relaxed(t)
  //    case "atomic_cmpxchgweak_seqcst_acquire":
  //      self = .atomic_cmpxchgweak_seqcst_acquire(t)
  //    case "atomic_cmpxchgweak_seqcst_seqcst":
  //      self = .atomic_cmpxchgweak_seqcst_seqcst(t)
  //    default:
  //      return nil
  //    }
  //  }

}

/// A function that parses an instance of `T` by consuming a prefix of tokens from `stream`, or
/// returns `nil` if such instance cannot be parsed.
///
/// - Note: a prefix of `tokens` may have been consumed even if the function returns `nil`.
private typealias BuiltinFunctionParser<T> =
  @Sendable (_ stream: inout ArraySlice<Substring>) -> T?

/// Returns a parser that consumes an element equal to `s` and returns `.some(s)`, or returns
/// `.some(nil)` if such an element can't be consumed.
private func maybe(_ s: String) -> BuiltinFunctionParser<String?> {
  { (stream: inout ArraySlice<Substring>) -> String?? in
    if let r = exactly(s)(&stream) { return .some(r) }
    return .some(nil)
  }
}

/// Returns a parser that consumes and returns an element equal to `s`.
private func exactly(_ s: String) -> BuiltinFunctionParser<String> {
  { (stream: inout ArraySlice<Substring>) -> String? in
    stream.first == s[...] ? (stream.popFirst(), .some(s)).1 : nil
  }
}

/// Returns a parser that returns the result of applying `a` and then `b` or `nil` if either `a`
/// or `b` returns `nil`.
private func + <A, B>(
  _ a: @escaping BuiltinFunctionParser<A>, _ b: @escaping BuiltinFunctionParser<B>
) -> BuiltinFunctionParser<(A, B)> {
  { (stream: inout ArraySlice<Substring>) -> (A, B)? in
    a(&stream).flatMap({ (x) in b(&stream).map({ (y) in (x, y) }) })
  }
}

/// Returns a parser that returns an instance of `T` if it can be built by consuming the next
/// element in the stream.
private func take<T: RawRepresentable>(
  _: T.Type
) -> BuiltinFunctionParser<T> where T.RawValue == String {
  { (stream: inout ArraySlice<Substring>) -> T? in
    stream.popFirst().flatMap({ (x) in T(rawValue: .init(x)) })
  }
}

/// Returns a built-in type parsed from `stream`.
private func machineType(_ stream: inout ArraySlice<Substring>) -> MachineType? {
  stream.popFirst().flatMap(MachineType.init(_:))
}

/// Returns the longest sequence of floating-point math flags that can be parsed from `stream`.
private func mathFlags(_ stream: inout ArraySlice<Substring>) -> MathFlags {
  var result: MathFlags = []
  while let x = stream.first {
    guard let y = MathFlags(x) else { break }
    stream.removeFirst()
    result.insert(y)
  }
  return result
}

/// Returns an overflow behavior parsed from `stream` or `.ignore` if none can be parsed.
private func overflowBehavior(_ stream: inout ArraySlice<Substring>) -> OverflowBehavior {
  switch stream.first {
  case "nuw":
    stream.removeFirst()
    return .nuw
  case "nsw":
    stream.removeFirst()
    return .nsw
  default:
    return .ignore
  }
}

/// Parses the parameters and type of an integer arithmetic instruction with overflow reporting.
private func integerArithmeticWithOverflowTail(
  _ stream: inout ArraySlice<Substring>
) -> MachineType? {
  let p = exactly("with") + exactly("overflow") + machineType
  return p(&stream).map(\.1)
}

/// Parses the parameters and type of an integer arithmetic instruction.
private let integerArithmeticTail =
  overflowBehavior + machineType

/// Parses the parameters and type of `icmp`.
private let integerComparisonTail =
  take(IntegerPredicate.self) + machineType

/// Parses the parameters and type of a floating-point arithmetic instruction.
private let floatingPointArithmeticTail =
  mathFlags + machineType

/// Parses the parameters and type of `fcmp`.
private let floatingPointComparisonTail =
  mathFlags + take(FloatingPointPredicate.self) + machineType
