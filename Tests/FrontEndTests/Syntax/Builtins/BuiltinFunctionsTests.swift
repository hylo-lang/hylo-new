import FrontEnd
import Testing

@Suite
struct BuiltinFunctionsTests {

  var program = Program()

  @Test
  mutating func showable() throws {
    let i64 = program.types.demand(MachineType.i(64))
    let i32 = program.types.demand(MachineType.i(32))
    let f64 = program.types.demand(MachineType.float64)
    let f32 = program.types.demand(MachineType.float32)

    #expect(show(.trap) == "trap")
    #expect(show(.addressOf) == "address")
    #expect(show(.assumeInitialized(true)) == "assume_initialized")
    #expect(show(.assumeInitialized(false)) == "assume_uninitialized")
    #expect(show(.alloca(i64)) == "alloca_i64")
    #expect(show(.add(.ignore, i64)) == "add_i64")
    #expect(show(.add(.nsw, i64)) == "add_nsw_i64")
    #expect(show(.sub(.ignore, i64)) == "sub_i64")
    #expect(show(.sub(.nsw, i64)) == "sub_nsw_i64")
    #expect(show(.mul(.ignore, i64)) == "mul_i64")
    #expect(show(.mul(.nsw, i64)) == "mul_nsw_i64")
    #expect(show(.udiv(exact: false, i64)) == "udiv_i64")
    #expect(show(.udiv(exact: true, i64)) == "udiv_exact_i64")
    #expect(show(.sdiv(exact: false, i64)) == "sdiv_i64")
    #expect(show(.sdiv(exact: true, i64)) == "sdiv_exact_i64")
    #expect(show(.urem(i64)) == "urem_i64")
    #expect(show(.srem(i64)) == "srem_i64")
    #expect(show(.shl(i64)) == "shl_i64")
    #expect(show(.ashr(i64)) == "ashr_i64")
    #expect(show(.lshr(i64)) == "lshr_i64")
    #expect(show(.and(i64)) == "and_i64")
    #expect(show(.or(i64)) == "or_i64")
    #expect(show(.xor(i64)) == "xor_i64")
    #expect(show(.signedAdditionWithOverflow(i64)) == "sadd_with_overflow_i64")
    #expect(show(.unsignedAdditionWithOverflow(i64)) == "uadd_with_overflow_i64")
    #expect(show(.signedSubtractionWithOverflow(i64)) == "ssub_with_overflow_i64")
    #expect(show(.unsignedSubtractionWithOverflow(i64)) == "usub_with_overflow_i64")
    #expect(show(.signedMultiplicationWithOverflow(i64)) == "smul_with_overflow_i64")
    #expect(show(.unsignedMultiplicationWithOverflow(i64)) == "umul_with_overflow_i64")
    #expect(show(.icmp(.eq, i64)) == "icmp_eq_i64")
    #expect(show(.trunc(i64, i32)) == "trunc_i64_i32")
    #expect(show(.truncateOrZeroExtend(i64, i32)) == "trunc_or_zext_i64_i32")
    #expect(show(.truncateOrSignExtend(i64, i32)) == "trunc_or_sext_i64_i32")
    #expect(show(.zext(i32, i64)) == "zext_i32_i64")
    #expect(show(.sext(i32, i64)) == "sext_i32_i64")
    #expect(show(.uitofp(i32, f32)) == "uitofp_i32_float32")
    #expect(show(.sitofp(i32, f32)) == "sitofp_i32_float32")
    #expect(show(.inttoptr) == "inttoptr")
    #expect(show(.ptrtoint) == "ptrtoint")
    #expect(show(.fadd([], f32)) == "fadd_float32")
    #expect(show(.fadd([.ninf, .nnan], f32)) == "fadd_ninf_nnan_float32")
    #expect(show(.fsub([], f32)) == "fsub_float32")
    #expect(show(.fsub([.ninf, .nnan], f32)) == "fsub_ninf_nnan_float32")
    #expect(show(.fdiv([], f32)) == "fdiv_float32")
    #expect(show(.fdiv([.ninf, .nnan], f32)) == "fdiv_ninf_nnan_float32")
    #expect(show(.frem([], f32)) == "frem_float32")
    #expect(show(.frem([.ninf, .nnan], f32)) == "frem_ninf_nnan_float32")
    #expect(show(.fcmp([], .oeq, f32)) == "fcmp_oeq_float32")
    #expect(show(.fcmp([.ninf, .nnan], .oeq, f32)) == "fcmp_ninf_nnan_oeq_float32")
    #expect(show(.fptrunc(f64, f32)) == "fptrunc_float64_float32")
    #expect(show(.fpext(f32, f64)) == "fpext_float32_float64")
    #expect(show(.fptoui(f32, i32)) == "fptoui_float32_i32")
    #expect(show(.fptosi(f32, i32)) == "fptosi_float32_i32")
    #expect(show(.ctpop(i64)) == "ctpop_i64")
    #expect(show(.ctlz(i64)) == "ctlz_i64")
    #expect(show(.zeroinitializer(i64)) == "zeroinitializer_i64")
    #expect(show(.advancedByBytes(byteOffset: i64, inBounds: false)) == "advanced_by_bytes_i64")
    #expect(
      show(.advancedByBytes(byteOffset: i64, inBounds: true)) == "advanced_by_bytes_inbounds_i64")
  }

  /// Returns the textual representation of `f`.
  private func show(_ f: BuiltinFunction) -> String {
    program.show(f)
  }

}
