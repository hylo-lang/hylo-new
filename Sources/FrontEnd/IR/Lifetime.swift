/// A region of the program rooted at a definition.
///
/// A lifetime rooted at a definition `d` is a region starting immediately after `d` and covering
/// a set of uses dominated by `d`. The "upper boundaries" of a lifetime are the program points
/// immediately after the uses sequenced last in that region.
///
/// - Note: The definition of an operand `o` isn't part of `o`'s lifetime.
internal struct Lifetime: Sendable {

  internal typealias Coverage = [IRBlock.ID: BlockCoverage]

  /// A position before or after an instruction.
  internal enum Boundary {

    /// The position immediately before the first instruction of a basic block.
    case start(of: IRBlock.ID)

    /// The position immediately before an instruction.
    case before(AnyInstructionIdentity)

    /// The position immediately after an instruction.
    case after(AnyInstructionIdentity)

  }

  /// A data structure encoding how a block covers the lifetime.
  internal enum BlockCoverage: Sendable {

    /// The operand is live in and out of the block.
    case liveInAndOut

    /// The operand is only live out.
    case liveOut

    /// The operand is only live in. The payload is its last use, if any.
    case liveIn(lastUse: Use?)

    /// The operand is neither live in or out, but it's used in the block. The payload is its last
    /// use, if any.
    case closed(lastUse: Use?)

  }

  /// The operand whose `self` is the lifetime.
  ///
  /// - Note: `operand` is either an instruction or a basic block parameter.
  internal let operand: IRValue

  /// The set of instructions in the lifetime.
  internal let coverage: Coverage

  /// Creates an empty lifetime.
  internal init(operand: IRValue) {
    self.operand = operand
    self.coverage = [:]
  }

  /// Creates an instance with the given properties.
  internal init(operand: IRValue, coverage: Coverage) {
    self.operand = operand
    self.coverage = coverage
  }

  /// Indicates whether the lifetime is empty.
  internal var isEmpty: Bool {
    for blockCoverage in coverage.values {
      switch blockCoverage {
      case .liveInAndOut, .liveOut, .liveIn, .closed(lastUse: .some):
        return false
      default:
        continue
      }
    }
    return true
  }

  /// The upper boundaries of the region formed by the elements in `self`.
  ///
  /// There's one upper boundary per basic block covered in the lifetime that isn't live-out. It
  /// falls immediately after the last element of `self` also contained in that block, or, in the
  /// case of a live-in block with no use, immediately before the first instruction.
  internal var upperBoundaries: some Sequence<Boundary> {
    coverage.lazy.compactMap { (b, c) -> Boundary? in
      switch c {
      case .liveIn(let use):
        return use.map({ .after($0.user) }) ?? .start(of: b)
      case .closed(let use):
        return use.map({ .after($0.user) }) ?? .after(operand.register!)
      case .liveInAndOut, .liveOut:
        return nil
      }
    }
  }

}
