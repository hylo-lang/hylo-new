/// A substitution table for rewriting the properties of IR instructions.
public struct IRSubstitutionTable: Sendable {

  /// A table from IR value to its substitution, if defined.
  ///
  /// Each value is assumed to have the same type as its corresponding key and to compute a
  /// semantically equivalent result.
  public private(set) var values: [IRValue: IRValue]

  /// A table from basic block to its substitution, if defined.
  public private(set) var blocks: [IRBlock.ID: IRBlock.ID]

  /// Creates an empty instance.
  public init() {
    self.values = [:]
    self.blocks = [:]
  }

  /// Accesses the substitution for `o` iff it is defined, or else `o`.
  public subscript(v: IRValue) -> IRValue {
    get { values[v] ?? v }
    set { values[v] = newValue }
  }

  /// Accesses the substitution for `b` iff it is defined, or else `b`.
  public subscript(b: IRBlock.ID) -> IRBlock.ID {
    get { blocks[b] ?? b }
    set { blocks[b] = newValue }
  }

}
