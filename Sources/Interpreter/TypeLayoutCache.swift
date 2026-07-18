import FrontEnd
import Utilities

/// A memoizing computer of type layouts.
struct TypeLayoutCache {

  /// The program supplying the types.
  let p: Program

  /// The ABI for which the types will be laid out.
  let abi: any TargetABI

  /// The memo of layouts computed so far.
  private var storage: [ConcreteTypeIdentity: TypeLayout] = [:]

  /// An instance for laying out types in `p` according to `abi`.
  public init(typesIn p: Program, for abi: any TargetABI) {
    self.p = p
    self.abi = abi
  }

  /// The layout for `t`.
  public subscript(_ t: ConcreteTypeIdentity) -> TypeLayout {
    mutating get {
      if let r = storage[t] { return r }
      let r = computeLayout(t)
      storage[t] = r
      return r
    }
  }

  /// Returns the layout for `t`.
  private mutating func computeLayout(_ t: ConcreteTypeIdentity) -> TypeLayout {
    if isMachineType(t) {
      let u = p.types[p.types.cast(t.underlying, to: MachineType.self)!]
      return TypeLayout(bytes: abi.layout(u), type: t, parts: [], isEnumLayout: false)
    } else if isEnum(t) {
      unimplemented()
    } else if hasRecordLayout(t) {
      unimplemented()
    } else {
      unreachable("\(p.show(t.underlying)) doesn't have any layout)")
    }
  }

  /// Returns true iff `t` is of `MachineType`.
  private mutating func isMachineType(_ t: ConcreteTypeIdentity) -> Bool {
    p.types.tag(of: t.underlying).value == MachineType.self
  }

  /// Returns true iff `t` is of enum type.
  private mutating func isEnum(_ t: ConcreteTypeIdentity) -> Bool {
    unimplemented()
  }

  /// Returns true iff `t` has a record layout.
  private mutating func hasRecordLayout(_ t: ConcreteTypeIdentity) -> Bool {
    unimplemented()
  }
}
