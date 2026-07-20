import FrontEnd
import Utilities

/// A memoizing computer of type layouts.
struct TypeLayoutCache {

  /// The ABI for which the types will be laid out.
  let abi: any TargetABI

  /// The memo of layouts computed so far.
  private var storage: [MonomorphicTypeIdentity: TypeLayout] = [:]

  /// An instance for laying out types according to `abi`.
  public init(for abi: any TargetABI) {
    self.abi = abi
  }

  /// The layout for `t` in `p`.
  public mutating func layout(
    _ t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if let r = storage[t] { return r }
    let k = MonomorphicTypeIdentity(p.types.dealiased(t.underlying))
    let r = computeLayout(k, in: &p)
    storage[k] = r
    return r
  }

  /// Returns the layout for `t` in `p`.
  ///
  /// - Precondition: `t` is not an alias.
  private mutating func computeLayout(
    _ t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if isMachineType(t.underlying, in: p) {
      let u = type(t.underlying, as: MachineType.self, in: p)
      return TypeLayout(bytes: abi.layout(u), type: t, parts: [], isEnumLayout: false)
    } else if isEnum(t.underlying, in: p) {
      unimplemented()
    } else if isStruct(t.underlying, in: p) {
      return computeLayout(struct: t, in: &p)
    } else if isTuple(t.underlying, in: p) {
      return computeLayout(tuple: t, in: &p)
    } else {
      unreachable("\(p.show(t.underlying)) doesn't have any layout)")
    }
  }

  /// Returns the layout for struct `t` in `p`.
  private mutating func computeLayout(
    struct t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let d = p.declaration(of: t.underlying)!
    let m = p.parent(containing: d).module
    let ms = p.storage(of: t.underlying, visibleFrom: m)!
    return computeLayout(
      record: t,
      havingMembers: ms.map {
        (type: MonomorphicTypeIdentity($0), label: nil)
      },
      in: &p
    )
  }

  /// Returns the layout for tuple `t` in `p`.
  private mutating func computeLayout(
    tuple t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let u = ConcreteTypeIdentity<Tuple>(uncheckedFrom: t.underlying)
    let (ms, o) = p.types.members(of: u)
    assert(o == false)
    return computeLayout(
      record: t,
      havingMembers: ms.map {
        (type: MonomorphicTypeIdentity($0), label: nil)
      },
      in: &p
    )
  }

  /// Returns the layout for a record `t` in `p` having members `ms`.
  private mutating func computeLayout(
    record t: MonomorphicTypeIdentity,
    havingMembers ms: [(type: MonomorphicTypeIdentity, label: String?)],
    in p: inout Program
  ) -> TypeLayout {
    var b = TypeLayout.Bytes(alignment: 1, size: 0)
    var parts: [TypeLayout.Part] = []
    for (i, m) in ms.enumerated() {
      let c = layout(m.type, in: &p).bytes
      b = b.appending(c)
      parts.append(
        .init(name: m.label ?? String(i), type: m.type, offset: b.size - c.size))
    }
    return TypeLayout(bytes: b, type: t, parts: parts, isEnumLayout: false)
  }

  /// Returns true iff `t` in `p` is of `MachineType`.
  private func isMachineType(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    tag(t, in: p) == MachineType.self
  }

  /// Returns true iff `t` in `p` is of enum type.
  private func isEnum(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    let u = tag(t, in: p)
    if u == Enum.self {
      return true
    } else if u == TypeApplication.self {
      return isEnum(type(t, as: TypeApplication.self, in: p).abstraction, in: p)
    } else {
      return false
    }
  }

  /// Returns true iff `t` in `p` is a `Struct`.
  private func isStruct(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    let u = tag(t, in: p)
    if u == Struct.self {
      return true
    } else if u == TypeApplication.self {
      return isStruct(type(t, as: TypeApplication.self, in: p).abstraction, in: p)
    } else {
      return false
    }
  }

  /// Returns true iff `t` in `p` is a `Tuple`.
  private func isTuple(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    tag(t, in: p) == Tuple.self
  }

  /// Returns the type identified by `t` in `p`, cast to `U`.
  private func type<U: TypeTree>(
    _ t: AnyTypeIdentity, as u: U.Type,
    in p: Program
  ) -> U {
    p.types[p.types.cast(t, to: u)!]
  }

  /// Returns the tag of `t` in `p`.
  private func tag(_ t: AnyTypeIdentity, in p: Program) -> any TypeTree.Type {
    p.types.tag(of: t).value
  }
}
