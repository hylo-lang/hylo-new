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
    let r = computeLayout(t, in: &p)
    storage[t] = r
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
    } else if isTuple(t.underlying, in: p) {
      return computeLayout(tuple: t, in: &p)
    } else if hasRecordLayout(t.underlying, in: p) {
      return computeLayout(struct: t, in: &p)
    } else if hasEnumLayout(t.underlying, in: p) {
      return computeLayout(enum: t, in: &p)
    } else {
      unreachable("\(p.show(t.underlying)) doesn't have any layout)")
    }
  }

  /// Returns the layout for struct `t` in `p`.
  private mutating func computeLayout(
    struct t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let ms = storage(t.underlying, in: &p)
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

  /// Returns the layout for an enum `t` in `p`.
  private mutating func computeLayout(
    enum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if isTaggedEnum(t.underlying, in: p) {
      computeLayout(taggedEnum: t, in: &p)
    } else {
      computeLayout(rawEnum: t, in: &p)
    }
  }

  /// Returns the layout for a tagged enum `t` in `p`.
  private mutating func computeLayout(
    taggedEnum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let basis = storage(t.underlying, in: &p)
      .map { layout(MonomorphicTypeIdentity($0), in: &p) }

    if basis.count == 0 {
      return TypeLayout(
        bytes: .init(alignment: 1, size: 0), type: t,
        parts: [], isEnumLayout: true)
    }

    let discriminator = abi.enumDiscriminator(count: basis.count, in: &p)
    let discriminatorLayout = layout(discriminator, in: &p)

    let payloadBytes = TypeLayout.Bytes(
      alignment: basis.lazy.map(\.alignment).max()!,
      size: basis.lazy.map(\.size).max()!)

    let payloadFirst = payloadBytes.appending(discriminatorLayout.bytes)
    let discriminatorFirst = discriminatorLayout.bytes.appending(payloadBytes)

    let payloadOffset: Int
    let discriminatorOffset: Int
    let l: TypeLayout.Bytes

    if payloadFirst.size < discriminatorFirst.size {
      l = payloadFirst
      payloadOffset = 0
      discriminatorOffset = l.size - discriminatorLayout.size
    } else {
      l = discriminatorFirst
      payloadOffset = l.size - payloadBytes.size
      discriminatorOffset = 0
    }

    return TypeLayout(
      bytes: l,
      type: t,
      parts:
        basis.map { .init(name: String(describing: $0.type), type: $0.type, offset: payloadOffset) }
        + [.init(name: "discriminator", type: discriminator, offset: discriminatorOffset)],
      isEnumLayout: true)
  }

  /// Returns the layout for a raw enum `t` in `p`.
  private mutating func computeLayout(
    rawEnum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    unimplemented()
  }

  /// Returns true iff enum `t` in `p` has a representation.
  ///
  /// - Precondition: `t` has an enum layout.
  private func isTaggedEnum(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    let u = tag(t, in: p)
    if u == Enum.self {
      let d = type(t, as: Enum.self, in: p).declaration
      return p[d].representation == nil
    } else if u == TypeAlias.self {
      return isTaggedEnum(type(t, as: TypeAlias.self, in: p).aliasee, in: p)
    } else if u == TypeApplication.self {
      return isTaggedEnum(type(t, as: TypeApplication.self, in: p).abstraction, in: p)
    } else {
      unreachable()
    }
  }

  /// Returns the types of stored parts of nominal `t` in `p`.
  private func storage(_ t: AnyTypeIdentity, in p: inout Program) -> [AnyTypeIdentity] {
    let d = p.declaration(of: t)!
    let m = p.parent(containing: d).module
    return p.storage(of: t, visibleFrom: m)!
  }

  /// Returns true iff `t` in `p` is of `MachineType`.
  private func isMachineType(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    tag(t, in: p) == MachineType.self
  }

  /// Returns true iff `t` in `p` has enum layout.
  private func hasEnumLayout(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    let u = tag(t, in: p)
    if u == Enum.self {
      return true
    } else if u == TypeAlias.self {
      return hasEnumLayout(type(t, as: TypeAlias.self, in: p).aliasee, in: p)
    } else if u == TypeApplication.self {
      return hasEnumLayout(type(t, as: TypeApplication.self, in: p).abstraction, in: p)
    } else {
      return false
    }
  }

  /// Returns true iff `t` in `p` has a record layout.
  private func hasRecordLayout(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    let u = tag(t, in: p)
    if u == Struct.self {
      return true
    } else if u == TypeApplication.self {
      return hasRecordLayout(type(t, as: TypeApplication.self, in: p).abstraction, in: p)
    } else if u == TypeAlias.self {
      return hasRecordLayout(type(t, as: TypeAlias.self, in: p).aliasee, in: p)
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
