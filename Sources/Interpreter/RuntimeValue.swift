import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
enum RuntimeValue: Hashable, Sendable {

  /// An instance of a `MachineType`.
  case scalar(BuiltinValue)

  /// The sequence of component values of given type.
  ///
  /// For product types, the value of each stored property in declaration order.
  /// For enum types, the value of the active case followed by the value of
  /// discriminator.
  case composite([RuntimeValue], ofType: MonomorphicTypeIdentity)

  /// A runtime type witness identifying a concrete Hylo type.
  case typeWitness(TypeWitnessValue)

  /// The stored `MachineType` value, or `nil` if `self` is not an instance of
  /// a `MachineType`.
  fileprivate var builtin: BuiltinValue? {
    switch self {
    case .scalar(let value): value
    case .composite(_, _): nil
    case .typeWitness(_): nil
    }
  }

  /// The component values of `self` declaration order.
  fileprivate var parts: [RuntimeValue] {
    switch self {
    case .scalar(_): []
    case .composite(let components, _): components
    case .typeWitness(_): []
    }
  }

}

extension RuntimeValue {

  /// Creates a `w`-bit integer storing the two's-complement representation of `n`.
  public init(_ n: BigInt, bitWidth w: UInt8) {
    self = .scalar(BuiltinValue(n, bitWidth: w))
  }

  /// Creates an instance of `MachineType.i(1)`.
  public init(_ b: Bool) {
    self = .scalar(BuiltinValue(b))
  }

  /// The value of the stored `i1`, if any.
  public var i1: Bool? { builtin?.i1 }

  /// The value of the stored `i8`, if any.
  public var i8: UInt8? { builtin?.i8 }

  /// The value of the stored `i16`, if any.
  public var i16: UInt16? { builtin?.i16 }

  /// The value of the stored `i32`, if any.
  public var i32: UInt32? { builtin?.i32 }

  /// The value of the stored `i64`, if any.
  public var i64: UInt64? { builtin?.i64 }

  /// The value of the stored `i128`, if any.
  public var i128: UInt128? { builtin?.i128 }

  /// The magnitude of stored integer value, if any.
  public var asUInt128: UInt128? { builtin?.asUInt128 }

}

extension RuntimeValue {

  /// Creates a value of type `t` (as defined in `p`) by interpreting its byte
  /// representation `storage` according to the layout provided by `layouts`.
  public init(
    _ storage: ArraySlice<UInt8>,
    type t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    layouts: inout LayoutComputer
  ) {
    let unwrappedType = p.underlyingType(t.underlying)
    switch p.tag(unwrappedType) {
    case MachineType.self:
      let v = p.type(unwrappedType, as: MachineType.self)
      self = .scalar(.init(storage, type: v, layouts: &layouts))
    case Struct.self, Tuple.self:
      self = .init(record: storage, type: t, definedIn: &p, layouts: &layouts)
    case Enum.self:
      self = .init(enum: storage, type: t, definedIn: &p, layouts: &layouts)
    case TypeWitness.self:
      let v = BuiltinValue(storage, type: .i(64), layouts: &layouts)
      self = .typeWitness(MonomorphicTypeIdentity(bits: v.i64!))
    default: unreachable()
    }
  }

  /// Creates a type witness of `t`.
  public init(witnessOf t: MonomorphicTypeIdentity) {
    self = .typeWitness(t)
  }

  /// Creates a value for record type `t`, defined in `p`, by interpreting its
  /// byte representation `storage` according to the layout provided by `layouts`.
  private init(
    record storage: ArraySlice<UInt8>,
    type t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    layouts: inout LayoutComputer
  ) {
    let l = layouts.layout(t, in: &p)
    let parts =
      l.parts.map {
        RuntimeValue($0, parentRepresentation: storage, program: &p, layouts: &layouts)
      }
    self = .composite(parts, ofType: t)
  }

  /// Creates a value of enum type `t`, defined in `p`, by interpreting its
  /// byte representation `storage` according to the layout provided by `layouts`.
  private init(
    enum storage: ArraySlice<UInt8>,
    type t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    layouts: inout LayoutComputer
  ) {
    let l = layouts.layout(t, in: &p)

    let discriminator = RuntimeValue(
      l.discriminator, parentRepresentation: storage, program: &p, layouts: &layouts)

    let activeCaseIndex = Int(discriminator.asUInt128!)
    let activeCase = RuntimeValue(
      l.parts[activeCaseIndex], parentRepresentation: storage,
      program: &p, layouts: &layouts)

    self = .composite([activeCase, discriminator], ofType: t)
  }

  /// Creates a value for `part` by interpreting the byte representation of its
  /// parent according to the layout provided by `layouts` in `program`.
  private init(
    _ part: TypeLayout.Part,
    parentRepresentation storage: ArraySlice<UInt8>,
    program: inout Program,
    layouts: inout LayoutComputer
  ) {
    let partStart = storage.startIndex + part.offset
    let partSize = layouts.layout(part.type, in: &program).size
    let bytes = storage[partStart..<partStart + partSize]
    self = .init(bytes, type: part.type, definedIn: &program, layouts: &layouts)
  }

}

extension RuntimeValue {

  /// Returns the memory representation of `self` as laid out by `typeLayouts`
  /// for `program`.
  public func bytes(
    laidOutUsing typeLayouts: inout LayoutComputer,
    for program: inout Program
  ) -> [UInt8] {
    switch self {
    case .scalar(let value):
      return value.bytes(laidOutUsing: &typeLayouts)
    case .composite(_, let type):
      switch program.tag(type.underlying) {
      case Struct.self, Tuple.self:
        return bytes(ofStoredRecord: type, definedIn: &program, laidOutUsing: &typeLayouts)
      case Enum.self:
        return bytes(ofStoredEnum: type, definedIn: &program, laidOutUsing: &typeLayouts)
      default:
        unreachable("A composite type must be a struct, tuple, or enum.")
      }
    case .typeWitness(let typeIdentity):
      return BuiltinValue.i64(typeIdentity.bits).bytes(laidOutUsing: &typeLayouts)
    }
  }

  /// Returns the memory representation of stored record type `t`, defined in `p`
  /// as laid out by `typeLayouts`.
  private func bytes(
    ofStoredRecord t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    laidOutUsing typeLayouts: inout LayoutComputer
  ) -> [UInt8] {
    assert(t == p.type(self))
    let l = typeLayouts.layout(t, in: &p)
    var bytes = [UInt8](repeating: 0, count: l.size)

    for (value, layout) in zip(parts, l.parts) {
      let partBytes = value.bytes(laidOutUsing: &typeLayouts, for: &p)
      bytes[layout.offset..<layout.offset + partBytes.count] = partBytes[...]
    }

    return bytes
  }

  /// Returns the memory representation of stored enum `t`, defined in `p`
  /// as laid out by `typeLayouts`.
  private func bytes(
    ofStoredEnum t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    laidOutUsing typeLayouts: inout LayoutComputer
  ) -> [UInt8] {
    assert(t == p.type(self))
    let l = typeLayouts.layout(t, in: &p)
    var bytes = [UInt8](repeating: 0, count: l.size)

    let discriminatorBytes = parts[1].bytes(laidOutUsing: &typeLayouts, for: &p)
    bytes[l.discriminator.offset..<l.discriminator.offset + discriminatorBytes.count] =
      discriminatorBytes[...]

    let activeCaseIndex = Int(parts[1].asUInt128!)
    let activeCaseBytes = parts[0].bytes(laidOutUsing: &typeLayouts, for: &p)
    let activeCaseOffset = l.parts[activeCaseIndex].offset
    bytes[activeCaseOffset..<activeCaseOffset + activeCaseBytes.count] = activeCaseBytes[...]

    return bytes
  }

}

extension UnsafeRawBufferPointer {

  /// Returns `true` iff the buffer's base address is aligned to `alignment`.
  fileprivate func isAligned(to alignment: Int) -> Bool {
    precondition(alignment > 0)
    return Int(bitPattern: baseAddress!) % alignment == 0
  }

}

extension Program {

  /// Returns the type of `v` in `self`.
  fileprivate mutating func type(_ v: RuntimeValue) -> MonomorphicTypeIdentity {
    switch v {
    case .scalar(let value): .init(types.demand(value.type).erased)
    case .composite(_, let type): type
    case .typeWitness(_): .init(types.demand(TypeWitness()).erased)
    }
  }

}
