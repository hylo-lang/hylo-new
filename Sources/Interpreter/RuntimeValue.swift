import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
enum RuntimeValue {

  /// When self is an instance of a `MachineType`.
  case scalar(BuiltinValue)

  /// The sequence of component values of a composite type.
  ///
  /// For product types, the value of each stored property in declaration order.
  /// For enum types, the value of the active case followed by the value of
  /// discriminator.
  case composite([RuntimeValue])

  /// The underlying builtin value.
  ///
  /// - Precondition: `self` is an instance of a `MachineType`.
  fileprivate var asBuiltin: BuiltinValue {
    switch self {
    case .scalar(let v): v
    case .composite(_): preconditionFailure("`self` is not an instance of scalar type.")
    }
  }

  /// The component values of a composite value in declaration order.
  ///
  /// - Precondition: `self` is an instance of a composite type.
  fileprivate var parts: [RuntimeValue] {
    switch self {
    case .scalar(_): preconditionFailure("`self` is not an instance of composite type.")
    case .composite(let vs): vs
    }
  }

}

extension RuntimeValue {

  /// Creates a `w`-bit integer having value `n`.
  public init(integer n: BigInt, bitWidth w: UInt8) {
    precondition(w == 1 || w == 8 || w == 16 || w == 32 || w == 64 || w == 128)

    self = .scalar(BuiltinValue(integer: n, bitWidth: w))
  }

  /// Creates an instance of `MachineType.i(1)`.
  public init(bool b: Bool) {
    self = .scalar(BuiltinValue(bool: b))
  }

  /// The boolean value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(1)`.
  public var asBool: Bool { asBuiltin.asBool }

  /// The 8-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(8)`.
  public var asI8: UInt8 { asBuiltin.asI8 }

  /// The 16-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(16)`.
  public var asI16: UInt16 { asBuiltin.asI16 }

  /// The 32-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(32)`.
  public var asI32: UInt32 { asBuiltin.asI32 }

  /// The 64-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(64)`.
  public var asI64: UInt64 { asBuiltin.asI64 }

  /// The 128-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(128)`.
  public var asI128: UInt128 { asBuiltin.asI128 }

  /// Returns the unsigned interpretation of `self` as an integer of type `t`.
  ///
  /// - Precondition: `self` is a value of type `t`.
  public func unsignedIntValue(as t: MachineType) -> UInt128 {
    switch t {
    case .i(let w):
      switch w {
      case 8: UInt128(asI8)
      case 16: UInt128(asI16)
      case 32: UInt128(asI32)
      case 64: UInt128(asI64)
      case 128: asI128
      default: preconditionFailure()
      }
    default: preconditionFailure()
    }
  }

}

extension RuntimeValue {

  /// Creates a value of type `t`, defined in `p`, from its byte
  /// representation `bs`, interpreted according to the layout provided by `l`.
  public init(
    ofType t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy l: inout TypeLayoutCache
  ) {
    let u = p.underlyingType(t.underlying)
    let s = p.tag(u)

    if s == MachineType.self {
      let v = p.type(u, as: MachineType.self)
      self = RuntimeValue(ofType: v, havingByteRepresentation: bs, providedBy: &l)
    } else if s == Struct.self || s == Tuple.self {
      self = RuntimeValue(
        record: t, definedIn: &p,
        havingByteRepresentation: bs, providedBy: &l)
    } else if s == Enum.self {
      self = RuntimeValue(
        enum: t, definedIn: &p,
        havingByteRepresentation: bs, providedBy: &l)
    } else {
      unreachable()
    }
  }

  /// Creates a value of type `t` from its byte representation `bs`, interpreted
  /// according to the layout provided by `c`.
  private init(
    ofType t: MachineType,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy c: inout TypeLayoutCache
  ) {
    switch t {
    case .i(let n):
      let v = BigInt(byteRepresentation: bs, inByteOrder: c.abi.byteOrder)
      self = .scalar(BuiltinValue(integer: v, bitWidth: n))
    case .word:
      let v = BigInt(byteRepresentation: bs, inByteOrder: c.abi.byteOrder)
      self = .scalar(BuiltinValue(integer: v, bitWidth: c.abi.bitsInAPointer))
    default: unimplemented("floats and ptr are not supported yet.")
    }
  }

  /// Creates a value for record type `t` defined in `p` from its byte
  /// representation `bs`, interpreted according to the layout provided by `c`.
  private init(
    record t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy c: inout TypeLayoutCache
  ) {
    let l = c.layout(t, in: &p)
    let parts =
      l.parts.map {
        RuntimeValue(
          part: $0, definedIn: &p,
          byteRepresentationOfParent: bs, andLayoutProvidedBy: &c)
      }
    self = .composite(parts)
  }

  /// Creates a value for enum type `t` defined in `p` from its byte
  /// representation `bs`, interpreted according to the layout provided by `c`.
  private init(
    enum t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy c: inout TypeLayoutCache
  ) {
    let l = c.layout(t, in: &p)

    let discriminator = RuntimeValue(
      part: l.discriminator, definedIn: &p,
      byteRepresentationOfParent: bs, andLayoutProvidedBy: &c)

    let discriminatorType = p.type(l.discriminator.type.underlying, as: MachineType.self)
    let activeCaseIndex = Int(discriminator.unsignedIntValue(as: discriminatorType))
    let activeCase = RuntimeValue(
      part: l.parts[activeCaseIndex], definedIn: &p,
      byteRepresentationOfParent: bs, andLayoutProvidedBy: &c)

    self = .composite([activeCase, discriminator])
  }

  /// Creates a value for `part` defined in `p` from the byte
  /// representation `bs` of its parent, interpreted according to the layout
  /// provided by `c`.
  private init(
    part: TypeLayout.Part,
    definedIn p: inout Program,
    byteRepresentationOfParent bs: ArraySlice<UInt8>,
    andLayoutProvidedBy c: inout TypeLayoutCache
  ) {
    let n = c.layout(part.type, in: &p).size
    let bytes = bs[bs.startIndex + part.offset..<bs.startIndex + part.offset + n]
    self = RuntimeValue(
      ofType: part.type, definedIn: &p,
      havingByteRepresentation: bytes, providedBy: &c)
  }

}

extension RuntimeValue {

  /// Returns the byte representation of `self` as a value of type `t`, defined
  /// in `p`, following the type layout of `t` provided by `c`.
  ///
  /// - Precondition: `self` is an instance of `t`.
  public func byteRepresentation(
    as t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    usingLayoutsFrom c: inout TypeLayoutCache
  ) -> [UInt8] {
    switch self {
    case .scalar(let v):
      let u = p.type(t.underlying, as: MachineType.self)
      return v.byteRepresentation(as: u, usingLayoutsFrom: &c)
    case .composite(_):
      let u = p.tag(t.underlying)
      if u == Struct.self || u == Tuple.self {
        return byteRepresentationOfRecord(as: t, definedIn: &p, usingLayoutsFrom: &c)
      } else if u == Enum.self {
        return byteRepresentationOfEnum(as: t, definedIn: &p, usingLayoutsFrom: &c)
      } else {
        unreachable("A composite type must be a struct, tuple, or enum.")
      }
    }
  }

  /// Returns the byte representation of `self` as a value of record type `t`,
  /// defined in `p`, following the layout of `t` provided by `c`.
  ///
  /// - Precondition: `self` is an instance of `t`.
  private func byteRepresentationOfRecord(
    as t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    usingLayoutsFrom c: inout TypeLayoutCache
  ) -> [UInt8] {
    let l = c.layout(t, in: &p)
    var r = [UInt8](repeating: 0, count: l.size)

    for (partValue, partInfo) in zip(parts, l.parts) {
      let partBytes = partValue.byteRepresentation(
        as: partInfo.type,
        definedIn: &p, usingLayoutsFrom: &c)
      r[partInfo.offset..<partInfo.offset + partBytes.count] = partBytes[...]
    }

    return r
  }

  /// Returns the byte representation of `self` as a value of enum type `t`,
  /// defined in `p`, following the layout of `t` provided by `c`.
  ///
  /// - Precondition: `self` is an instance of `t`.
  private func byteRepresentationOfEnum(
    as t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    usingLayoutsFrom c: inout TypeLayoutCache
  ) -> [UInt8] {
    let l = c.layout(t, in: &p)
    var r = [UInt8](repeating: 0, count: l.size)

    let discriminator =
      parts[1].byteRepresentation(
        as: l.discriminator.type,
        definedIn: &p, usingLayoutsFrom: &c)
    let discriminatorOffset = l.discriminator.offset
    let discriminatorType =
      p.type(l.discriminator.type.underlying, as: MachineType.self)
    r[discriminatorOffset..<discriminatorOffset + discriminator.count] = discriminator[...]

    let activeCaseIndex =
      Int(parts[1].unsignedIntValue(as: discriminatorType))
    let activeCase = parts[0].byteRepresentation(
      as: l.parts[activeCaseIndex].type,
      definedIn: &p, usingLayoutsFrom: &c)
    let activeCaseOffset = l.parts[activeCaseIndex].offset
    r[activeCaseOffset..<activeCaseOffset + activeCase.count] = activeCase[...]

    return r
  }

}
