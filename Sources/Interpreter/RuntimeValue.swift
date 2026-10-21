import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
enum RuntimeValue {

  /// An instance of a `MachineType`.
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
  public init(_ n: BigInt, bitWidth w: UInt8) {
    precondition(w == 1 || w == 8 || w == 16 || w == 32 || w == 64 || w == 128)

    self = .scalar(BuiltinValue(n, bitWidth: w))
  }

  /// Creates an instance of `MachineType.i(1)`.
  public init(_ b: Bool) {
    self = .scalar(BuiltinValue(b))
  }

  /// The boolean value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(1)`.
  public var asBool: Bool { asBuiltin.asBool }

  /// The 8-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(8)`.
  public var asUInt8: UInt8 { asBuiltin.asUInt8 }

  /// The 16-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(16)`.
  public var asUInt16: UInt16 { asBuiltin.asUInt16 }

  /// The 32-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(32)`.
  public var asUInt32: UInt32 { asBuiltin.asUInt32 }

  /// The 64-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(64)`.
  public var asUInt64: UInt64 { asBuiltin.asUInt64 }

  /// The 128-bit unsigned value.
  ///
  /// - Precondition: `self` is an instance of `MachineType.i(128)`.
  public var asUInt128: UInt128 { asBuiltin.asUInt128 }

  /// Returns the unsigned interpretation of `self` as an integer of type `t`.
  ///
  /// - Precondition: `self` is a value of type `t`.
  public func unsignedIntValue(as t: MachineType) -> UInt128 {
    switch t {
    case .i(let w):
      switch w {
      case 8: UInt128(asUInt8)
      case 16: UInt128(asUInt16)
      case 32: UInt128(asUInt32)
      case 64: UInt128(asUInt64)
      case 128: asUInt128
      default: preconditionFailure()
      }
    default: preconditionFailure()
    }
  }

}

extension RuntimeValue {

  /// Creates a value of type `t`, defined in `p`, by interpreting its byte
  /// representation `bs` according to the layout provided by `l`.
  public init(
    ofType t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy l: inout LayoutComputer
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

  /// Creates a value of type `t` by interpreting its byte representation `bs`
  /// according to the layout provided by `c`.
  private init(
    ofType t: MachineType,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy c: inout LayoutComputer
  ) {
    switch t {
    case .i(let n):
      let v = BigInt(unsignedFrom: bs, storedIn: c.abi.byteOrder)
      self = .scalar(BuiltinValue(v, bitWidth: n))
    case .word:
      let v = BigInt(unsignedFrom: bs, storedIn: c.abi.byteOrder)
      self = .scalar(BuiltinValue(v, bitWidth: c.abi.bitsInAPointer))
    default: unimplemented("floats and ptr are not supported yet.")
    }
  }

  /// Creates a value for record type `t`, defined in `p`, by interpreting its
  /// byte representation `bs` according to the layout provided by `c`.
  private init(
    record t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy c: inout LayoutComputer
  ) {
    let l = c.layout(t, in: &p)
    let parts =
      l.parts.map {
        RuntimeValue(
          part: $0, definedIn: &p,
          havingByteRepresentationOfParent: bs, providedBy: &c)
      }
    self = .composite(parts)
  }

  /// Creates a value of enum type `t`, defined in `p`, by interpreting its
  /// byte representation `bs` according to the layout provided by `c`.
  private init(
    enum t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    havingByteRepresentation bs: ArraySlice<UInt8>,
    providedBy c: inout LayoutComputer
  ) {
    let l = c.layout(t, in: &p)

    let discriminator = RuntimeValue(
      part: l.discriminator, definedIn: &p,
      havingByteRepresentationOfParent: bs, providedBy: &c)

    let discriminatorType = p.type(l.discriminator.type.underlying, as: MachineType.self)
    let activeCaseIndex = Int(discriminator.unsignedIntValue(as: discriminatorType))
    let activeCase = RuntimeValue(
      part: l.parts[activeCaseIndex], definedIn: &p,
      havingByteRepresentationOfParent: bs, providedBy: &c)

    self = .composite([activeCase, discriminator])
  }

  /// Creates a value for `part`, defined in `p`, by interpreting the byte
  /// representation `bs` of `part`'s immediate parent according to the layout
  /// provided by `c`.
  private init(
    part: TypeLayout.Part,
    definedIn p: inout Program,
    havingByteRepresentationOfParent bs: ArraySlice<UInt8>,
    providedBy c: inout LayoutComputer
  ) {
    let n = c.layout(part.type, in: &p).size
    let bytes = bs[bs.startIndex + part.offset..<bs.startIndex + part.offset + n]
    self = RuntimeValue(
      ofType: part.type, definedIn: &p,
      havingByteRepresentation: bytes, providedBy: &c)
  }

}

extension RuntimeValue {

  /// Returns the memory representation of stored `t`, defined in `p`
  /// as laid out by `typeLayouts`.
  public func bytes(
    ofStored t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    laidOutUsing typeLayouts: inout LayoutComputer
  ) -> [UInt8] {
    switch self {
    case .scalar(let value):
      let valueType = p.type(t.underlying, as: MachineType.self)
      return value.bytes(ofStored: valueType, laidOutUsing: &typeLayouts)
    case .composite(_):
      let typeTag = p.tag(t.underlying)
      if typeTag == Struct.self || typeTag == Tuple.self {
        return bytes(ofStoredRecord: t, definedIn: &p, laidOutUsing: &typeLayouts)
      } else if typeTag == Enum.self {
        return bytes(ofStoredEnum: t, definedIn: &p, laidOutUsing: &typeLayouts)
      } else {
        unreachable("A composite type must be a struct, tuple, or enum.")
      }
    }
  }

  /// Returns the memory representation of stored record type `t`, defined in `p`
  /// as laid out by `typeLayouts`.
  private func bytes(
    ofStoredRecord t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    laidOutUsing typeLayouts: inout LayoutComputer
  ) -> [UInt8] {
    let l = typeLayouts.layout(t, in: &p)
    var bytes = [UInt8](repeating: 0, count: l.size)

    for (partValue, partInfo) in zip(parts, l.parts) {
      let partBytes = partValue.bytes(
        ofStored: partInfo.type,
        definedIn: &p, laidOutUsing: &typeLayouts)
      bytes[partInfo.offset..<partInfo.offset + partBytes.count] = partBytes[...]
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
    let l = typeLayouts.layout(t, in: &p)
    var bytes = [UInt8](repeating: 0, count: l.size)

    let discriminator =
      parts[1].bytes(
        ofStored: l.discriminator.type,
        definedIn: &p, laidOutUsing: &typeLayouts)
    let discriminatorOffset = l.discriminator.offset
    let discriminatorType =
      p.type(l.discriminator.type.underlying, as: MachineType.self)
    bytes[discriminatorOffset..<discriminatorOffset + discriminator.count] = discriminator[...]

    let activeCaseIndex =
      Int(parts[1].unsignedIntValue(as: discriminatorType))
    let activeCase = parts[0].bytes(
      ofStored: l.parts[activeCaseIndex].type,
      definedIn: &p, laidOutUsing: &typeLayouts)
    let activeCaseOffset = l.parts[activeCaseIndex].offset
    bytes[activeCaseOffset..<activeCaseOffset + activeCase.count] = activeCase[...]

    return bytes
  }

}
