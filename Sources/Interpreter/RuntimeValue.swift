import BigInt
import FrontEnd
import Utilities

/// A value occurring during program execution.
enum RuntimeValue {

  /// An instance of a `MachineType`.
  case scalar(BuiltinValue)

  /// The sequence of component values of given type.
  ///
  /// For product types, the value of each stored property in declaration order.
  /// For enum types, the value of the active case followed by the value of
  /// discriminator.
  case composite([RuntimeValue], ofType: MonomorphicTypeIdentity)

  /// Returns the type of the stored value in `program`.
  public func type(in program: inout Program) -> MonomorphicTypeIdentity {
    switch self {
    case .scalar(let value): .init(program.types.demand(value.type).erased)
    case .composite(_, let type): type
    }
  }

  /// The underlying builtin value.
  ///
  /// - Precondition: `self` is an instance of a `MachineType`.
  fileprivate var asBuiltin: BuiltinValue {
    switch self {
    case .scalar(let v): v
    case .composite(_, _): preconditionFailure("`self` is not an instance of scalar type.")
    }
  }

  /// The component values of a composite value in declaration order.
  ///
  /// - Precondition: `self` is an instance of a composite type.
  fileprivate var parts: [RuntimeValue] {
    switch self {
    case .scalar(_): preconditionFailure("`self` is not an instance of composite type.")
    case .composite(let vs, _): vs
    }
  }

}

extension RuntimeValue {

  /// Creates an integer of type `t` storing the two's-complement representation of `n`.
  public init(_ n: BigInt, ofType t: MachineType) {
    self = .scalar(BuiltinValue(n, ofType: t))
  }

  /// Creates an instance of `MachineType.i(1)`.
  public init(_ b: Bool) {
    self = .scalar(BuiltinValue(b))
  }

  /// The value of the stored `i1`, or `nil` if `self` does not match `.i1(_)`
  public var i1: Bool? { asBuiltin.i1 }

  /// The value of the stored `i8`, or `nil` if `self` does not match `.i8(_)`
  public var i8: UInt8? { asBuiltin.i8 }

  /// The value of the stored `i16`, or `nil` if `self` does not match `.i16(_)`
  public var i16: UInt16? { asBuiltin.i16 }

  /// The value of the stored `i32`, or `nil` if `self` does not match `.i32(_)`
  public var i32: UInt32? { asBuiltin.i32 }

  /// The value of the stored `i64`, or `nil` if `self` does not match `.i64(_)`
  public var i64: UInt64? { asBuiltin.i64 }

  /// The value of the stored `i128`, or `nil` if `self` does not match `.i128(_)`
  public var i128: UInt128? { asBuiltin.i128 }

  /// The value of the stored `word`, or `nil` if `self` doesn't match `.word(_)`
  public var word: UInt128? { asBuiltin.word }

  /// The magnitude of stored integer value.
  public var asUInt128: UInt128 { asBuiltin.asUInt128 }

}

extension RuntimeValue {

  /// Creates a value of type `t`, defined in `p`, by interpreting its byte
  /// representation `storage` according to the layout provided by `layouts`.
  public init(
    _ storage: ArraySlice<UInt8>,
    type t: MonomorphicTypeIdentity,
    definedIn p: inout Program,
    layouts: inout LayoutComputer
  ) {
    let u = p.underlyingType(t.underlying)
    let s = p.tag(u)

    if s == MachineType.self {
      let v = p.type(u, as: MachineType.self)
      self = .init(storage, type: v, layouts: &layouts)
    } else if s == Struct.self || s == Tuple.self {
      self = .init(record: storage, type: t, definedIn: &p, layouts: &layouts)
    } else if s == Enum.self {
      self = .init(enum: storage, type: t, definedIn: &p, layouts: &layouts)
    } else {
      unreachable()
    }
  }

  /// Creates a value of type `t` by interpreting its byte representation `storage`
  /// according to the layout provided by `layouts`.
  private init(
    _ storage: ArraySlice<UInt8>,
    type t: MachineType,
    layouts: inout LayoutComputer
  ) {
    switch t {
    case .i(_):
      let v = BigInt(unsignedFrom: storage, storedIn: layouts.abi.byteOrder)
      self = .scalar(BuiltinValue(v, ofType: t))
    case .word:
      let v = BigInt(unsignedFrom: storage, storedIn: layouts.abi.byteOrder)
      self = .scalar(BuiltinValue(v, ofType: t))
    default: unimplemented("floats and ptr are not supported yet.")
    }
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

    let activeCaseIndex = Int(discriminator.asUInt128)
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
      let typeTag = program.tag(type.underlying)
      if typeTag == Struct.self || typeTag == Tuple.self {
        return bytes(ofStoredRecord: type, definedIn: &program, laidOutUsing: &typeLayouts)
      } else if typeTag == Enum.self {
        return bytes(ofStoredEnum: type, definedIn: &program, laidOutUsing: &typeLayouts)
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
    assert(t == type(in: &p))
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
    assert(t == type(in: &p))
    let l = typeLayouts.layout(t, in: &p)
    var bytes = [UInt8](repeating: 0, count: l.size)

    let discriminatorBytes = parts[1].bytes(laidOutUsing: &typeLayouts, for: &p)
    bytes[l.discriminator.offset..<l.discriminator.offset + discriminatorBytes.count] =
      discriminatorBytes[...]

    let activeCaseIndex = Int(parts[1].asUInt128)
    let activeCaseBytes = parts[0].bytes(laidOutUsing: &typeLayouts, for: &p)
    let activeCaseOffset = l.parts[activeCaseIndex].offset
    bytes[activeCaseOffset..<activeCaseOffset + activeCaseBytes.count] = activeCaseBytes[...]

    return bytes
  }

}
