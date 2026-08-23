import FrontEnd

extension IntegerPredicate {

  /// Returns the result of `self(lhs, rhs)`.
  public func callAsFunction(_ lhs: UInt128, _ rhs: UInt128) -> Bool {
    switch self {
    case .eq: lhs == rhs
    case .ne: lhs != rhs
    case .ugt: lhs > rhs
    case .uge: lhs >= rhs
    case .ult: lhs < rhs
    case .ule: lhs <= rhs
    case .sgt: Int128(bitPattern: lhs) > Int128(bitPattern: rhs)
    case .sge: Int128(bitPattern: lhs) >= Int128(bitPattern: rhs)
    case .slt: Int128(bitPattern: lhs) < Int128(bitPattern: rhs)
    case .sle: Int128(bitPattern: lhs) <= Int128(bitPattern: rhs)
    }
  }

  /// Returns the result of `self(lhs, rhs)`.
  public func callAsFunction(_ lhs: UInt64, _ rhs: UInt64) -> Bool {
    switch self {
    case .eq: lhs == rhs
    case .ne: lhs != rhs
    case .ugt: lhs > rhs
    case .uge: lhs >= rhs
    case .ult: lhs < rhs
    case .ule: lhs <= rhs
    case .sgt: Int64(bitPattern: lhs) > Int64(bitPattern: rhs)
    case .sge: Int64(bitPattern: lhs) >= Int64(bitPattern: rhs)
    case .slt: Int64(bitPattern: lhs) < Int64(bitPattern: rhs)
    case .sle: Int64(bitPattern: lhs) <= Int64(bitPattern: rhs)
    }
  }

  /// Returns the result of `self(lhs, rhs)`.
  public func callAsFunction(_ lhs: UInt32, _ rhs: UInt32) -> Bool {
    switch self {
    case .eq: lhs == rhs
    case .ne: lhs != rhs
    case .ugt: lhs > rhs
    case .uge: lhs >= rhs
    case .ult: lhs < rhs
    case .ule: lhs <= rhs
    case .sgt: Int32(bitPattern: lhs) > Int32(bitPattern: rhs)
    case .sge: Int32(bitPattern: lhs) >= Int32(bitPattern: rhs)
    case .slt: Int32(bitPattern: lhs) < Int32(bitPattern: rhs)
    case .sle: Int32(bitPattern: lhs) <= Int32(bitPattern: rhs)
    }
  }

  /// Returns the result of `self(lhs, rhs)`.
  public func callAsFunction(_ lhs: UInt16, _ rhs: UInt16) -> Bool {
    switch self {
    case .eq: lhs == rhs
    case .ne: lhs != rhs
    case .ugt: lhs > rhs
    case .uge: lhs >= rhs
    case .ult: lhs < rhs
    case .ule: lhs <= rhs
    case .sgt: Int16(bitPattern: lhs) > Int16(bitPattern: rhs)
    case .sge: Int16(bitPattern: lhs) >= Int16(bitPattern: rhs)
    case .slt: Int16(bitPattern: lhs) < Int16(bitPattern: rhs)
    case .sle: Int16(bitPattern: lhs) <= Int16(bitPattern: rhs)
    }
  }

  /// Returns the result of `self(lhs, rhs)`.
  public func callAsFunction(_ lhs: UInt8, _ rhs: UInt8) -> Bool {
    switch self {
    case .eq: lhs == rhs
    case .ne: lhs != rhs
    case .ugt: lhs > rhs
    case .uge: lhs >= rhs
    case .ult: lhs < rhs
    case .ule: lhs <= rhs
    case .sgt: Int8(bitPattern: lhs) > Int8(bitPattern: rhs)
    case .sge: Int8(bitPattern: lhs) >= Int8(bitPattern: rhs)
    case .slt: Int8(bitPattern: lhs) < Int8(bitPattern: rhs)
    case .sle: Int8(bitPattern: lhs) <= Int8(bitPattern: rhs)
    }
  }

  /// Returns result of `self(lhs, rhs)`, where `lhs` and `rhs` are `w`-bit integers.
  internal func callAsFunction(
    _ lhs: RuntimeValue, _ rhs: RuntimeValue,
    bitWidth w: Int
  ) -> Bool {
    switch w {
    case 1: self(lhs.bool ? UInt8(1) : 0, rhs.bool ? UInt8(1) : 0)
    case 8: self(lhs.i8, rhs.i8)
    case 16: self(lhs.i16, rhs.i16)
    case 32: self(lhs.i32, rhs.i32)
    case 64: self(lhs.i64, rhs.i64)
    case 128: self(lhs.i128, rhs.i128)
    default: fatalError("Unknown builtin integer size \(w)")
    }
  }

}
