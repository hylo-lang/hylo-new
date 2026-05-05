/// An unambiguous textual description of a type, scope, or declaration known to the compiler.
enum ReservedSymbol: UInt8 {

  /// The `Hylo` module.
  case hylo

  /// `Hylo.Bool`.
  case bool

  /// `Hylo.Int`.
  case int

  /// `Hylo.Int64`.
  case int64

  /// The `Never` type.
  case never

  /// The `Void` type.
  case void

}

extension ReservedSymbol: TextOutputStreamable {

  func write<T: TextOutputStream>(to output: inout T) {
    output.write(Base64Digit(rawValue: rawValue)!.description)
  }

}
