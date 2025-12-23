import BigInt

extension BigInt {

  /// Parses an instance from a Hylo integer literal, returning `nil` if parsing failed.
  internal init?<T: StringProtocol>(hyloLiteral literal: T) {
    if literal.starts(with: "-") {
      if let m = BigUInt(hyloLiteral: literal.dropFirst()) {
        self.init(sign: .minus, magnitude: m)
      } else {
        return nil
      }
    } else {
      if let m = BigUInt(hyloLiteral: literal) {
        self.init(sign: .plus, magnitude: m)
      } else {
        return nil
      }
    }
  }

}

extension BigUInt {

  /// Parses an instance from a Hylo integer literal, returning `nil` if parsing failed.
  internal init?<T: StringProtocol>(hyloLiteral literal: T) {
    switch literal.prefix(2) {
    case "0b":
      self.init(literal.dropFirst(2).sans("_"), radix: 2)
    case "0o":
      self.init(literal.dropFirst(2).sans("_"), radix: 8)
    case "0x":
      self.init(literal.dropFirst(2).sans("_"), radix: 16)
    default:
      self.init(literal.sans("_"))
    }
  }

}

extension StringProtocol {

  /// Returns `self` with each occurrence of `c` removed.
  fileprivate func sans(_ c: Character) -> String {
    .init(filter({ (a) in a != c }))
  }

}
