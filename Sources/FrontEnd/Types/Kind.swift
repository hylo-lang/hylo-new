import Archivist

/// The type of a type constructor.
@Archivable
public struct Kind: Sendable {

  /// The type of a kind's raw value.
  private typealias RawValue = UInt32

  /// Creates an instance with the given raw value.
  private init(rawValue: RawValue) {
    self.rawValue = rawValue
  }

  /// The raw representation of `self`.
  ///
  /// The value of a kind is decoded from a stream of bits, reading from least to most significant.
  /// `0` denotes the kind of proper types and `1` denotes an arrow whose right-hand and left-hand
  /// sides are serialized next, in that order. For instance, the value `0010011` denotes the kind
  /// `(* -> *) -> (* -> *)`.
  private let rawValue: RawValue

  /// If `self` is an arrow, returns its left-hand and right-hand sides.
  public var arrow: (lhs: Kind, rhs: Kind)? {
    if self.rawValue == 0 {
      return nil
    } else {
      let l = bitWidth(component: 2)
      let r = bitWidth(component: 2 << l)
      let a = (rawValue >> 1) & (((1 as RawValue) << l) - 1)
      let b = (rawValue >> (1 + l)) & (((1 as RawValue) << r) - 1)
      return (lhs: .init(rawValue: a), rhs: .init(rawValue: b))
    }
  }

  /// Returns the number of bits in the part of `self` identified by `component`, which is a bit
  /// mask identifiying the least significant bit of `self` or a part thereof.
  private func bitWidth(component m: RawValue) -> Int {
    if (rawValue & m) == 0 {
      return 1
    } else {
      let l = bitWidth(component: m << 1)
      let r = bitWidth(component: m << (1 + l))
      return (1 + l + r)
    }
  }

  /// The kind of proper types (often written `*` in literature).
  public static let proper = Kind(rawValue: 0)

  /// The kind of a higher-order type constructor.
  public static func arrow(_ lhs: Kind, _ rhs: Kind) -> Kind {
    let l = lhs.bitWidth(component: 1)
    let r = rhs.bitWidth(component: 1)
    precondition((l + r) < RawValue.bitWidth, "not enough bits to represent '(\(lhs) -> \(rhs))'")
    return .init(rawValue: 1 | (lhs.rawValue << 1) | (rhs.rawValue << (1 + l)))
  }

}

extension Kind: Equatable {}

extension Kind: Hashable {}

extension Kind: CustomStringConvertible {

  public var description: String {
    if let (a, b) = arrow {
      return "(\(a) -> \(b))"
    } else {
      return "*"
    }
  }

}
