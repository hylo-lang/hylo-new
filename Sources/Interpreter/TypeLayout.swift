import FrontEnd
import Utilities

/// The layout of a type in memory, including the positions of its parts.
struct TypeLayout: Regular {

  /// Memory layout of a type, without any detail about parts.
  public struct Bytes: Regular {
    /// The minimum alignment of an instance.
    let alignment: Int

    /// The number of bytes occupied by an instance.
    let size: Int

  }

  /// A (potential, in the case of enum types) named or unnambed member of a type.
  public struct Member: Regular {
    /// The name if any (i.e. tuple label or stored property name).
    public let name: String?

    /// The type of the member.
    public let type: MonomorphicTypeIdentity
  }

  /// A (potential, in the case of enum types) part of `type` and
  /// where it is stored in a `type` instance.
  public struct Part: Regular {
    /// The name if any (i.e. tuple label or stored property name).
    public let name: String?

    /// The type of the part.
    public let type: MonomorphicTypeIdentity

    /// The byte offset of the part with respect to the layout.
    public let offset: Int
  }

  /// Aggregate properties of this layout.
  public let whole: Bytes

  /// The minimum alignment of an instance.
  public var alignment: Int { whole.alignment }

  /// The number of bytes occupied by an instance.
  public var size: Int { whole.size }

  /// The type whose layout is described by `self`.
  public let type: MonomorphicTypeIdentity

  /// The structure.
  ///
  /// For product types, info for each stored property in storage order.
  /// For enum types, info for each case when it is active, followed by info
  /// for the discriminator.
  /// Empty otherwise (built-in types).
  public let parts: [Part]

  /// True iff `self` is the layout of an enum type, which changes how
  /// its `parts` are interpreted.
  public let isEnumLayout: Bool
}

extension UnsignedInteger {

  /// Returns `self` rounded up to the nearest multiple of `n`.
  ///
  /// - Precondition: `n > 0`.
  internal func roundedUp(toNearestMultipleOf n: Self) -> Self {
    let r = self % n
    return (r == 0) ? self : self + (n - r)
  }

}

extension TypeLayout.Bytes {

  /// Returns the layout of the tuple `(S, T)`, where `S` and `T` are types whose layout is
  /// represented by `self` and `t` respectively.
  ///
  /// - Note: the `T` instance is stored `t.size` bytes before the end of the tuple.
  func appending(_ t: Self) -> Self {
    let r = UInt(size).roundedUp(toNearestMultipleOf: UInt(t.alignment))
    return .init(
      alignment: Int(lcm(self.alignment, t.alignment)),
      size: Int(r) + t.size)
  }

}
