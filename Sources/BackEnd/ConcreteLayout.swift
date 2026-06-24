import SwiftyLLVM

/// A description of the layout of a Hylo type for a particular target.
internal struct ConcreteLayout {

  /// The size of an instance.
  ///
  /// A footprint denotes either a "fixed" size in bytes, known at compile-time, or a "dynamic"
  /// size determined at run-time. Types with a dynamic size are for values containing flexible
  /// and/or opaque parts. Such values cannot be loaded from memory to register.
  internal struct Footprint {

    /// The raw value of the instance.
    ///
    /// Non-negative numbers represent a fixed size, in bytes. `-1` represents a dynamic size. All
    /// other values are undefined.
    private let raw: Int

    /// The size represented by `self` iff it is fixed.
    internal var fixed: Int? {
      raw >= 0 ? raw : nil
    }

    /// An instance representing a size determined at runtime.
    internal static let dynamic: Footprint = Footprint(raw: -1)

    /// Creates an instance representing a fixed size of `n` bytes.
    internal static func fixed(_ n: Int) -> Footprint {
      precondition(n >= 0)
      return .init(raw: n)
    }

    /// Returns `true` iff `l` denotes a fixed size of `r` bytes.
    internal static func == (l: Self, r: Int) -> Bool {
      (l.raw == r) && (r >= 0)
    }

    /// Returns `true` iff `l` does not denote a fixed size of `r` bytes.
    internal static func != (l: Self, r: Int) -> Bool {
      (l.raw != r) || (r < 0)
    }

    /// Returns `true` iff `l` denotes a fixed size of less than or exactly `r` bytes.
    internal static func <= (l: Self, r: Int) -> Bool {
      UInt(bitPattern: l.raw) < r
    }

  }

  /// The LLVM types of the fields constituting the parts of an instance, if any.
  ///
  /// This property may be empty if the type described by `self` has no stored property, either
  /// because it is opaque or because it is a machine type.
  internal let fields: [LLVMType]

  /// A map from the index of a property to the index of its corresponding LLVM field, or `-1` if that
  /// property's representation is erased.
  ///
  /// - Invariant: the length of `propertyToField` is greater than or equal to that of `fields`.
  internal let propertyToField: [Int]

  /// The size of an instance.
  internal let size: Footprint

  /// The alignment requirement.
  internal let alignment: Int

}
