import Foundation

/// Returns the Hylo source code declaring the standard library's integer types.
internal func generateIntegerTypes() -> String {
  var types: [IntegerTypeDefinition] = []

  for bits in [8, 16, 32, 64] {
    types.append(.fixedSize(bits: bits, .signed, includedConformances: .minimal))
    types.append(.fixedSize(bits: bits, .unsigned, includedConformances: .minimal))
  }

  types.append(
    .init(
      name: "Int",
      documentation:
        "/// A signed integer type that can represent any object size on the target platform.",
      builtinType: "word", .signed, .fittingLargestObjectSize, includedConformances: .all))

  types.append(
    .init(
      name: "UInt",
      documentation:
        "/// An unsigned integer type that can represent any object size on the target platform.",
      builtinType: "word", .unsigned, .fittingLargestObjectSize, includedConformances: .minimal))

  return types.map(\.description).joined(separator: "\n")
}

extension IntegerTypeDefinition {

  /// Creates a fixed-size integer type's definition.
  static func fixedSize(
    bits: Int, _ signedness: Signedness, includedConformances: Conformances
  ) -> IntegerTypeDefinition {
    .init(
      name: signedness == .signed ? "Int\(bits)" : "UInt\(bits)",
      documentation: "/// \(prefixed(bits))-bit \(signedness) integer.",
      builtinType: "i\(bits)", signedness, .fixedWidth(bits: bits),
      includedConformances: includedConformances)
  }

}

/// Returns `x` prefixed with an indefinite article.
private func prefixed(_ x: Int) -> String {
  x.description.first == "8" ? "An \(x)" : "A \(x)"
}

/// Whether an integer type is signed or unsigned.
private enum Signedness: String, CustomStringConvertible {

  case signed = "s"
  case unsigned = "u"

  /// The description of the signedness.
  var description: String {
    switch self {
    case .signed: "signed"
    case .unsigned: "unsigned"
    }
  }

  /// The abbreviation used in builtin type names.
  var abbreviated: String { rawValue }

}

/// The size of an integer type.
private enum Size {

  /// The type can represent the size of the largest object in memory on the target platform.
  ///
  /// Equivalent of `size_t`/`ssize_t` in C.
  case fittingLargestObjectSize

  /// The type has exactly `bits` bits.
  case fixedWidth(bits: Int)

}

/// The set of conformances to generate for an integer type.
private enum Conformances {

  /// Provide all conformances.
  case all

  /// Provide only `Movable` and `ExpressibleByIntegerLiteral`.
  case minimal

}

/// Information for emitting a standard library integer type.
private struct IntegerTypeDefinition: CustomStringConvertible {

  /// The exposed name of the generated declaration, e.g., `Int64`.
  let declarationName: String

  /// The documentation of the type, including `///` prefixes.
  let declarationDocumentation: String

  /// The name of the stored underlying builtin type, e.g., `i64`.
  let builtinType: String

  /// Whether the integer is signed.
  let signedness: Signedness

  /// The size of the type.
  let size: Size

  /// The set of conformances to generate.
  let includedConformances: Conformances

  /// Constructs an instance from its parts.
  init(
    name: String, documentation: String, builtinType: String, _ signedness: Signedness,
    _ size: Size, includedConformances: Conformances
  ) {
    self.declarationName = name
    self.declarationDocumentation = documentation
    self.builtinType = builtinType
    self.signedness = signedness
    self.size = size
    self.includedConformances = includedConformances
  }

  /// The code introducing the `abs()` method for signed types, nil otherwise.
  var absMethod: String? {
    signedness == .unsigned
      ? nil
      : """


        /// Returns the absolute value of `self`.
        ///
        /// - Requires: `self` must not be `\(declarationName)`'s minimum value.
        @inline(always)
        public fun abs() -> Self {
          if self < Self.zero() { Self.zero() - self } else { Self(value: self.value) }
        }
      """
  }

  /// The smallest integer `self` can represent.
  var minimumValue: String {
    let bits =
      switch size {
      case .fittingLargestObjectSize:
        // TODO emit Builtin constant for the platform's size_t.
        // See: https://github.com/hylo-lang/hylo-new/issues/331
        64
      case .fixedWidth(let bits):
        bits
      }

    return switch signedness {
    case .signed: "\(-(Int128(1) << (bits - 1)))"
    case .unsigned: "0"
    }
  }

  /// The largest integer `self` can represent.
  var maximumValue: String {
    let bits =
      switch size {
      case .fittingLargestObjectSize:
        // TODO emit Builtin constant for the platform's size_t.
        64
      case .fixedWidth(let bits):
        bits
      }

    return switch signedness {
    case .signed: "\((Int128(1) << (bits - 1)) - 1)"
    case .unsigned: "\((Int128(1) << bits) - 1)"
    }
  }

  /// The source code representation of this type.
  var description: String {
    """
    \(declarationDocumentation)
    @_symbol(\"\(declarationName)\")
    public struct \(declarationName) is Deinitializable {

      /// The raw value of this instance.
      module var value: Builtin.\(builtinType)

      /// Creates an instance with its raw value.
      @inline(always)
      module memberwise init

      /// Creates an instance with value `0`.
      @inline(always)
      public init() {
        &self.value = Builtin.zeroinitializer_\(builtinType)()
      }\(absMethod ?? "")

      @inline(always)
      public static fun min() -> Self {
        \(minimumValue) as Self
      }

      @inline(always)
      public static fun max() -> Self {
        \(maximumValue) as Self
      }

      // MARK: Equatable conformance

      /// Returns `true` iff `self` is equal to `other`.
      @inline(always)
      public fun infix== (other: Self) -> Bool {
        .new(value: Builtin.icmp_eq_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is not equal to `other`.
      @inline(always)
      public fun infix!= (other: Self) -> Bool {
        .new(value: Builtin.icmp_ne_\(builtinType)(self.value, other.value))
      }

      // MARK: Comparable conformance

      /// Returns `true` iff `self` is less than `other`.
      @inline(always)
      public fun infix< (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)lt_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is less than or equal to `other`.
      @inline(always)
      public fun infix<= (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)le_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is greater than `other`.
      @inline(always)
      public fun infix> (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)gt_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is greater than or equal to `other`.
      @inline(always)
      public fun infix>= (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)ge_\(builtinType)(self.value, other.value))
      }

      // MARK: AdditiveArithmetic conformance

      /// Returns `self` added to `other`.
      @inline(always)
      public fun infix+ (other: Self) -> Self {
        let (result, overflow) = \
    Builtin.\(signedness.abbreviated)add_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          Builtin.trap()
        } else {
          return .new(value: result)
        }
      }

      /// Increments `self` by `other`.
      @inline(always)
      public fun infix+= (other: Self) inout {
        let t = self + other  // Avoid requiring `Movable`.
        &self = t.copy()
      }

      /// Returns `other` subtracted from `self`.
      @inline(always)
      public fun infix- (other: Self) -> Self {
        let (result, overflow) = \
    Builtin.\(signedness.abbreviated)sub_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          Builtin.trap()
        } else {
          return .new(value: result)
        }
      }

      /// Decrements `self` by `other`.
      @inline(always)
      public fun infix-= (other: Self) inout {
        let t = self - other  // Avoid requiring `Movable`.
        &self = t.copy()
      }

      /// Returns `0`.
      @inline(always)
      public static fun zero() -> Self {
        .new()
      }

      // MARK: Numeric conformance

      /// Returns `self` multiplied by `other`.
      @inline(always)
      public fun infix* (other: Self) -> Self {
        let (result, overflow) = \
    Builtin.\(signedness.abbreviated)mul_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          Builtin.trap()
        } else {
          return .new(value: result)
        }
      }

      /// Multiplies `self` by `other`.
      @inline(always)
      public fun infix*= (other: Self) inout {
        let t = self * other  // Avoid requiring `Movable`.
        &self = t.copy()
      }

      /// Returns `self` divided by `other`, rounded towards zero.
      ///
      /// - Requires: `other` is not `0`, and the result is representable without overflow.
      @inline(always)
      public fun infix/ (other: Self) -> Self {
        if \(divisionIllegal("self", "other", type: "Self")) {
          Builtin.trap()
        } else {
          return .new(value: \
    Builtin.\(signedness.abbreviated)div_\(builtinType)(self.value, other.value))
        }
      }\(copyDefinition ?? "")

    }\(conformances)

    """
  }

  /// Returns an expression that's `true` iff `x` would be illegal to divide by `d` in type `t`.
  func divisionIllegal(_ x: String, _ d: String, type t: String) -> String {
    switch signedness {
    case .signed:
      "\(d) == (0 as \(t)) || (\(x) == (\(minimumValue) as \(t)) && \(d) == (-1 as \(t)))"
    case .unsigned:
      "\(d) == (0 as \(t))"
    }
  }

  /// The conformance declarations related to `self`.
  private var conformances: String {
    let minimal =
      """


      public given \(declarationName) is ExpressibleByIntegerLiteral { /* built-in */ }

      public given \(declarationName) is Movable {}
      """

    return switch includedConformances {
    case .all:
      """
      \(minimal)

      public given \(declarationName) is Copyable {}

      public given \(declarationName) is Equatable {}

      public given \(declarationName) is Comparable {}

      public given \(declarationName) is AdditiveArithmetic {}

      public given \(declarationName) is Numeric {}
      """
    case .minimal:
      minimal
    }

  }

  /// The definition of the `copy() -> Self` method, unless synthesized.
  var copyDefinition: String? {
    switch includedConformances {
    case .all:
      nil
    default:
      """


        /// MARK: Copyable conformance (only needed for dummies, synthesized otherwise)

        /// Returns a copy of `self`.
        @inline(always)
        public fun copy() -> Self {
          self + .zero()
        }
      """
    }
  }

}
