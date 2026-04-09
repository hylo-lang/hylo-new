import Foundation

/// Generates `Integers.hylo` inside `outputDirectory`, creating the directory if needed.
func generateIntegerTypes() throws -> String {
  var types: [IntegerTypeDefinition] = []

  for bits in [8, 16, 32, 64] {
    types.append(.fixedSize(bits: bits, .signed))
    types.append(.fixedSize(bits: bits, .unsigned))
  }

  types.append(
    .init(
      name: "Int",
      documentation:
        "/// A signed integer type that can represent any object size on the target platform.",
      builtinType: "word", .signed, .fittingLargestObjectSize))

  types.append(
    .init(
      name: "UInt",
      documentation:
        "/// An unsigned integer type that can represent any object size on the target platform.",
      builtinType: "word", .unsigned, .fittingLargestObjectSize))

  return types.map(\.description).joined(separator: "\n")
}

extension IntegerTypeDefinition {

  /// Creates a fixed-size integer type's definition.
  static func fixedSize(bits: Int, _ signedness: SignednessPrefix) -> IntegerTypeDefinition {
    .init(
      name: signedness == .signed ? "Int\(bits)" : "UInt\(bits)",
      documentation: "/// \(signedness.prefixedDescription) \(bits)-bit integer.",
      builtinType: "i\(bits)", signedness, .fixedWidth(bits: bits))
  }

}

/// Whether an integer type is signed or unsigned.
enum SignednessPrefix: String, CustomStringConvertible {

  case signed = "s"
  case unsigned = "u"

  var description: String {
    switch self {
    case .signed: "signed"
    case .unsigned: "unsigned"
    }
  }

  /// The description of the signedness prefixed with an indefinite article.
  var prefixedDescription: String {
    switch self {
    case .signed: "A signed"
    case .unsigned: "An unsigned"
    }
  }

  /// The abbreviation used in builtin type names.
  var abbreviated: String { rawValue }

}

/// The size of an integer type.
enum Size {

  /// The type is capable of representing the size of the largest object in memory on the target platform.
  case fittingLargestObjectSize

  /// The type has exactly `bits` bits.
  case fixedWidth(bits: Int)

}

/// Information for emitting a standard library integer type.
struct IntegerTypeDefinition: CustomStringConvertible {

  let declarationName: String
  let declarationDocumentation: String
  let builtinType: String
  let signedness: SignednessPrefix
  let size: Size

  /// Constructs an instance from its basic parts.
  init(
    name: String, documentation: String, builtinType: String, _ signedness: SignednessPrefix,
    _ size: Size
  ) {
    self.declarationName = name
    self.declarationDocumentation = documentation
    self.builtinType = builtinType
    self.signedness = signedness
    self.size = size
  }

  /// The code introducing the `abs()` method for signed types, nil otherwise.
  var absMethod: String? {
    signedness == .unsigned
      ? nil
      : """

        /// Returns the absolute value of `self`.
        ///
        /// - Precondition: `self` must not be the \(declarationName)'s minimum value.
        public fun abs() -> Self {
          if self < Self.zero() { Self.zero() - self } else { Self(value: self.value) }
        }
      """
  }

  /// The source code representation of this type.
  var description: String {
    """
    \(declarationDocumentation)
    @_symbol(\"\(declarationName)\")
    public struct \(declarationName) is Deinitializable {

      /// The raw value of this instance.
      internal var value: Builtin.\(builtinType)

      /// Cre ates an instance with its raw value.
      internal memberwise init

      /// Creates an instance equal to `false`.
      public init() {
        &self.value = Builtin.zeroinitializer_\(builtinType)()
      }
    \(absMethod ?? "")

    }

    public given \(declarationName) is ExpressibleByIntegerLiteral { /* built-in */ }

    public given \(declarationName) is Movable {}

    public given \(declarationName) is Equatable {

      /// Returns `true` if `self` is equal to `other`.
      public fun infix== (other: Self) -> Bool {
        .new(value: Builtin.icmp_eq_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` if `self` is not equal to `other`.
      public fun infix!= (other: Self) -> Bool {
        .new(value: Builtin.icmp_ne_\(builtinType)(self.value, other.value))
      }

    }

    public given \(declarationName) is Comparable {

      /// Returns `true` if `self` is less than `other`.
      public fun infix< (other: Self) -> Bool {
        .new(value: Builtin.icmp_\(signedness.abbreviated)lt_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` if `self` is less than or equal to `other`.
      public fun infix<= (other: Self) -> Bool {
        .new(value: Builtin.icmp_\(signedness.abbreviated)le_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` if `self` is greater than `other`.
      public fun infix> (other: Self) -> Bool {
        .new(value: Builtin.icmp_\(signedness.abbreviated)gt_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` if `self` is greater than or equal to `other`.
      public fun infix>= (_ other: Self) -> Bool {
        .new(value: Builtin.icmp_\(signedness.abbreviated)ge_\(builtinType)(self.value, other.value))
      }

    }

    public given \(declarationName) is AdditiveArithmetic {

      /// Returns `self` added to `other`.
      fun infix+ (other: Self) -> Self {
        let (result, overflow) = Builtin.\(signedness.abbreviated)add_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          fatal_error()
        } else {
          return .new(value: result)
        }
      }

      /// Returns `other` subtracted from `self`.
      fun infix- (other: Self) -> Self {
        let (result, overflow) = Builtin.\(signedness.abbreviated)sub_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          fatal_error()
        } else {
          return .new(value: result)
        }
      }

      /// Returns `0`.
      static fun zero() -> Self {
        .new()
      }

    }

    public given \(declarationName) is Numeric {

      /// Returns `self` multiplied by `other`.
      fun infix* (other: Self) -> Self {
        let (result, overflow) = Builtin.\(signedness.abbreviated)mul_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          fatal_error()
        } else {
          return .new(value: result)
        }
      }

    }


    """
  }

}
