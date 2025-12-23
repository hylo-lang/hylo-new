import Archivist

/// A modifier on a declaration.
@Archivable
public enum DeclarationModifier: UInt8, Sendable {

  /// Introduces a member stored out-of-line.
  case indirect

  /// Introduces a static member.
  case `static`

  /// Introduces an entity only within its enclosing scope.
  case `private`

  /// Introduces an entity visible up to the module boundary.
  case `internal`

  /// Introduces an entity visible beyond the module boundary.
  case `public`

  /// Introduces an entity whose contents is visible across resilience boundaries.
  case inlineable

  /// Returns `true` iff `self` can appear after `other` in sources.
  public func canOccurAfter(_ other: DeclarationModifier) -> Bool {
    switch self {
    case .indirect, .static:
      return true
    case .inlineable:
      return false
    default:
      assert(isAccessModifier)
      return other == .inlineable
    }
  }

  /// Returns `true` iff `self` and `other` can be applied on the same declaration.
  public func canOccurWith(_ other: DeclarationModifier) -> Bool {
    switch self {
    case .indirect:
      return (other != self) && (other != .static)
    case .static:
      return (other != self) && (other != .indirect)
    case .inlineable:
      return true
    default:
      assert(isAccessModifier)
      return !other.isAccessModifier
    }
  }

  /// Returns `true` iff `self` is an access modifier.
  public var isAccessModifier: Bool {
    switch self {
    case .private, .internal, .public:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `self` can be applied to a conformance declaration.
  public var isApplicableToConformance: Bool {
    isAccessModifier
  }

  /// Returns `true` iff `self` can be applied on an initializer declaration.
  public var isApplicableToInitializer: Bool {
    isAccessModifier || self == .inlineable
  }

  /// Returns `true` iff `self` can be applied on a type declaration.
  public var isApplicableToTypeDeclaration: Bool {
    isAccessModifier || self == .inlineable
  }

}
