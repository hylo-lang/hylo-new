import Archivist

/// A modifier on a declaration.
@Archivable
public enum DeclarationModifier: UInt8, Sendable {

  /// Introduces a member stored out-of-line.
  case indirect

  /// Introduces a static member.
  case `static`

  /// Introduces an entity visible up to the module boundary.
  case `module`

  /// Introduces an entity visible beyond the module boundary.
  case `public`

  /// Returns `true` iff `self` can appear after `other` in sources.
  public func canOccurAfter(_ other: DeclarationModifier) -> Bool {
    switch self {
    case .indirect, .static:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `self` and `other` can be applied on the same declaration.
  public func canOccurWith(_ other: DeclarationModifier) -> Bool {
    switch self {
    case .indirect:
      return (other != self) && (other != .static)
    case .static:
      return (other != self) && (other != .indirect)
    default:
      assert(isAccessModifier)
      return !other.isAccessModifier
    }
  }

  /// Returns `true` iff `self` is an access modifier.
  public var isAccessModifier: Bool {
    switch self {
    case .module, .public:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `self` can be applied to a conformance declaration.
  public var isApplicableToConformance: Bool {
    isAccessModifier
  }

  /// Returns `true` iff `self` can be applied to an import declaration.
  public var isApplicableToImport: Bool {
    isAccessModifier
  }

  /// Returns `true` iff `self` can be applied on an initializer declaration.
  public var isApplicableToInitializer: Bool {
    isAccessModifier
  }

  /// Returns `true` iff `self` can be applied on a type declaration.
  public var isApplicableToTypeDeclaration: Bool {
    isAccessModifier
  }

}
