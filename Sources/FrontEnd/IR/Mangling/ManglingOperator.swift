import Utilities

/// Short identifier specifying how to interpret the next fragment of mangled data.
public enum ManglingOperator: String, CaseIterable, Sendable {

  // Convention: operator strings are matching regex "[a-z]*[A-Z]"

  /// Starts a lookup of a previously mangled symbol.
  case lookup = "K"

  /// Starts a lookup of a previously mangled type.
  case lookupType = "L"

  /// Starts a lookup to the current qualification.
  case lookupRelative = "rK"

  /// Starts a reserved symbol identifier.
  case reserved = "R"

  /// Starts a reserved type identifier.
  case reservedType = "tR"

  /// Starts an associated type declaration symbol.
  case associatedTypeDeclaration = "taD"

  /// Starts an enum case declaration symbol.
  case enumCaseDeclaration = "ecD"

  /// Starts an enum declaration symbol.
  case enumDeclaration = "eD"

  /// Starts a binding declaration symbol.
  case bindingDeclaration = "bD"

  /// Starts a conformance declaration symbol.
  case conformanceDeclaration = "cD"

  /// Starts an extension declaration symbol.
  case extensionDeclaration = "xD"

  /// Starts an import declaration symbol.
  case importDeclaration = "iD"

  /// Starts a function declaration symbol.
  case functionDeclaration = "F"

  /// Starts a static function declaration symbol.
  case staticFunctionDeclaration = "sF"

  /// Starts a function bundle declaration symbol.
  case functionBundleDeclaration = "bF"

  /// Starts an initializer declaration symbol.
  case initializerDeclaration = "iF"

  /// Starts a synthesized function declaration symbol.
  case synthesizedFunctionDeclaration = "xF"

  /// Starts a function implementation declaration symbol.
  case implementationDeclaration = "mF"

  /// Starts an existentialized function declaration symbol.
  case existentializedDeclaration = "eF"

  /// Starts a generic parameter declaration symbol.
  case genericParameterDeclaration = "G"

  /// Starts a parameter declaration symbol.
  case parameterDeclaration = "P"

  /// Starts a struct declaration symbol.
  case structDeclaration = "S"

  /// Starts a typealias declaration symbol.
  case typealiasDeclaration = "A"

  /// Starts a trait declaration symbol.
  case traitDeclaration = "C"

  /// Starts a variable declaration symbol.
  case variableDeclaration = "V"

  /// Starts a variant declaration symbol.
  case variantDeclaration = "vD"

  /// Starts an arrow type.
  case arrowType = "lT"

  /// Starts an associated type.
  case associatedType = "aaT"

  /// Starts a bundle type.
  case bundleType = "bT"

  /// Starts an enum type.
  case enumType = "eT"

  /// Starts an equality witness type.
  case equalityWitnessType = "ewT"

  /// Starts a function pointer type.
  case functionPointerType = "fT"

  /// Starts an implication type.
  case implicationType = "iT"

  /// Starts a literal integer type.
  case literalIntegerType = "liT"

  /// Starts a literal float type.
  case literalFloatType = "lfT"

  /// Starts a machine integer type of a specific width.
  case machineIntegerType = "miT"

  /// Starts a machine float type of a specific width.
  case machineFloatType = "mfT"

  /// Starts a machine pointer type.
  case machinePointerType = "mpT"

  /// Starts a machine word type.
  case machineWordType = "mwT"

  /// Starts a generic parameter conformer type.
  case genericParameterConformerType = "gcT"

  /// Starts a generic parameter user type.
  case genericParameterUserType = "guT"

  /// Starts a generic parameter nth type.
  case genericParameterNthType = "gnT"

  /// Starts a metakind type.
  case metakindType = "mkT"

  /// Starts a metatype type.
  case metatypeType = "mT"

  /// Starts a module type.
  case opaqueEnvironmentType = "oeT"

  /// Starts a remote type.
  case remoteType = "rT"

  /// Starts a struct type.
  case structType = "sT"

  /// Starts a trait type.
  case traitType = "cT"

  /// Starts a tuple cons type.
  case tupleConsType = "tT"

  /// Starts a tuple empty type.
  case tupleEmptyType = "teT"

  /// Starts a type alias type.
  case typeAliasType = "aT"

  /// Starts a type application type.
  case typeApplicationType = "pT"

  /// Starts a universal type.
  case universalType = "uT"

  /// Starts an anonymous scope.
  case anonymousScope = "Y"

  /// Starts a module name.
  case module = "M"

  /// Starts a translation unit.
  case translationUnit = "U"

  /// Starts a virtual translation unit.
  case virtualTranslationUnit = "vU"

  /// Starts a witness table symbol.
  case witnessTable = "wW"

  /// An instance containing the operator that prefixes `s`, if any.
  init?(prefixing s: Substring) {
    if s.isEmpty { return nil }

    var i = s.startIndex
    while s[i].isASCII && s[i].isLowercase {
      i = s.index(after: i)
      if i == s.endIndex { return nil }
    }

    if let o = ManglingOperator(rawValue: String(s[...i])) {
      self = o
    } else {
      return nil
    }
  }

  /// `true` iff `self` starts an entity declaration.
  var isEntityOperator: Bool {
    switch self {
    case .lookup, .lookupRelative, .reserved, .associatedTypeDeclaration, .enumCaseDeclaration,
      .enumDeclaration, .bindingDeclaration, .conformanceDeclaration, .extensionDeclaration,
      .importDeclaration, .functionDeclaration, .staticFunctionDeclaration,
      .functionBundleDeclaration, .initializerDeclaration,
      .synthesizedFunctionDeclaration, .implementationDeclaration, .existentializedDeclaration,
      .genericParameterDeclaration, .parameterDeclaration,
      .structDeclaration, .typealiasDeclaration, .traitDeclaration, .variableDeclaration,
      .variantDeclaration, .anonymousScope, .module, .translationUnit, .virtualTranslationUnit:
      return true
    default:
      return false
    }
  }

  /// `true` iff `self` is an operator that starts a type.
  var isTypeOperator: Bool {
    switch self {
    case .lookupType, .reservedType, .arrowType, .associatedType, .bundleType, .enumType,
      .equalityWitnessType,
      .functionPointerType, .implicationType, .literalIntegerType, .literalFloatType,
      .machineIntegerType, .machineFloatType, .machinePointerType, .machineWordType,
      .genericParameterConformerType, .genericParameterUserType, .genericParameterNthType,
      .metakindType, .metatypeType, .opaqueEnvironmentType, .remoteType, .structType, .traitType,
      .tupleConsType, .tupleEmptyType, .typeAliasType, .typeApplicationType, .universalType:
      return true
    default:
      return false
    }
  }

}

extension ManglingOperator: TextOutputStreamable {

  public func write<T: TextOutputStream>(to output: inout T) {
    output.write(rawValue)
  }

}
