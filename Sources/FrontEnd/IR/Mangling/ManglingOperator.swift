import Utilities

/// Short identifier specifying how to interpret the next fragment of mangled data.
public enum ManglingOperator: String, CaseIterable, Sendable {

  // Convention: operator strings are matching regex "[a-z]*[A-Z]"

  /// Starts a lookup of a previously mangled symbol.
  case lookup = "K"

  /// Starts a lookup of a previously mangled type.
  case lookupType = "L"

  /// Indicates a lookup to the current qualification.
  case lookupRelative = "rK"

  /// Starts a reserved symbol identifier.
  case reserved = "R"

  /// Starts a reserved symbol identifier.
  case reservedType = "tR"

  /// Indicates an associated type declaration symbol.
  case associatedTypeDeclaration = "taD"

  /// Indicates an enum case declaration symbol.
  case enumCaseDeclaration = "ecD"

  /// Indicates an enum declaration symbol.
  case enumDeclaration = "eD"

  /// Indicates a binding declaration symbol.
  case bindingDeclaration = "bD"

  /// Indicates a conformance declaration symbol.
  case conformanceDeclaration = "cD"

  /// Indicates an extension declaration symbol.
  case extensionDeclaration = "xD"

  /// Indicates an import declaration symbol.
  case importDeclaration = "iD"

  /// Indicates a function declaration symbol.
  case functionDeclaration = "F"

  /// Indicates a static function declaration symbol.
  case staticFunctionDeclaration = "sF"

  /// Indicates a function bundle declaration symbol.
  case functionBundleDeclaration = "bF"

  /// Indicates a synthesized function declaration symbol.
  case synthesizedFunctionDeclaration = "xF"

  /// Indicates a generic parameter declaration symbol.
  case genericParameterDeclaration = "G"

  /// Indicates a parameter declaration symbol.
  case parameterDeclaration = "P"

  /// Indicates a struct declaration symbol.
  case structDeclaration = "S"

  /// Indicates a typealias declaration symbol.
  case typealiasDeclaration = "A"

  /// Indicates a trait declaration symbol.
  case traitDeclaration = "C"

  /// Indicates a variable declaration symbol.
  case variableDeclaration = "V"

  /// Indicates a variant declaration symbol.
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

  /// Indicates a literal integer type.
  case literalIntegerType = "liT"

  /// Indicates a literal float type.
  case literalFloatType = "lfT"

  /// Starts a machine integer type of a specific width.
  case machineIntegerType = "miT"

  /// Starts a machine float type of a specific width.
  case machineFloatType = "mfT"

  /// Indicates a machine pointer type.
  case machinePointerType = "mpT"

  /// Indicates a machine word type.
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

  /// Indicates a tuple empty type.
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
      .functionBundleDeclaration,
      .synthesizedFunctionDeclaration, .genericParameterDeclaration, .parameterDeclaration,
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
