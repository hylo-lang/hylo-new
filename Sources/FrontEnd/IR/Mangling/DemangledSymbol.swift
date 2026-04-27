/// The demangled description of an entity.
indirect enum DemangledSymbol: Hashable, Sendable {

  /// Creates an instance decoding the symbol mangled in `s`.
  ///
  /// `self` is assigned to an error if `s` is malformed.
  init(_ s: String) {
    if let x = String(assemblySanitized: s) {
      var source = DemanglingContext(stream: x[...])
      self = ManglingEncoding.demangle(from: &source)
    } else {
      self = .error(nil, remaining: s)
    }
  }

  /// The declaration of an entity.
  case entity(DemangledEntity)

  /// A type.
  case type(DemangledType)

  /// A witness table.
  case witnessTable(DemangledType)

  /// An error encountered during demangling.
  ///
  /// The payload captures what we could demangle until we encountered the error, if any, and the characters
  /// still remaining to be parsed.
  case error(DemangledSymbol?, remaining: String)

  /// An instance decoding a reserved symbol identifier.
  init(reserved: ReservedSymbol) {
    switch reserved {
    case .hylo:
      self = .entity(.hylo)
    case .bool:
      self = .entity(.init(coreType: "Bool"))
    case .int:
      self = .entity(.init(coreType: "Int"))
    case .int64:
      self = .entity(.init(coreType: "Int64"))
    case .never:
      self = .type(.never)
    case .void:
      self = .type(.void)
    }
  }

  /// A textual description of the kind of symbol represented by `self`, without any details.
  var tag: String {
    switch self {
    case .entity:
      return "entity"
    case .type:
      return "type"
    case .witnessTable:
      return "witness table"
    case .error:
      return "error"
    }
  }

}

extension DemangledSymbol: CustomStringConvertible {

  public var description: String {
    switch self {
    case .entity(let e):
      return e.description
    case .type(let t):
      return t.description
    case .witnessTable(let t):
      return "witness table \(t)"
    case .error(let e, let r):
      if let e = e {
        return "\(e) ??? (remaining: \(r))"
      } else {
        return "??? (remaining: \(r))"
      }
    }
  }

}

/// The payload of a `DemangledSymbol.entity`.
indirect enum DemangledEntity: Hashable, Sendable {

  /// A reference to the innermost enclosing entity.
  case relative

  /// A module.
  case module(String)

  /// A translation unit.
  case sourceFile(String)

  /// A virtual translation unit.
  case virtualTranslationUnit(Int)

  /// A scope.
  case scope(String)

  /// An anonymous scope.
  case anonymousScope(UInt64)

  /// A binding declaration.
  case binding(names: [Name])

  /// A conformance declaration.
  case conformanceDeclaration(type: DemangledType, usings: [DemangledEntity])

  /// An extension declaration.
  case extensionDeclaration(type: DemangledType, usings: [DemangledEntity])

  /// A function declaration.
  case functionDeclaration(name: Name, type: DemangledType, isStatic: Bool)

  /// A function bundle declaration.
  case functionBundleDeclaration(name: Name, type: DemangledType)

  /// An initializer.
  case initializer(DemangledEntity)

  /// A synthesized function.
  case synthesizedFunction(DemangledEntity, [DemangledType.TypeApplicationArgument])

  /// An implementation IR function.
  case implementation(DemangledEntity, DemangledEntity, [DemangledType.TypeApplicationArgument])

  /// An existentialized declaration.
  case existentialized(DemangledEntity)

  /// A variant.
  case variant(AccessEffect)

  /// A qualified entity with `head` as the innermost component and `previous` as the qualification.
  case qualified(head: DemangledEntity, previous: DemangledEntity)

  /// An error encountered during demangling of an entity.
  case error

  /// An instance representing a core type declaration.
  init(coreType: String) {
    self = .qualified(head: .scope(coreType), previous: .hylo)
  }

  /// The `Hylo` module.
  fileprivate static var hylo: DemangledEntity {
    .module("Hylo")
  }

}

extension DemangledEntity: CustomStringConvertible {

  public var description: String {
    switch self {
    case .relative:
      return ".."
    case .module(let name):
      return name
    case .translationUnit(let name):
      return name
    case .virtualTranslationUnit:
      // Don't report the ID; useful for testing with exact match.
      return "#"
    case .scope(let name):
      return name
    case .anonymousScope:
      return "$anonymous"
    case .binding(let names):
      return names.description
    case .conformanceDeclaration(let type, let usings):
      let u = usings.map { "\($0)" }.joined(separator: ", ")
      return "given \(type) where \(u)"
    case .extensionDeclaration(let type, let usings):
      let u = usings.map { "\($0)" }.joined(separator: ", ")
      return "extension \(type) where \(u)"
    case .functionDeclaration(let name, let type, let isStatic):
      return "\(isStatic ? "static " : "")fun \(name): \(type)"
    case .functionBundleDeclaration(let name, let type):
      return "fun bundle \(name): \(type)"
    case .initializer(let e):
      return "init \(e)"
    case .synthesizedFunction(let e, let arguments):
      let args = arguments.map { "[\($0.formal): \($0.argument)]" }.joined(separator: ", ")
      return "\(e)<\(args)>"
    case .implementation(let e, let c, let a):
      let args = a.map { "[\($0.formal): \($0.argument)]" }.joined(separator: ", ")
      return "\(e) implements \(c)<\(args)>"
    case .existentialized(let e):
      return "some \(e)"
    case .variant(let e):
      return "\(e)"
    case .qualified(let head, let previous):
      return "\(previous).\(head)"
    case .error:
      return "?"
    }
  }

}

/// The payload of a `DemangledSymbol.type`.
indirect enum DemangledType: Hashable, Sendable {

  /// An error encountered during demangling of a type.
  case error

  /// The `Never` type.
  case never

  /// The `Void` type.
  case void

  /// An arrow type.
  case arrow(
    style: Call.Style,
    effect: AccessEffect,
    environment: DemangledType,
    inputs: [Parameter],
    output: DemangledType)

  /// An associated type.
  case associatedType(declaration: DemangledEntity, type: DemangledType)

  /// An enum type.
  case enumType(DemangledEntity)

  /// A bundle type.
  case bundle(shape: DemangledType, variants: AccessEffectSet)

  /// An equality witness type.
  case equalityWitness(DemangledType, DemangledType)

  /// A function pointer type.
  case functionPointer(inputs: [DemangledType], output: DemangledType)

  /// A generic parameter type representing the conformer of a trait.
  case genericParameterConformer(declaration: DemangledEntity, kind: Kind)

  /// A generic parameter declared in sources.
  case genericParameterUser(declaration: DemangledEntity, kind: Kind)

  /// The `n`-th parameter of a built-in type.
  case genericParameterNth(index: Int, kind: Kind)

  /// An implication type.
  case implication(usings: [DemangledType], head: DemangledType)

  /// An integer literal type.
  case integerLiteral

  /// A float literal type.
  case floatLiteral

  /// A machine type.
  case machine(MachineType)

  /// A metakind type.
  case metakind(Kind)

  /// A metatype.
  case metatype(DemangledType)

  /// An opaque environment type.
  case opaqueEnvironment(DemangledEntity)

  /// A remote type.
  case remote(DemangledType, AccessEffect)

  /// A struct type.
  case structType(DemangledEntity)

  /// A trait type.
  case traitType(DemangledEntity)

  /// A tuple type with at least one element.
  case tupleConsType(DemangledType, DemangledType)

  /// An empty tuple type.
  case tupleEmptyType

  /// A type alias type.
  case typeAlias(declaration: DemangledEntity, aliasee: DemangledType)

  /// A type application.
  case typeApplication(abstraction: DemangledType, arguments: [TypeApplicationArgument])

  /// An universal type.
  case universalType(parameters: [DemangledType], head: DemangledType)

  /// A type application argument.
  struct TypeApplicationArgument: Hashable, Sendable {

    /// The formal parameter.
    let formal: DemangledType

    /// The value of the type.
    let argument: DemangledType

  }

  /// A parameter of a callable symbol.
  struct Parameter: Hashable, Sendable {

    /// The parameter label, if any.
    let label: String?

    /// The type of the parameter.
    let type: DemangledType

  }

}

extension DemangledType: CustomStringConvertible {

  public var description: String {
    switch self {
    case .error:
      return "?"

    case .never:
      return "Never"

    case .void:
      return "Void"

    case .arrow(_, let effect, let environment, let inputs, let output):
      return "[\(environment)](\(list: inputs)) \(effect) -> \(output)"

    case .associatedType(let domain, let name):
      return "\(domain).\(name)"

    case .enumType(let e):
      return e.description

    case .bundle(let shape, let variants):
      return "bundle<\(shape), \(variants)>"

    case .equalityWitness(let lhs, let rhs):
      return "\(lhs) == \(rhs)"

    case .functionPointer(let inputs, let output):
      let i = inputs.map { (t) -> String in
        "\(t)"
      }
      return "ptr (\(list: i)) -> \(output)"

    case .genericParameterConformer(let declaration, let kind):
      return "GenericParameterConformer<\(declaration), \(kind)>"

    case .genericParameterUser(let declaration, let kind):
      return "GenericParameterUser<\(declaration), \(kind)>"

    case .genericParameterNth(let index, let kind):
      return "GenericParameterNth<\(index), \(kind)>"

    case .implication(let usings, let head):
      let u = usings.map { "\($0)" }
      return "(\(list: u)) => \(head)"

    case .integerLiteral:
      return "IntegerLiteral"

    case .floatLiteral:
      return "FloatLiteral"

    case .machine(let t):
      return t.description

    case .metakind(let k):
      return "Metakind<\(k)>"

    case .metatype(let t):
      return "Metatype<\(t)>"

    case .opaqueEnvironment(let d):
      return "some \(d)"

    case .remote(let t, let a):
      return "\(a) \(t)"

    case .structType(let e):
      return e.description

    case .traitType(let e):
      return e.description

    case .tupleConsType, .tupleEmptyType:
      let l = tupleAsList.map { "\($0)" }.joined(separator: ", ")
      return "(\(l))"

    case .typeAlias(let declaration, let aliasee):
      return "typealias \(declaration) = \(aliasee)"

    case .typeApplication(let abstraction, let arguments):
      let args = arguments.map({ (a) in "[\(a.formal): \(a.argument)]" }).joined(separator: ", ")
      return "\(abstraction)<\(args)>"
    case .universalType(let parameters, let head):
      let params = parameters.map { "\($0)" }.joined(separator: ", ")
      return "<\(params)> \(head)"
    }
  }

  /// If `self` is a tuple type, returns its components. Otherwise, returns `[self]`.
  private func tupleAsList() -> [DemangledType] {
    switch self {
    case .tupleConsType(let head, let tail):
      return [head] + tail.tupleAsList
    case .tupleEmptyType:
      return []
    default:
      return [self]
    }
  }

}

extension DemangledType.Parameter: CustomStringConvertible {

  public var description: String {
    if let label = label {
      return "\(label): \(type)"
    } else {
      return "\(type)"
    }
  }

}
