/// The identity of a symbol that can be mangled.
enum ManglingSymbol: Hashable {

  /// A declaration or a scope.
  case node(AnySyntaxIdentity)

  /// A file scope.
  case fileScope(ScopeIdentity)

  /// A module.
  case module(Module.ID)

  /// A canonical type.
  case type(AnyTypeIdentity)

}
