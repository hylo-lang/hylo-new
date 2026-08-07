import Archivist

/// An entity built in the compiler.
@Archivable
public enum BuiltinEntity: Hashable, Sendable {

  /// The `Self` alias.
  case selfAlias

  /// The `Metatype` alias.
  case metatypeAlias

  /// The `Never` alias.
  case neverAlias

  /// The `Void` alias.
  case voidAlias

  /// The built-in module.
  case module

  /// The witness of a coercion.
  case coercion

  /// A built-in type.
  case type

  /// A built-in entity.
  case function(BuiltinFunction)

}
