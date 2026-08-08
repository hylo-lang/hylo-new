import Archivist

/// An entity built in the compiler.
///
/// Such entities may be referred to from source (e.g. `Builtin.add_i8(_:_:)`) but don't have a
/// corresponding declaration.
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

  /// A built-in function.
  case function(BuiltinFunction)

}
