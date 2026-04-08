import Archivist

/// An entity built in the compiler.
@Archivable
public enum BuiltinEntity: Hashable, Sendable {

  /// A built-in type alias.
  case alias

  /// The witness of a coercion.
  case coercion

  /// A built-in entity.
  case function(BuiltinFunction)

}
