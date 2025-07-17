import Archivist

/// An entity built in the compiler.
@Archivable
public enum BuiltinEntity: Hashable, Sendable {

  /// A built-in type alias.
  case alias

  /// The product constructor, aka the infix type operator `*`.
  case product

  /// The product constructor, aka the infix type operator `+`.
  case sum

  /// The witness of a coercion.
  case coercion

  /// A built-in entity.
  case function(BuiltinFunction)

}
