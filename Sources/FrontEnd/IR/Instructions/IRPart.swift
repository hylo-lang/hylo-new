import Archivist
import Utilities

/// An instruction projecting the part of a whole.
public protocol IRPart: Instruction {

  /// The place of the whole containing the part being accessed.
  var whole: IRValue { get }

  /// A witness of the run-time type of the whole iff that type has been existentialized.
  var wholeWitness: IRValue? { get }

  /// The type of the subfield being accessed.
  var partType: AnyTypeIdentity { get }

  /// Returns a copy of `self` reading member offsets from the given witness.
  func existentialized(readingOffsetsWith wholeWitness: IRValue) -> Self

}
