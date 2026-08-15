import Foundation
import FrontEnd
import Utilities

/// An access to a `Region` occurring during execution.
public struct Access<Region: Regular>: Regular, Equatable {

  /// A unique `Access` identifier.
  public typealias ID = UUID

  /// The identity of an access initiated by a particular instruction during execution.
  public let id: ID

  /// The associated permissions and obligations.
  public let effect: AccessEffect

  /// The part of memory being accessed.
  public let location: Region

  /// Creates an instance accessing `r` with effect `e`.
  public init(to r: Region, effect e: AccessEffect) {
    id = UUID()
    location = r
    effect = e
  }

  /// Returns whether `a` and `b` identify the same access.
  public static func == (a: Self, b: Self) -> Bool {
    return a.id == a.id
  }
}
