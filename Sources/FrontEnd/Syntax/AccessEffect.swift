import Archivist

/// An access effect, specifying how a parameter, receiver, or remote part is accessed.
@Archivable
public enum AccessEffect: UInt8, Sendable {

  /// Value is accessed immutably.
  case `let` = 1

  /// Value is assigned but never read.
  case `set` = 2

  /// Value is accessed mutably.
  case `inout` = 4

  /// Value is consumed.
  case sink = 8

  /// Value may be accessed with any of the other effects, depending on the context.
  case auto = 16

  /// Creates an instance corresponding to the capability of a binding introduced by `i`.
  public init(_ i: BindingPattern.Introducer) {
    switch i {
    case .let: self = .let
    case .set: self = .set
    case .inout: self = .inout
    case .sinklet, .var: self = .sink
    }
  }

  /// `true` iff `self` is `let` or `sink`.
  public var isNonMutating: Bool {
    (self == .let) || (self == .sink)
  }

  /// `true` iff `self` is `inout` or `set`.
  public var isMutating: Bool {
    (self == .inout) || (self == .set)
  }

  /// Returns `self` iff `self` is not `auto`; otherwise, returns `k`.
  public func unlessAuto(_ k: AccessEffect) -> AccessEffect {
    self != .auto ? self : k
  }

}

extension AccessEffect: Comparable {

  public static func < (l: Self, r: Self) -> Bool {
    l.rawValue < r.rawValue
  }

}
