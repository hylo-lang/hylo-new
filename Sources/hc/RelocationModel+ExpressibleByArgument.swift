import SwiftyLLVM
import ArgumentParser

extension RelocationModel: @retroactive ExpressibleByArgument {

  /// All enum cases as strings are possible values for this flag.
  public static var allValueStrings: [String] {
    allCases.map { String(describing: $0) }
  }

  /// Parses a string argument into an enum case.
  public init?(argument: String) {
    guard let c = Self.allCases.first(where: { String(describing: $0) == argument }) else {
      return nil
    }
    self = c
  }

}