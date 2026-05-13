import SwiftyLLVM
import ArgumentParser

extension CodeModel: @retroactive ExpressibleByArgument {

  /// Parses a string argument into an enum case, excluding JIT support.
  public init?(argument: String) {
    guard argument != "jit",
          let c = Self.allCases.first(where: { String(describing: $0) == argument }) else {
      return nil
    }
    self = c
  }

  /// All possible values for this flag, excluding JIT support.
  public static var allValueStrings: [String] {
    allCases.filter { $0 != .jit }.map { String(describing: $0) }
  }

}
