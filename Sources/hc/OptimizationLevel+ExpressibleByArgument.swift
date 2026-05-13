import SwiftyLLVM
import ArgumentParser

extension OptimizationLevel: @retroactive ExpressibleByArgument {

  /// Creates an instance from a command-line argument string.
  public init?(argument: String) {
    switch argument {
    case "0": self = .none
    case "1": self = .less
    case "2": self = .default
    case "3": self = .aggressive
    default: return nil
    }
  }

  /// All possible optimization levels (-O0, -O1, -O2, -O3).
  public static var allValueStrings: [String] { ["0", "1", "2", "3"] }

}