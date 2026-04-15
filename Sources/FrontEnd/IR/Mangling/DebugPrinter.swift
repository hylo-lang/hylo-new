/// A utility for printing debug information with indentation to reflect the structure of the data
/// being printed.
struct DebugPrinter {

  /// Whether to print debug information at all.
  public let enabled: Bool

  /// The current indentation level.
  private var indentation: Int = 0

  /// An instance with the given properties.
  init(enabled: Bool) {
    self.enabled = enabled
  }

  /// Returns the application of `action`, logging the scope described by `description` and the
  /// result if debug printing is enabled.
  mutating func withScope<T>(_ description: @autoclosure () -> String, _ action: () -> T) -> T {
    if enabled {
      let d = description()
      print("- enter \(d)")
      indentation += 1
      let r = action()
      indentation -= 1
      print("- leave \(d): \(r)")
      return r
    } else {
      return action()
    }
  }

  /// Executes `action`, logging the scope described by `description` if debug printing is enabled.
  mutating func withScope(_ description: @autoclosure () -> String, _ action: () -> Void) {
    if enabled {
      let d = description()
      print("- enter \(d)")
      indentation += 1
      action()
      indentation -= 1
      print("- leave \(d)")
    } else {
      action()
    }
  }

  /// Prints `x` to the standard output, prefixed by indentation reflecting the current nesting
  /// level. Does nothing if `enabled` is `false`.
  func print<T>(_ x: @autoclosure () -> T) {
    if enabled {
      printIndentation()
      Swift.print(x())
    }
  }

  /// Prints the indentation corresponding to the current nesting level.
  private func printIndentation() {
    for _ in 0..<indentation {
      Swift.print("  ", terminator: "")
    }
  }

}
