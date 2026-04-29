/// A utility for printing debug information with indentation to reflect the structure of the data
/// being printed.
internal struct DebugPrinter {

  /// Whether to print debug information at all.
  internal let enabled: Bool
  /// The current indentation level.
  private var indentation: Int = 0

  /// An instance with the given properties.
  internal init(enabled: Bool) {
    self.enabled = enabled
  }

  /// Increases the indentation level by one iff `enabled` is `true`.
  mutating func indent() {
    if enabled {
      indentation += 1
    }
  }

  /// Decreases the indentation level by one iff `enabled` is `true`.
  mutating func dedent() {
    if enabled {
      indentation -= 1
    }
  }

  /// Returns the application of `action`, logging the scope described by `description` and the
  /// resulting value if debug printing is enabled.
  internal func withScope<T>(
    _ description: @autoclosure () -> String, _ action: () -> T
  ) -> T {
    if enabled {
      let d = description()
      printWithIndentation("- enter \(d)")
      let r = action()
      printWithIndentation("- leave \(d): \(r)")
      return r
    } else {
      return action()
    }
  }

  /// Executes `action`, logging the scope described by `description` if debug printing is enabled.
  internal func withScope(
    _ description: @autoclosure () -> String, _ action: () -> Void
  ) {
    if enabled {
      let d = description()
      printWithIndentation("- enter \(d)")
      action()
      printWithIndentation("- leave \(d)")
    } else {
      action()
    }
  }

  /// Prints `x` to the standard output, prefixed by indentation reflecting the current nesting
  /// level iff `enabled` is `true`. Does nothing otherwise.
  internal func printWithIndentation<T>(_ x: @autoclosure () -> T) {
    if enabled {
      printIndentation()
      print(x())
    }
  }

  /// Prints the indentation corresponding to the current nesting level.
  private func printIndentation() {
    for _ in 0..<indentation {
      print("  ", terminator: "")
    }
  }

}
