/// Marks this execution path as unreachable, causing a fatal error otherwise.
public func unreachable(
  _ message: @autoclosure () -> String = "",
  file: StaticString = #file,
  line: UInt = #line
) -> Never {
  fatalError(message(), file: file, line: line)
}

/// Reports that a feature is not yet implemented at halts the program's execution.
public func unimplemented(
  _ feature: @autoclosure () -> String? = nil,
  file: StaticString = #file,
  line: UInt = #line
) -> Never {
  fatalError(
    "unimplemented feature" + (feature().map({ (s) in ": \(s)" }) ?? ""),
    file: file, line: line)
}
