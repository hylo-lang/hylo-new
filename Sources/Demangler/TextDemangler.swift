import FrontEnd

/// Demangles Hylo symbols embedded in text.
public enum TextDemangler {

  /// A mangled symbol and its demangled representation.
  public typealias Symbol = (mangled: Substring, demangled: String)

  /// Returns `input` with each mangled Hylo symbol replaced by its demangled representation.
  public static func rewrite(_ input: String) -> String {
    var result = ""
    var lastIndex = input.startIndex

    input.enumerateManglingCandidates { (candidate) in
      if lastIndex < candidate.startIndex {
        result.append(contentsOf: input[lastIndex..<candidate.startIndex])
      }
      result.append(contentsOf: demangle(candidate) ?? String(candidate))
      lastIndex = candidate.endIndex
    }

    if lastIndex < input.endIndex {
      result.append(contentsOf: input[lastIndex..<input.endIndex])
    }
    return result
  }

  /// Returns each mangled Hylo symbol found in `input` and its demangled representation.
  public static func symbols(in input: String) -> [Symbol] {
    var result: [Symbol] = []
    input.enumerateManglingCandidates { (candidate) in
      if let demangled = demangle(candidate) {
        result.append((mangled: candidate, demangled: demangled))
      }
    }
    return result
  }

  /// Returns the demangled form of `candidate`, or `nil` if parsing is incomplete.
  private static func demangle(_ candidate: Substring) -> String? {
    guard let result = String(candidate).demangled(), !result.contains("#!") else { return nil }
    return result
  }

}

extension String {

  /// Enumerates candidate mangled symbols in `self`.
  ///
  /// A candidate starts at `$` and continues while characters remain valid mangling symbols.
  fileprivate func enumerateManglingCandidates(_ action: (Substring) -> Void) {
    var remaining = self[...]
    while let start = remaining.firstIndex(of: "$") {
      let token = remaining[start...]
      let end = token.firstIndex(where: { (c) in !c.isValidManglingSymbol }) ?? token.endIndex
      action(token[..<end])
      remaining = token[end...]
    }
  }

}

extension Character {

  /// `true` iff `self` is valid in a mangled Hylo symbol.
  fileprivate var isValidManglingSymbol: Bool {
    isASCII && (isLetter || isNumber || self == "_" || self == "." || self == "$")
  }

}
