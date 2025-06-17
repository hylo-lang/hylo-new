/// The tokens of a source file.
public struct Lexer: IteratorProtocol, Sequence {

  /// A snapshot of a lexer's internal state.
  public typealias Backup = SourceFile.Index

  /// The source file being tokenized.
  public let source: SourceFile

  /// The current position of the lexer in `source`.
  public private(set) var position: SourceFile.Index

  /// Creates an instance enumerating the tokens in `source`.
  public init(tokenizing source: SourceFile) {
    self.source = source
    self.position = source.startIndex
  }

  /// Advances to the next token and returns it, or returns `nil` if no next token exists.
  public mutating func next() -> Token? {
    if let unterminated = discardWhitespacesAndComments() { return unterminated }
    guard let head = peek() else { return nil }

    if let t = takeNumericLiteral() {
      return t
    } else if head == "\"" {
      return takeStringLiteral()
    } else if head.isIdentifierHead {
      return takeKeywordOrIdentifier()
    } else if head == "#" {
      return takePoundKeywordOrLiteral()
    } else if head.isOperator {
      return takeOperator()
    } else {
      return takePunctuationOrParenthesizedOperator()
    }
  }

  /// Returns a snapshot of `self`'s internal state that can be restored using `restore(_:)`.
  public func save() -> Backup {
    position
  }

  /// Restores the state of `self` from a snapshot.
  public mutating func restore(_ snapshot: Backup) {
    position = snapshot
  }

  /// Consumes and returns a numeric literal iff one can be scanned from the character stream.
  private mutating func takeNumericLiteral() -> Token? {
    let p = take("-") ?? position

    guard let h = peek(), h.isDecimalDigit else {
      position = p
      return nil
    }

    // Is the literal is non-decimal?
    if let i = take("0") {
      let isEmpty: Bool

      switch peek() {
      case .some("x"):
        discard()
        isEmpty = takeDigitSequence(\.isHexDigit).isEmpty
      case .some("o"):
        discard()
        isEmpty = takeDigitSequence(\.isOctalDigit).isEmpty
      case .some("b"):
        discard()
        isEmpty = takeDigitSequence(\.isBinaryDigit).isEmpty
      default:
        isEmpty = true
      }

      if !isEmpty {
        // Non-decimal number literals cannot have an exponent.
        return .init(tag: .integerLiteral, site: span(p ..< position))
      } else {
        position = i
      }
    }

    // Read the integer part.
    let q = take(while: { (c) in c.isDecimalDigit || (c == "_") }).endIndex

    // Is there a fractional part?
    if let i = take(".") {
      if takeDigitSequence(\.isDecimalDigit).isEmpty {
        position = i
        return .init(tag: .integerLiteral, site: span(p ..< q))
      }
    }

    // Is there an exponent?
    if let i = take("e") ?? take("E") {
      _ = take("+") ?? take("-")
      if takeDigitSequence(\.isDecimalDigit).isEmpty {
        position = i
      }
    }

    // No fractional part and no exponent.
    if position == q {
      return .init(tag: .integerLiteral, site: span(p ..< position))
    } else {
      return .init(tag: .floatingPointLiteral, site: span(p ..< position))
    }
  }

  /// Consumes and returns the longest sequence that start with a digit and then contains either
  /// digits or the underscore, using `isDigit` to determine whether a character is a digit.
  private mutating func takeDigitSequence(_ isDigit: (Character) -> Bool) -> Substring {
    if let h = peek(), isDigit(h) {
      return take(while: { (c) in isDigit(c) || (c == "_") })
    } else {
      return source.text[position ..< position]
    }
  }

  /// Consumes and returns a string literal.
  private mutating func takeStringLiteral() -> Token {
    let start = position
    _ = take()

    var escape = false
    while position < source.endIndex {
      if !escape && (take("\"") != nil) {
        return .init(tag: .stringLiteral, site: span(start ..< position))
      } else if take("\\") != nil {
        escape = !escape
      } else {
        discard()
        escape = false
      }
    }

    return .init(tag: .unterminatedStringLiteral, site: span(start ..< position))
  }

  /// Consumes and returns a keyword or identifier.
  private mutating func takeKeywordOrIdentifier() -> Token {
    let word = take(while: \.isIdentifierTail)

    if word == "as" {
      _ = take("!") ?? take("*")
      return .init(tag: .conversion, site: span(word.startIndex ..< position))
    }

    let tag: Token.Tag
    switch word {
    case "_": tag = .underscore
    case "auto": tag = .auto
    case "case": tag = .case
    case "else": tag = .else
    case "enum": tag = .enum
    case "extension": tag = .extension
    case "false": tag = .false
    case "fun": tag = .fun
    case "given": tag = .given
    case "if": tag = .if
    case "import": tag = .import
    case "infix": tag = .infix
    case "init": tag = .`init`
    case "inout": tag = .inout
    case "internal": tag = .internal
    case "let": tag = .let
    case "match": tag = .match
    case "postfix": tag = .postfix
    case "prefix": tag = .prefix
    case "private": tag = .private
    case "public": tag = .public
    case "return": tag = .return
    case "set": tag = .set
    case "sink": tag = .sink
    case "static": tag = .static
    case "struct": tag = .struct
    case "subscript": tag = .subscript
    case "trait": tag = .trait
    case "true": tag = .true
    case "type": tag = .type
    case "var": tag = .var
    case "where": tag = .where
    default: tag = .name
    }

    assert(!word.isEmpty)
    return .init(tag: tag, site: span(word.startIndex ..< word.endIndex))
  }

  /// Consumes and returns a keyword prefixed by a '#' symbol.
  private mutating func takePoundKeywordOrLiteral() -> Token {
    let start = position
    _ = take()

    let tag: Token.Tag
    switch take(while: \.isIdentifierTail) {
    case "": tag = .error
    default: tag = .poundLiteral
    }

    return .init(tag: tag, site: span(start ..< position))
  }

  /// Consumes and returns an operator.
  private mutating func takeOperator() -> Token {
    let start = position

    // Leading angle brackets are tokenized individually, to parse generic clauses.
    if let h = peek(), h.isAngleBracket {
      return takePunctuationOrParenthesizedOperator()
    }

    // Stars are tokenized individually, to parse kinds.
    if take("*") != nil {
      return .init(tag: .star, site: span(start ..< position))
    }

    let text = take(while: \.isOperator)
    let tag: Token.Tag
    switch text {
    case "&": tag = .ampersand
    case "=": tag = .assign
    case "->": tag = .arrow
    case "==": tag = .equal
    default: tag = .operator
    }
    return .init(tag: tag, site: span(start ..< position))
  }

  /// Consumes and returns a punctuation token or parenthesized operator if possible; otherwise
  /// consumes a single character and returns an error token.
  private mutating func takePunctuationOrParenthesizedOperator() -> Token {
    let start = position
    let tag: Token.Tag
    switch take() {
    case "<": tag = .leftAngle
    case ">": tag = .rightAngle
    case "{": tag = .leftBrace
    case "}": tag = .rightBrace
    case "[": tag = .leftBracket
    case "]": tag = .rightBracket
    case "(": tag = take("+)") == nil ? .leftParenthesis : .oplus
    case ")": tag = .rightParenthesis
    case "@": tag = .at
    case ",": tag = .comma
    case ";": tag = .semicolon
    case ":": tag = take(":") == nil ? .colon : .doubleColon
    case ".": tag = take("..") == nil ? .dot : .ellipsis
    default: tag = .error
    }
    return .init(tag: tag, site: span(start ..< position))
  }

  /// Consumes and returns the next character.
  private mutating func take() -> Character {
    defer { position = source.index(after: position) }
    return source[position]
  }

  /// Returns the next character without consuming it or `nil` if all the input has been consumed.
  private func peek() -> Character? {
    position != source.endIndex ? source[position] : nil
  }

  /// Discards all whitespaces and comments preceding the next token, returning an error token iff
  /// the scanner encounters an unmatched block comment opening sequence.
  private mutating func discardWhitespacesAndComments() -> Token? {
    while position != source.endIndex {
      if source[position].isWhitespace {
        discard()
      } else if take("//") != nil {
        discard(while: { (c) in !c.isNewline })
      } else if take("/*") != nil {
        var openedBlocks = 1
        let start = position
        while true {
          if take("/*") != nil {
            openedBlocks += 1
          } else if openedBlocks == 0 {
            break
          } else if take("*/") != nil {
            openedBlocks -= 1
          } else if position == source.endIndex {
            return .init(tag: .unterminatedBlockComment, site: span(start ..< position))
          } else {
            discard()
          }
        }
      } else {
        break
      }
    }
    return nil
  }

  /// Discards `count` characters.
  private mutating func discard(_ count: Int = 1) {
    position = source.index(position, offsetBy: count)
  }

  /// Discards characters until `predicate` isn't satisfied or all the input has been consumed.
  private mutating func discard(while predicate: (Character) -> Bool) {
    _ = take(while: predicate)
  }

  /// Returns the longest prefix of the input whose characters all satisfy `predicate` and advances
  /// the position of `self` until after that prefix.
  private mutating func take(while predicate: (Character) -> Bool) -> Substring {
    let start = position
    while (position != source.endIndex) && predicate(source[position]) {
      position = source.index(after: position)
    }
    return source.text[start ..< position]
  }

  /// If the input starts with `prefix`, returns the current position and advances to the position
  /// until after `prefix`. Otherwise, returns `nil`.
  private mutating func take(_ prefix: String) -> String.Index? {
    var newPosition = position
    for c in prefix {
      if newPosition == source.endIndex || source[newPosition] != c { return nil }
      newPosition = source.index(after: newPosition)
    }
    defer { position = newPosition }
    return position
  }

  /// Returns a source span covering `range`.
  private func span(_ range: Range<String.Index>) -> SourceSpan {
    .init(range, in: source)
  }

}

extension Character {

  /// `true` iff `self` is a letter or the underscore.
  fileprivate var isIdentifierHead: Bool {
    self.isLetter || self == "_"
  }

  /// `true` iff `self` is a letter, a decimal digit, or the underscore.
  fileprivate var isIdentifierTail: Bool {
    self.isIdentifierHead || self.isDecimalDigit
  }

  /// `true` iff `self` is an angle bracket.
  fileprivate var isAngleBracket: Bool {
    self == "<" || self == ">"
  }

  /// `true` iff `self` may be part of an operator.
  fileprivate var isOperator: Bool {
    "<>=+-*/%&|!?^~".contains(self)
  }

  /// `true` iff `self` is a decimal digit.
  fileprivate var isDecimalDigit: Bool {
    asciiValue.map({ (ascii) in (0x30 ... 0x39) ~= ascii }) ?? false
  }

  /// `true` iff `self` is an octal digit.
  fileprivate var isOctalDigit: Bool {
    asciiValue.map({ (ascii) in (0x30 ... 0x37) ~= ascii }) ?? false
  }

  /// `true` iff `self` is a binary digit.
  fileprivate var isBinaryDigit: Bool {
    (self == "0") || (self == "1")
  }

}
