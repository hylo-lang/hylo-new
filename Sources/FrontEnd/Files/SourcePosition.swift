/// A character boundary in a source file.
public struct SourcePosition: Hashable {

  /// The source file containing the position.
  public let source: SourceFile

  /// The position relative to the source file.
  public let index: String.Index

  /// Creates an instance with the given properties.
  public init(_ index: String.Index, in file: SourceFile) {
    self.source = file
    self.index = index
  }

  /// The 0-based line and offset of this position.
  /// 
  /// Offsets are counted in Unicode extended grapheme clusters from line start.
  public var lineAndOffset: (line: Int, offset: Int) {
    let r = source.lineAndOffset(index)
    return (r.line, r.offset)
  }

  /// The 0-based line and 0-based UTF-16 offset of this position.
  public var lineAndUTF16Offset: LineAndUTF16Offset {
    source.lineAndUTF16Offset(index)
  }

}

extension SourcePosition: Comparable {

  public static func < (l: Self, r: Self) -> Bool {
    precondition(l.source == r.source, "incompatible locations")
    return l.index < r.index
  }

}

extension SourcePosition: CustomStringConvertible {

  public var description: String {
    let (line, offset) = lineAndOffset
    return "\(source.name):\(line + 1):\(offset + 1)"
  }

}
