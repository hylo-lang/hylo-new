import Archivist
import BigInt

extension BigInt {

  /// Parses an instance from a Hylo integer literal, returning `nil` if parsing failed.
  internal init?<T: StringProtocol>(hyloLiteral literal: T) {
    if literal.starts(with: "-") {
      if let m = BigUInt(hyloLiteral: literal.dropFirst()) {
        self.init(sign: .minus, magnitude: m)
      } else {
        return nil
      }
    } else {
      if let m = BigUInt(hyloLiteral: literal) {
        self.init(sign: .plus, magnitude: m)
      } else {
        return nil
      }
    }
  }

}

extension BigInt: @retroactive Archivable {

  /// Reads `self` from `archive`.
  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let count = try Int(archive.readUnsignedLEB128())
    self = try withUnsafeTemporaryAllocation(of: UInt8.self, capacity: count) { (data) in
      for i in 0 ..< count {
        try data.initializeElement(at: i, to: archive.readByte())
      }
      return BigInt(UnsafeRawBufferPointer(data))
    }
  }

  /// Writes `self` to `archive`.
  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    let data = self.serializeToBuffer()
    defer { data.deallocate() }
    archive.write(contentsOf: data, in: &context) { (b, a, _) in
      a.write(byte: b)
    }
  }

}

extension BigUInt {

  /// Parses an instance from a Hylo integer literal, returning `nil` if parsing failed.
  internal init?<T: StringProtocol>(hyloLiteral literal: T) {
    switch literal.prefix(2) {
    case "0b":
      self.init(literal.dropFirst(2).sans("_"), radix: 2)
    case "0o":
      self.init(literal.dropFirst(2).sans("_"), radix: 8)
    case "0x":
      self.init(literal.dropFirst(2).sans("_"), radix: 16)
    default:
      self.init(literal.sans("_"))
    }
  }

}
