// See https://github.com/swiftlang/swift/issues/75601
@preconcurrency import func Foundation.putc
@preconcurrency import var Foundation.stderr

/// A handle to the standard error.
internal struct StandardError: TextOutputStream, Sendable {

  internal mutating func write(_ string: String) {
    for byte in string.utf8 { putc(numericCast(byte), stderr) }
  }

}
