import Foundation

#if os(Windows)
  import WinSDK
#endif

struct FileError: Error {
  let description: String
}

extension String {

  /// Writes the string to `url` and marks it read-only, to guard against accidental modification.
  /// 
  /// Overwrites an existing file even if that file is currently read-only.
  public func forceWriteReadonly(to url: URL, encoding: Encoding) throws {
    try? url.setWritable(true)
    try write(to: url, atomically: true, encoding: encoding)
    try url.setWritable(false)
  }

}

extension URL {

  /// Makes the file at `self` read-only or writable.
  /// 
  /// On POSIX, this toggles the owner's write access. 
  /// On Windows, this toggles the file's read-only attribute. 
  fileprivate func setWritable(_ writable: Bool) throws {
    #if os(Windows)
      let path = try self.withUnsafeFileSystemRepresentation { (r) in
        if let p = r {
          return String(cString: p)
        } else {
          throw FileError(description: "\(self) cannot be represented as a file system path.")
        }
      }

      try path.withCString(encodedAs: UTF16.self) { widePath in
        var attributes = GetFileAttributesW(widePath)
        if attributes == INVALID_FILE_ATTRIBUTES {
          throw FileError(description: "Failed to read file attributes of '\(self)'.")
        }
        if writable {
          attributes &= ~UInt32(FILE_ATTRIBUTE_READONLY)
        } else {
          attributes |= UInt32(FILE_ATTRIBUTE_READONLY)
        }
        guard SetFileAttributesW(widePath, attributes).boolValue else {
          throw FileError(description: "Failed to set file attributes of '\(self)'.")
        }
      }
    #else
      let attributes = try FileManager.default.attributesOfItem(atPath: self.path)
      guard var permissions = (attributes[.posixPermissions] as? NSNumber)?.uint16Value else {
        throw FileError(description: "Failed to read file permissions of '\(self)'.")
      }

      let ownerWrite: UInt16 = 0o200
      if writable {
        permissions |= ownerWrite
      } else {
        permissions &= ~ownerWrite
      }
      
      try FileManager.default.setAttributes([.posixPermissions: NSNumber(value: permissions)],
        ofItemAtPath: self.path)
    #endif
  }

}
