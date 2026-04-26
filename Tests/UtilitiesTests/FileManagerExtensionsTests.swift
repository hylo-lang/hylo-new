import Utilities
import XCTest
import Foundation

final class FileManagerExtensionsTests: XCTestCase {

  func testWithUniqueTemporaryDirectory() throws {
    var path: URL? = nil
    try FileManager.default.withUniqueTemporaryDirectory { p in
      path = p
      var isDirectory: ObjCBool = false
      XCTAssertTrue(FileManager.default.fileExists(atPath: p.path, isDirectory: &isDirectory))
      XCTAssertTrue(isDirectory.boolValue)
    }
    let p = try XCTUnwrap(path)
    XCTAssertFalse(FileManager.default.fileExists(atPath: p.path))
  }

  func testWithUniqueTemporaryDirectoryAsync() async throws {
    var path: URL? = nil
    try await FileManager.default.withUniqueTemporaryDirectory { p in
      path = p
      var isDirectory: ObjCBool = false
      XCTAssertTrue(FileManager.default.fileExists(atPath: p.path, isDirectory: &isDirectory))
      XCTAssertTrue(isDirectory.boolValue)

      try await Task.sleep(for: .microseconds(0))
    }
    let p = try XCTUnwrap(path)
    XCTAssertFalse(FileManager.default.fileExists(atPath: p.path))
  }

}
