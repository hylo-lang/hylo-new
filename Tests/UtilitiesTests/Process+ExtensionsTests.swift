import XCTest
import Utilities

final class ProcessExtensionsTests: XCTestCase {

  /// Tests that we properly handle large amounts of output without
  /// either deadlocking or dropping any.
  func testLargeProcessOutput() throws {

    let lineLength = 63
    let oneLine = String(repeating: "x", count: lineLength)

    // Known size of pipe output buffer
    let outputBufferSize = 64 * 1024 // 64K
    // Number of buffers worth we will output.
    let outputSizeInBuffers = 4
    let totalOutputSize = outputSizeInBuffers * outputBufferSize
    let lineCount = totalOutputSize / (lineLength + 1)
    print("line count", lineCount)
    XCTAssertEqual(
      totalOutputSize % (lineLength + 1), 0,
      "Something is wrong with the test.")

    var executable: String
    var arguments: [String]
    #if os(Windows)
    executable = "cmd"
    arguments = [
      "-c",
      "for /l %i in (1, 1, \(lineCount)) do echo \(oneLine)"]
    #else
    executable = "sh"
    arguments = [
      "-c",
      // The format string keeps seq from formatting its numbers in
      // scientific notation once they reach 1e+06.  It only matters
      // when `outputSizeInBuffers` exceeds 976 but we want the test
      // to work if we increase the value for stress-testing purposes.
      "for i in $(seq -f '%1.0f' 1 \(lineCount)); do echo \(oneLine); done"]
    #endif

    let binary = try Host.findBinaryExecutable(invokedAs: executable)
    let output = try Process.executionOutput(binary, arguments: arguments)
    XCTAssertEqual(output.count - totalOutputSize, 0)
  }

}
