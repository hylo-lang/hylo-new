import LLVM
import LLVMEmitter
import XCTest

class ExampleTest: XCTestCase {
  func testExample() {
    let example = Example(1, 2)
    XCTAssertEqual(example.sum(), 3)
  }

  func testLLVM() {
    XCTAssertEqual(exampleFun(1, 2), 3)
  }

}
