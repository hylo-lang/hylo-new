import Clang
import Foundation

/// Represents a qualified C++ class name, e.g. `::llvm::LLVMContext`, split into its namespaces and class name components.
struct QualifiedClassName: CustomStringConvertible {
  let namespaces: [String]
  let name: String

  /// Parses the given qualified class name into its components.
  public init?(_ name: String) {
    guard name.hasPrefix("::") else {
      return nil
    }
    let components = name.dropFirst(2).split(separator: "::").map(String.init)
    if components.isEmpty {
      return nil
    }
    if components.contains(where: { $0.isEmpty }) {
      return nil
    }
    self.namespaces = Array(components.dropLast())
    self.name = components.last!
  }

  var description: String {
    (namespaces + [name]).map { "::" + $0 }.joined()
  }
}

/// Wraps the given (non-movable, non-copyable) C++ class in a new, movable and non-copyable C++ class, storing the
/// wrapped class in a `std::unique_ptr`. The wrapper class is emitted to the given output file.
///
/// 
///
/// Parameters:
/// - `class`: Qualified name of the class to wrap, e.g. `::llvm::LLVMContext`
func wrap(class: QualifiedClassName, in file: URL, wrappedAs: QualifiedClassName, output: URL) {
  // todo add default move assignment and move constructor, default destructor, explicitly deleted copy constructor and explicitly deleted copy assignment operator
  // todo add namespace around the wrapper class
  // todo add a `asLLVM()` method to expose both a mutable and a const reference to the wrapped class.
  // todo expose all public data members of the wrapped class as getters and setters on the wrapper class in the form of `getX() const`, `getX()`, `setX(X&& x)`.
  // todo expose all type declarations of the original class (such as nested enums, nested type aliases) as type aliases to the corresponding original types with a fully qualified name to prvent ambiguity.
  // todo expose all public methods of the original class (and whatever it inherited publicly) by forwarding the calls to the wrapped class. Take care of how parameters are passed, first design a sound strategy for this.

}

wrap(
  class: .init("::llvm::LLVMContext")!,
  in: URL(
    filePath:
      "/home/ambrus/llvm-20.1.6-x86_64-unknown-linux-gnu-MinSizeRel/include/llvm/IR/LLVMContext.h"),
  wrappedAs: .init("::LLVM::LLVMContext")!,
  output: URL(filePath: "/home/ambrus/hylo-new/Sources/LLVMEmitter/include/generated/LLVMContext.h"))
