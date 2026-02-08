import Clang
import Foundation
import cclang

extension CXString {
  func asSwift() -> String {
    guard clang_getCString(self) != nil else { return "" }
    let result = String(cString: clang_getCString(self)!)
    clang_disposeString(self)
    return result
  }
}

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

/// Represents information about a class member extracted from the AST
struct ClassMemberInfo {
  var publicMethods: [MethodInfo] = []
  var publicFields: [FieldInfo] = []
  var nestedTypes: [TypeAliasInfo] = []
}

struct MethodInfo {
  let name: String
  let isConst: Bool
  let isStatic: Bool
  let isDeleted: Bool
  let returnType: CType
  let parameters: [(name: String, type: CType)]
  let documentation: String?
}

struct FieldInfo {
  let name: String
  let type: CType
  let documentation: String?
}

struct TypeAliasInfo {
  let name: String
  let underlyingType: String
}

/// Wraps the given (non-movable, non-copyable) C++ class in a new, movable and non-copyable C++ class, storing the
/// wrapped class in a `std::unique_ptr`. The wrapper class is emitted to the given output file.
///
/// Parameters:
/// - `class`: Qualified name of the class to wrap, e.g. `::llvm::LLVMContext`
/// - `includes`: Array of include directives needed for the wrapped class
func wrap(
  class classToWrap: QualifiedClassName, in file: URL, wrappedAs: QualifiedClassName,
  includes: [String], output: URL
) {
  do {
    // Parse the header file
    let translationUnit = try TranslationUnit(
      path: file.path,
      commandLineArgs: [
        "-x", "c++",
        "-std=c++20",
        "-I/home/ambrus/llvm-20.1.6-x86_64-unknown-linux-gnu-MinSizeRel/include",
      ]
    )

    // Find the class declaration
    guard
      let classDecl = findClassDeclaration(
        in: translationUnit,
        qualifiedName: classToWrap
      )
    else {
      print("Error: Could not find class '\(classToWrap)' in '\(file.path)'")
      return
    }

    // Extract class members
    let memberInfo = extractClassMembers(from: classDecl)

    // Generate wrapper code (pass classDecl for printing policy)
    let wrapperCode = generateWrapperCode(
      originalClass: classToWrap,
      wrappedAs: wrappedAs,
      memberInfo: memberInfo,
      includes: includes,
      classCursor: classDecl
    )

    // Write to output file
    try wrapperCode.write(to: output, atomically: true, encoding: .utf8)
    print("Successfully generated wrapper for '\(classToWrap)' at '\(output.path)'")

  } catch {
    print("Error: \(error)")
  }
}

/// Finds a class declaration in the translation unit by its qualified name
func findClassDeclaration(
  in translationUnit: TranslationUnit,
  qualifiedName: QualifiedClassName
) -> Cursor? {
  var foundClass: Cursor? = nil
  var currentNamespaces: [String] = []

  func visitCursor(_ cursor: Cursor) -> ChildVisitResult {
    // Track namespace context
    if cursor is Namespace {
      currentNamespaces.append(cursor.description)
      defer { currentNamespaces.removeLast() }
      cursor.visitChildren(visitCursor)
      return .continue
    }

    // Check for class declaration
    if cursor is ClassDecl || cursor is StructDecl {
      let className = cursor.description
      if className == qualifiedName.name && currentNamespaces == qualifiedName.namespaces {
        foundClass = cursor
        return .abort
      }
    }

    return .recurse
  }

  translationUnit.visitChildren(visitCursor)
  return foundClass
}

extension Cursor {
  var isScopedEnumDecl: Bool {
    return clang_getCursorKind(self.asClang()) == CXCursor_EnumDecl
      && clang_EnumDecl_isScoped(self.asClang()) != 0
  }
}
/// Extracts public members from a class declaration
func extractClassMembers(from classDecl: Cursor) -> ClassMemberInfo {
  var memberInfo = ClassMemberInfo()
  var currentAccessSpecifier: CXXAccessSpecifierKind? = .public  // Default for structs

  classDecl.visitChildren { cursor in
    // Track access specifier changes
    if let accessSpec = cursor.accessSpecifier {
      currentAccessSpecifier = accessSpec
    }

    // Only process public members
    guard currentAccessSpecifier == .public else {
      return .continue
    }

    // Extract methods
    if let method = cursor as? CXXMethod {
      if let methodInfo = extractMethodInfo(from: method) {
        memberInfo.publicMethods.append(methodInfo)
      }
    }

    // Extract fields
    if let field = cursor as? FieldDecl {
      if let fieldInfo = extractFieldInfo(from: field) {
        memberInfo.publicFields.append(fieldInfo)
      }
    }

    // Extract nested type aliases and enums
    if cursor is TypedefDecl || cursor is TypeAliasDecl || cursor.isScopedEnumDecl {
      if let typeInfo = extractTypeAliasInfo(from: cursor) {
        memberInfo.nestedTypes.append(typeInfo)
      }
    }

    return .recurse
  }

  return memberInfo
}

/// Extracts information about a method
func extractMethodInfo(from method: CXXMethod) -> MethodInfo? {
  let name = method.description

  // Get method type information (for const checking)
  guard let methodType = method.type else { return nil }

  // Get the result type using our helper function
  guard let resultType = method.resultType else { return nil }

  // Extract parameters
  var parameters: [(name: String, type: CType)] = []
  for child in method.children() {
    if child is ParmDecl {
      let paramName = child.description.isEmpty ? "" : child.description
      if let paramType = child.type {
        parameters.append((name: paramName, type: paramType))
      }
    }
  }

  // Check if method is const
  let typeDesc = methodType.description
  let isConst = typeDesc.contains("const")

  // Check if method is deleted
  let isDeleted = clang_CXXMethod_isDeleted(method.asClang()) != 0

  // For now, assume all methods are non-static (instance methods)
  // In the future, we could detect static methods by checking storage class
  let isStatic = false

  // Extract documentation comment
  let rawComment = clang_Cursor_getRawCommentText(method.asClang()).asSwift()
  let documentation = rawComment.isEmpty ? nil : rawComment

  return MethodInfo(
    name: name,
    isConst: isConst,
    isStatic: isStatic,
    isDeleted: isDeleted,
    returnType: resultType,
    parameters: parameters,
    documentation: documentation
  )
}

/// Extracts information about a field
func extractFieldInfo(from field: FieldDecl) -> FieldInfo? {
  guard let type = field.type else { return nil }

  // Extract documentation comment
  let rawComment = clang_Cursor_getRawCommentText(field.asClang()).asSwift()
  let documentation = rawComment.isEmpty ? nil : rawComment

  return FieldInfo(name: field.description, type: type, documentation: documentation)
}

/// Extracts information about a nested type
func extractTypeAliasInfo(from cursor: Cursor) -> TypeAliasInfo? {
  guard let t = cursor.type else { return nil }
  return TypeAliasInfo(
    name: cursor.description,
    underlyingType: t.fullyQualifiedName(using: cursor.printingPolicy)
  )
}

/// Converts a Clang type to a fully qualified type string using SwiftClang's printing policy
func fullyQualifiedTypeName(_ type: CType, cursor: Cursor) -> String {
  // Get printing policy from cursor and enable fully qualified names
  var policy = cursor.printingPolicy
  policy.set(.fullyQualifiedName, value: 1)

  // Use the new fullyQualifiedName API
  return type.fullyQualifiedName(using: policy)
}

/// Generates the wrapper C++ code
func generateWrapperCode(
  originalClass: QualifiedClassName,
  wrappedAs: QualifiedClassName,
  memberInfo: ClassMemberInfo,
  includes: [String],
  classCursor: Cursor
) -> String {
  var code = """
    // Auto-generated wrapper for \(originalClass)
    #pragma once
    #include <memory>

    """

  // Add user-specified includes
  for include in includes {
    code += "#include \(include)\n"
  }

  code += """


    """

  // Generate namespace opening
  for namespace in wrappedAs.namespaces {
    code += "namespace \(namespace) {\n"
  }

  code += """

    class \(wrappedAs.name) {
    private:
      std::unique_ptr<\(originalClass)> wrapped_;

    public:
      // Constructor
      \(wrappedAs.name)() : wrapped_(std::make_unique<\(originalClass)>()) {}
      
      // Move constructor
      \(wrappedAs.name)(\(wrappedAs.name)&&) = default;
      
      // Move assignment
      \(wrappedAs.name)& operator=(\(wrappedAs.name)&&) = default;
      
      // Destructor
      ~\(wrappedAs.name)() = default;
      
      // Deleted copy operations
      \(wrappedAs.name)(const \(wrappedAs.name)&) = delete;
      \(wrappedAs.name)& operator=(const \(wrappedAs.name)&) = delete;
      
      // Access to wrapped object
      \(originalClass)& asLLVM() { return *wrapped_; }
      const \(originalClass)& asLLVM() const { return *wrapped_; }


    """

  // Generate type aliases for nested types
  for typeAlias in memberInfo.nestedTypes {
    code += "  using \(typeAlias.name) = \(originalClass)::\(typeAlias.name);\n"
  }

  if !memberInfo.nestedTypes.isEmpty {
    code += "\n"
  }

  // Generate getters and setters for public fields
  for field in memberInfo.publicFields {
    let qualifiedFieldType = field.type.fullyQualifiedName(using: classCursor.printingPolicy)

    // Add documentation if available
    if let doc = field.documentation {
      code += "\(doc)\n"
    }

    code += "  // Accessors for field '\(field.name)'\n"
    code +=
      "  \(qualifiedFieldType) get\(field.name.capitalized)() const { return wrapped_->\(field.name); }\n"
    code +=
      "  \(qualifiedFieldType) get\(field.name.capitalized)() { return wrapped_->\(field.name); }\n"

    // Only generate setter if field is not const
    if !field.type.isConstQualified {
      code +=
        "  void set\(field.name.capitalized)(\(qualifiedFieldType) value) { wrapped_->\(field.name) = std::move(value); }\n"
    }
    code += "\n"
  }

  // Generate forwarding methods
  for method in memberInfo.publicMethods {
    let qualifiedReturnType = method.returnType.fullyQualifiedName(
      using: classCursor.printingPolicy)

    // Generate unique parameter names for unnamed parameters
    var usedNames = Set<String>()
    let parametersWithNames = method.parameters.enumerated().map {
      (index, param) -> (name: String, type: CType) in
      var paramName = param.name
      if paramName.isEmpty {
        paramName = "arg\(index)"
      }
      // Ensure uniqueness
      var uniqueName = paramName
      var counter = 0
      while usedNames.contains(uniqueName) {
        counter += 1
        uniqueName = "\(paramName)\(counter)"
      }
      usedNames.insert(uniqueName)
      return (name: uniqueName, type: param.type)
    }

    let paramsList = parametersWithNames.map { param in
      let qualifiedParamType = fullyQualifiedTypeName(param.type, cursor: classCursor)
      return "\(qualifiedParamType) \(param.name)"
    }.joined(separator: ", ")

    let constQualifier = method.isConst ? " const" : ""
    let staticQualifier = method.isStatic ? "static " : ""

    let argsList = parametersWithNames.map { param in
      let qualifiedParamType = fullyQualifiedTypeName(param.type, cursor: classCursor)
      return "std::forward<\(qualifiedParamType)>(\(param.name))"
    }.joined(separator: ", ")

    // Add documentation if available
    if let doc = method.documentation {
      code += "  \(doc)\n"
    } else {
      code += "  // Forwarding method '\(method.name)'\n"
    }

    if method.isDeleted {
      // Deleted function - just declare it as deleted
      code +=
        "  \(staticQualifier)\(qualifiedReturnType) \(method.name)(\(paramsList))\(constQualifier) = delete;\n\n"
    } else {
      // Normal function - forward the call
      code +=
        "  \(staticQualifier)\(qualifiedReturnType) \(method.name)(\(paramsList))\(constQualifier) {\n"
      if qualifiedReturnType != "void" {
        code += "    return wrapped_->\(method.name)(\(argsList));\n"
      } else {
        code += "    wrapped_->\(method.name)(\(argsList));\n"
      }
      code += "  }\n\n"
    }
  }

  code += "};\n\n"

  // Generate namespace closing
  for _ in wrappedAs.namespaces.reversed() {
    code += "} // namespace\n"
  }

  return code
}

extension String {
  var capitalized: String {
    guard let first = self.first else { return self }
    return first.uppercased() + self.dropFirst()
  }
}

wrap(
  class: .init("::llvm::LLVMContext")!,
  in: URL(
    filePath:
      "/home/ambrus/llvm-20.1.6-x86_64-unknown-linux-gnu-MinSizeRel/include/llvm/IR/LLVMContext.h"),
  wrappedAs: .init("::LLVM::LLVMContext")!,
  includes: [
    "<llvm/IR/LLVMContext.h>",
    "<llvm/IR/Module.h>",
    "<llvm/IR/IRBuilder.h>",
    "<llvm/IR/Function.h>",
    "<llvm/IR/BasicBlock.h>",
    "<llvm/IR/Type.h>",
    "<llvm/IR/Verifier.h>",
    "<llvm/IR/DiagnosticInfo.h>",
    "<llvm/IR/DiagnosticHandler.h>",
    "<llvm/IR/LLVMRemarkStreamer.h>",
    "<llvm/IR/DataLayout.h>",
    "<llvm/Support/raw_ostream.h>",
    "<llvm/Remarks/RemarkStreamer.h>",
  ],
  output: URL(
    filePath:
      "/home/ambrus/hylo-new/SwiftyLLVM/Sources/LLVMWrapperCxx/include/generated/LLVMContext.hpp")
)
