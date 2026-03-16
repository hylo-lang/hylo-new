// swift-tools-version:6.2
import PackageDescription
import Foundation

#if os(Windows)
  let onWindows = true
#else
  let onWindows = false
#endif

/// Swttings common to all Swift targets.
let commonSwiftSettings: [SwiftSetting] = [
  .unsafeFlags(["-warnings-as-errors"])
]

let package = Package(
  name: "Hylo",
  platforms: [
    .macOS(.v15)
  ],
  products: [
    .executable(name: "hc", targets: ["hc"])
  ],
  dependencies: [
    .package(
      url: "https://github.com/attaswift/BigInt.git",
      from: "5.7.0"),
    .package(
      url: "https://github.com/kyouko-taiga/Archivist.git",
      revision: "0b66ecdb3a0da5a94af49274e2751e3332f12b90"),
    .package(
      url: "https://github.com/apple/swift-algorithms.git",
      from: "1.2.0"),
    .package(
      url: "https://github.com/apple/swift-argument-parser.git",
      from: "1.1.4"),
    .package(
      url: "https://github.com/apple/swift-collections.git",
      from: "1.1.0"),
    .package(path: "./Swifty-LLVM"),
  ],
  targets: [
    .executableTarget(
      name: "hc",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
      ],
      swiftSettings: commonSwiftSettings),

    .executableTarget(
      name: "hc-tests",
      dependencies: [
        .product(name: "ArgumentParser", package: "swift-argument-parser")
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "Driver",
      dependencies: [
        .target(name: "FrontEnd"),
        .target(name: "LLVMEmitter"),
        .target(name: "StandardLibrary"),
        .target(name: "Utilities"),
        .product(name: "Archivist", package: "archivist"),
        .product(name: "SwiftyLLVM", package: "Swifty-LLVM"),
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "FrontEnd",
      dependencies: [
        .target(name: "Utilities"),
        .target(name: "StableCollections"),
        .product(name: "Archivist", package: "archivist"),
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
        .product(name: "BigInt", package: "BigInt"),
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "LLVMEmitter",
      dependencies: [
        .target(name: "FrontEnd"),
        .product(name: "SwiftyLLVM", package: "Swifty-LLVM"),
        .target(name: "Utilities"),
      ],
      path: "Sources/BackEnd/LLVM",
      swiftSettings: commonSwiftSettings,
    ),

    .target(
      name: "StableCollections",
      dependencies: [
        .target(name: "Utilities")
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "StandardLibrary",
      path: "StandardLibrary",
      exclude: [],
      resources: [.copy("Full"), .copy("Minimal")],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "Utilities",
      dependencies: [
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "CompilerTests",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "StandardLibrary"),
        .target(name: "Utilities"),
      ],
      exclude: ["README.md"] + allNonSwiftFiles(in: "Tests/CompilerTests"),
      swiftSettings: commonSwiftSettings,
      plugins: ["CompilerTestsPlugin"]),

    .testTarget(
      name: "FrontEndTests",
      dependencies: [
        .target(name: "FrontEnd")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "LLVMEmitterTests",
      dependencies: [
        .target(name: "LLVMEmitter"),
        .target(name: "Driver")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "StableCollectionsTests",
      dependencies: [
        .target(name: "StableCollections")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "UtilitiesTests",
      dependencies: [
        .target(name: "Utilities")
      ],
      swiftSettings: commonSwiftSettings),

    .plugin(
      name: "CompilerTestsPlugin",
      capability: .buildTool(),
      dependencies: [
        .target(name: "hc-tests")
      ]),
  ])

/// Returns the list of relative urls of all non-swift files in the given directory.
func allNonSwiftFiles(in directory: String) -> [String] {
  guard let enumerator: FileManager.DirectoryEnumerator = FileManager.default.enumerator(atPath: directory) 
  else { return [] }
  
  let l = enumerator.compactMap { $0 as? String }
    .filter { !$0.hasSuffix(".swift") && !isDirectory(directory + "/" + $0) }

  return l
}

func isDirectory(_ path: String) -> Bool {
  // Heuristic for common file formats:
  if path.hasSuffix(".hylo") || path.hasSuffix(".observed") || path.hasSuffix(".expected") ||
    path.hasSuffix(".diagnostics") || path.hasSuffix(".c") {
    return false
  }

  // Fallback to filesystem check
  var isDirectory: ObjCBool = true
  if !FileManager.default.fileExists(atPath: path, isDirectory: &isDirectory) {
    fatalError("Expected file or directory at recently scanned path: \(path)\nPlease rerun the build.")
  }
  return isDirectory.boolValue
}