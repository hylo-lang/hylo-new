// swift-tools-version:6.0
import PackageDescription

let package = Package(
  name: "HyloSwiftFormatter",
  dependencies: [
    .package(url: "https://github.com/apple/swift-syntax", from: "602.0.0")
  ],
  targets: [
    .target(
      name: "FormatFixups",
      dependencies: [
        .product(name: "SwiftSyntax", package: "swift-syntax"),
        .product(name: "SwiftParser", package: "swift-syntax"),
      ]),

    .executableTarget(
      name: "hylo-format",
      dependencies: [
        .target(name: "FormatFixups")
      ]),

    .testTarget(
      name: "FormatFixupsTests",
      dependencies: [
        .target(name: "FormatFixups")
      ]),
  ])
