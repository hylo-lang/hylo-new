# SwiftyLLVM
A Swift wrapper around LLVM's C++ API.

## Usage
All targets transitively dependent on SwiftyLLVM must set the C++ interoperability mode:

```swift
.target(
  name: "ExampleTarget",
  dependencies: [.product(name: "SwiftyLLVM", package: "SwiftyLLVM")],
  swiftSettings: [.interoperabilityMode(.Cxx)]
),
```