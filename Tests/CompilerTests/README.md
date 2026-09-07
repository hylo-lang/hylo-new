# Compiler tests

This directory contains tests running the entire compiler on program inputs.
Test suites are generated with the contents of the `negative` and `positive` sub-directories, which define use cases.
A use case is either a single Hylo source file or a directory representing a package.

A single-file test is compiled to a binary executable, just as if it was passed as an argument to `hc`.
A package test is built according to the configuration specified by its manifest.
The generated binary is invoked with working directory set to the package test's root directory or
the parent of a single-file test case. 

## Test attributes

Tests can be configured with various flags and option, called *test attributes*.
For a single-file test, these settings are written on the first line, prefixed by `//!`.
For instance, the following test will compile the program, execute it, and check that the exit status is `42`.

```hylo
//! exit-status:42

public fun main() -> Int32 { 42 }
```

For a package test, settings are written by adding an `options` entry to the manifest, whole value is an array of flags and options expressed as character strings. 

### Testing without the standard library

Add the test attribute `no-std` on the first line of a single-file test to disable the loading of the standard library.
We encourage using `no-std` when possible, as it makes the test significantly faster.

### Stopping after a compilation stage

Add the test attribute `stage:stage_name` to stop the driver after a specific compilation stage.
Valid stages are:

- `stage:parsing`
- `stage:typing`
- `stage:lowering`
- `stage:llvm`
- `stage:execution` (default); applicable only in positive tests.

### Termination

Add the test attribute `exit-status:n` to specify the expected expected exit status of the compiled program.
`0` is expected by default.

Add the test attribute `trap` to specify that the compiled program is expected to trap (e.g., by calling `fatal_error()`).

These two test attributes are mutually exclusive.
Both of them are applicable only in combination with `stage:execution`.

## Textual Artifact Expectations

Add a `test-case.<artifact-tag>.expected` file besides your `test-case.hylo` to assert the contents of a compilation artifact. Valid artifacts are:
- `*.raw-ir.expected`
- `*.refined-ir.expected`
- `*.llvm-ir.expected`

An artifact is composed of a set of contiguous sections, delimited by empty lines. E.g. each function in Hylo IR and LLVM IR are their own sections.

It is sufficient to specify a subset of sections of the actual artifact. The expected section is matched with the observed section having the closest first line. Then they are compared for equality.

## Inspecting Intermediate Artifacts

Intermediate compilation artifacts are saved on test failure as `*.observed` files besides the corresponding test case. You can temporarily set `alwaysSaveArtifacts` to `true` in `CompilerTests.swift` to save these even when a test passes.

## Generating Swift tests manually

Test cases are generated automatically as part of SPM's build sequence.
You can also use `hc-tests` to generate test cases manually.
The tool goes over each file or sub-directory under `negative` and `positive` and create a corresponding method to invoke `CompilerTests.compile(_:)`.

## Testing Cross-Compilation

> Note: Due to our current qemu setup, this only works on Linux, and requires a target with Linux ABI (not freestanding).

To run the tests for another target under qemu's user-mode emulator:

- Install qemu's user-mode emulators and the cross toolchain of the target.
  On Ubuntu those are the `qemu-user` package, which provides the `qemu-<arch>` emulators, and the
  `gcc-<target>` package (e.g. `gcc-arm-linux-gnueabihf`), which provides the target's headers,
  libc and crt objects.
- Build with `-Xswiftc -DSWIFTY_LLVM_CROSS_COMPILATION_ENABLED`.
- Set the following environment variables before running the tests:
  - `HYLO_TEST_TARGET`: the LLVM target triple (default: host)
  - `HYLO_TEST_RUNNER`: the emulator for that target, e.g. `qemu-arm`. This can be a binary name on `PATH` or an absolute path. (default: no emulator)
  - `QEMU_LD_PREFIX`: the absolute path to the directory holding the target's dynamic linker and shared libraries.

For instance, to run the tests on 32-bit ARM:

```bash
swift build --build-tests -Xswiftc -enable-testing \
  -Xswiftc -DSWIFTY_LLVM_CROSS_COMPILATION_ENABLED

HYLO_TEST_TARGET=armv7-unknown-linux-gnueabihf \
  HYLO_TEST_RUNNER=qemu-arm \
  QEMU_LD_PREFIX=/usr/arm-linux-gnueabihf \
  swift test --skip-build -Xswiftc -enable-testing -Xswiftc -DSWIFTY_LLVM_CROSS_COMPILATION_ENABLED  --filter 'CompilerTests\.CompilerTests/'
```
