# Compiler tests

This directory contains tests running the entire compiler on program inputs.
Test suites are generated with the contents of the `negative` and `positive` sub-directories, which define use cases.
A use case is either a single Hylo source file or a directory representing a package.

A single-file test is compiled to a binary executable, just as if it was passed as an argument to `hc`.
A package test is built according to the configuration specified by its manifest.

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
