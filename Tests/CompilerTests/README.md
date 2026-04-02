# Compiler tests

This directory contains tests running the entire compiler on program inputs.
Test suites are generated with the contents of the `negative` and `positive` sub-directories, which define use cases.
A use case is either a single Hylo source file or a directory representing a package.

A single-file test is compiled to a binary executable, just as if it was passed as an argument to `hc`.
A package test is built according to the configuration specified by its manifest.

## Test kinds

Tests are discovered from two directories:

- `positive/` contains programs that are expected to compile successfully.
- `negative/` contains programs that are expected to produce at least one compilation error.

Each test case can be written in one of two forms:

- A single `.hylo` source file.
- A package directory whose manifest is stored in `package.json`.

For single-file tests, the manifest is read from the first line of the file when that line starts with `//!`.
For package tests, the manifest is read from the `options` array in `package.json`.

## Manifest format

Manifest options are written as space-separated entries.
Each entry is either:

- A flag such as `no-std`.
- A key-value pair such as `stage:typing`.

Example single-file manifest:

```hylo
//! no-std stage:lowering
```

Example package manifest:

```json
{
  "options": ["stage:run", "assert-exit-code:0"]
}
```

## Supported manifest options

### `no-std`

Omits loading and linking the standard library while compiling the test.

### `stage:<stage>`

Selects how far the compiler should run before the test stops.
The supported stages are:

- `parsing`
- `typing`
- `lowering`
- `llvmLowering`
- `executableLinking`
- `run`

If no stage is specified, the default is `codegen`.

### `assert-exit-code:<status>`

Requires the test program to be linked to an executable and then run.
The test passes only if the process exits with the specified integer status code.

This option requires `stage:run` to be set; omitting it is a test configuration error.

## Assertions performed by the test runner

### Positive tests

Positive tests assert that compilation completes without fatal diagnostics until the requested stage.

In the `run` stage, the exit code is checked to be 0 or the value specified by `assert-exit-code:<NUMBER>`.

### Negative tests

Negative tests assert that compilation produces at least one error.

If one or more `.diagnostics.expected` files are present, the test runner also compares the rendered diagnostics for each source file with the contents of their corresponding `<SOURCE>.diagnostics.expected` file.

If the observed diagnostics do not match an expected file, the runner also writes a `.diagnostics.observed` file next to the source to help update the fixture.

## Writing expected diagnostics

Expected diagnostics are matched per source file.
This is most useful for negative tests, especially package tests that contain multiple source files.

Use the exact rendered diagnostic output that the compiler emits for that source file.

## Practical guidance

- Use `positive/` for tests that should compile cleanly.
- Use `negative/` for tests that should fail.
- Add `stage:<stage>` when you want to stop before later phases.
- Add `assert-exit-code:<status>` when you need to test runtime behavior.
- Add `no-std` when the test should not depend on the standard library.
- Add `.expected` files when a negative test needs to verify the exact diagnostics.

## Generating Swift tests manually

Test cases are generated automatically as part of SPM's build sequence.
You can also use `hc-tests` to generate test cases manually.
The tool goes over each file or sub-directory under `negative` and `positive` and create a corresponding method to invoke `CompilerTests.compile(_:)`.

