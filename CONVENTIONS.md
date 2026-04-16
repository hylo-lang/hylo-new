# Coding Guidelines

## Documentation

Documentation enables local reasoning - it's a shortcut for understanding so readers can avoid looking up implementation or usages to infer meaning.

- Document every declaration with at least a summary sentence, using `///` style comments.
- Start with a summary sentence fragment describing what it *does* (functions) or what it *is* (types, properties). End with a period.
- Omit needless words: don't repeat the receiver's type, don't write `the`, `given`, `of self`, `of the current object` when context makes these obvious.
- Use `iff` instead of `if` where applicable.
- Use `<...>, if any.` for optional values where the absence reason is obvious. Otherwise: `<...> if <condition>, nil otherwise.`
- Document preconditions with `- Requires:`. If the precondition is obvious from the summary, it need not be repeated.
- Multiple preconditions should be in a markdown list below `- Requires:`.
- Document performance of every operation that doesn't run in constant time and space.
- Conformance implementations are exempt from documentation when nothing useful can be added beyond the protocol requirement itself.

## Contracts

- Create the strictest contracts possible, so long as the client can reason about the preconditions locally.
- Preconditions and postconditions are relationships between components - think in terms of what the caller must provide and what the callee guarantees in return.
- Contract evolution: you may safely weaken preconditions and strengthen postconditions. The reverse breaks clients, so you must inspect all call sites before introducing the change.

## Errors

Distinguish bugs from runtime errors:
- **Bug**: a programming mistake. Stop before more damage is done.
- **Runtime error**: postconditions can't be met despite correct usage. Respond by `throw`ing or returning an optional/result.

When to use each termination mechanism:
- **`precondition(condition, "message")`** - the caller violated a documented requirement. Checked in all builds.
- **`assert(condition, "message")`** - an internal invariant that should hold if the implementation is correct. Checked only in debug builds.
- **`unreachable("message")`** - a code path that is logically impossible given the surrounding control flow or type system.
- **`unimplemented("feature name")`** - a stub for functionality not yet written.
- **`fatalError("message")`** - avoid this, either `unreachable()` or `unimplemented()` should be used instead. If you don't expect it to be unreachable nor unimplemented, prefer reporting an error with throw or returning `nil`.

When a contract seems too strict to use correctly without accidentally breaking preconditions, you can either relax the preconditions (e.g. `demandModule(name:)` - gets or creates the module if it doesn't exist yet) or report an error/return an optional (e.g. `myHashmap[key]` - returns nil if key is not found).

Avoid typed `throws` unless you are confident that the immediate caller will be interested in handling the error and it doesn't just use its description but is interested in the specific error type.

## Safety

- When using an unsafe or unchecked construct (e.g. `@unchecked Sendable`), include a comment that justifies the need and explains why it's safe.

## Algorithms

- Prefer named algorithms over inline loops. A loop is a mechanism; a named algorithm is a statement of intent.
- When a suitable algorithm doesn't exist, create one as an extension on the appropriate type (`Sequence`, `Collection`, etc.) rather than inlining the loop at the call site.
- Structure data so efficient algorithms become possible (e.g. storing something in an ordered collection for binary search, or storing in a hashmap for O(1) lookup).

## Types

- Use strong types to encode invariants. If a value can only be valid in certain states, make invalid states unrepresentable.
- Every instance of a type should have exactly one clearly-defined value, expressed in terms of its operations.
- Keep the efficient basis of a type small and well-documented. All other operations should be derivable from it.
- Prefer value types. Reference types (`class`) are appropriate only for identity, shared mutable state, or non-copyable resources—document why.

## Naming

- Follow the [Swift API Design Guidelines](https://www.swift.org/documentation/api-design-guidelines/). Name mutating methods with imperative verb phrases; name nonmutating variants with past participle or `ing` forms.
- No abbreviations in APIs unless universally known (e.g. `URL`, `ID`).
- Don't include the type in a binding's name.
- If the type is too weak, a qualified argument label can help (e.g. `f(outputDirectory: URL)`), but prefer making the type more strict to capture the invariants (e.g. `f(output: DirectoryURL)`).
- Single-letter names are fine in small scopes: `l`/`r` for binary operators, `n` for a syntax node, `m` for a module, `i`/`j` for indices.
- When naming a collection of objects, use a plural form (even in case of short names): `files`, `xs`, `ms`.
- Prefer descriptive labels over `for` as a parameter label.

## Testing

- All new code should be covered by tests.
- Tests should exercise the contract: verify postconditions under valid preconditions.
- (Death tests are not supported in Swift XCTest, but it would be nice to write tests that exercise that libraries uphold safety by crashing correctly on precondition violations.)

## Formatting

- Indent with 2 spaces.
- Use a 100-column line limit.
- Add blank lines inside type, extension, and enum declarations - leave one empty line after the opening brace and before the closing brace.
- Separate protocol conformances into their own extensions unless it's a marker protocol.
- Use explicit named parameters in parentheses for multi-statement closures: `{ element in ... }`. Use `$0` shorthand only in short, single-expression closures.
- Use `MARK:` comments to organize sections in large files.
- Use `self.` in initializers when assigning to stored properties.
