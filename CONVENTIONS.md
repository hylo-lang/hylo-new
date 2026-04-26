# Coding Conventions
## Documentation
- Each symbol should have at least a brief one-sentence summary with `///` style comments.
- No documentation is better than documentation that repeats the declaration's name. When adding a summary, make sure it adds value.
- The documentation's intent is to help with local reasoning,functioning as a shortcut for understanding, so users can avoid looking up the code.
- Document preconditions when not obvious from the summary.
- You can phrase the summary in a way that makes the precondition obvious.

## Algorithms
- Avoid using raw loops and complex iteration; use named algorithms instead.
- When custom iteration seems necessary, make an extension on the suitable data type (e.g. `Sequence`, `Array`, `Dictionary`, `URL`, etc.).

## Testing
- All newly added code should be tested.

## Types
- Use strong types where possible to enforce invariants and prevent invalid states.

## Contracts
- Create the strictest contracts possible, so long the client can reason about the preconditions locally.
- If the contract seems to strict, you may relax it and make invalid inputs a reported error (preferably `throw`n).

## Naming
- In a small scope, single-letter variable names can be used.
- No abbreviations shall be used in APIs, unless something is a universally known acronym.

