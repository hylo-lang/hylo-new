# Sources of Undefined Behavior in Unsafe Code

This document describes the laws that must be followed in order to
avoid [undefined behavior](Safety.md#undefined-behavior) when unsafe
constructs are used.

Early versions of this document were developed in [this
discussion](https://github.com/orgs/hylo-lang/discussions/1868).

## Definitions

- A **projection** is a `sink`, `set`, `inout` or `let` access. [^temporary] [^var]
- A **projection of type `T`** is an access to an object of type `T`.
- A projection's **lifetime** starts when it is created and ends immediately after its last use.
- Projections are **active** when they are created.
- Projections are subject to two kinds of **transition** during their lifetimes:
  - An active projection can temporarily become **inactive**.
  - The **kind** (`sink`, `set`, `inout` or `let`) of a projection can change to `let`.
- An object is **initialized** at the first completion of a `set` access on it (an `init` function is a `set` access on `self`).
- An object is **complete** when all parts[^parts] are initialized.
- An initialized or complete object becomes **incomplete** (and **uninitialized** [^init-complete]) when any part is accessed as `sink`, and returns to its prior state whenever all of its parts have returned to an initialized state.

[^temporary]: Projections can be bound to names but may also be the temporary unnamed results of expressions.
[^var]:  A `var` declaration creates a bound `sink` projection.
[^parts]: An object's parts all follow from its type declaration and do not depend on the  user-defined semantics of operations.  For example, they do not include “logical parts” that can only be reached via declared pointers, such as the elements of a dynamic array, even though its `==` operation implies that they are parts.
[^init-complete]: Every initialized object is complete, so every incomplete object is uninitialized.

## Transitions

### Initialization and deinitialization

- A `set` projection becomes an `inout` projection when the accessed object is complete.
- An `inout` projection becomes a `set` projection when the accessed object is incomplete (and must
  return to `inout` before its lifetime ends).

### Re-Projection

There are four ways to produce a new projection from a projection `p`:
- Pattern matching, e.g. `let q = p`, where `q` is produced, or `for (inout x, let y) in foo { ... }` where `x` and `y` are produced.
- Passing `p` as an argument to a function or subscript, where the corresponding parameter is produced.
- Subscripting, e.g. `p[0]`
- Member access, e.g. `p.x`

In the first two cases, the kind of the new projection is explicitly declared.  In the latter two it
is the same as the kind of `p`, except when `p` is a `set` projection and the accessed part is
initialized, in which case the new projection's kind is `inout`.

Depending on the kind of the original and new projections, the original projection may make a
temporary transition from active to inactive, or from one kind to another.

| new ⬇ \ original ➡ | **`sink`** | **`set`** | **`inout`** | **`let`** |
|--------------------|------------|-----------|-------------|-----------|
| `sink`             | inactive   | n/a       | inactive    | n/a       |
| `set`              | n/a        | inactive  | n/a         | n/a       |
| `inout`            | inactive   | n/a       | inactive    | n/a       |
| `let`              | `let`      | n/a       | `let`       | *none*    |


When pattern matching binds multiple parts at once, if any of the new bindings calls for the original binding to become inactive, it becomes inactive rather than changing its kind.

**Note:** a `sink let` declaration creates a `sink` binding on which mutation is disallowed.

The transition of a projection `p` ends when no re-projections of `p` remain, when it reverts to its
earlier kind and becomes active.

## Laws

In entirely safe code, the compiler upholds these properties:
- An active non-`set` projection of type `T` always refers to a complete object of type `T`.
- if *x* is an active `sink`, `set`, or `inout` projection of an object *y*, no other projection that includes *y* is active.

**Note:** the compiler also ensures that only active projections of complete objects are used in expressions other than those that narrow active projections of incomplete objects to their stored parts, e.g. in `x.y`, `x` may project an incomplete object.

The behavior of a program that violates either property (e.g., using pointers) is undefined.  For example:

```swift
let i = 3
let p = pointer[to: i] // i becomes inactive
let q = p.copy()       // projection of p ends; i becomes active
let j = q.unsafe[]     // UB: active projection `j` includes the object bound to active `sink` projection `i`
```

