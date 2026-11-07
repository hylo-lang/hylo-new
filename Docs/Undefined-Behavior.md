# Sources of Undefined Behavior in Unsafe Code

This document describes the laws that must be followed in order to
avoid [undefined behavior](Safety.md#undefined-behavior) when unsafe
constructs are used.

Early versions of this document were developed in [this
discussion](https://github.com/orgs/hylo-lang/discussions/1868).

## Definitions

- A **projection** is a `sink`, `set`, `inout` or `let` access. [^temporary] [^var]
- A **projection of type `T`** is an access to an object of type `T`.
- Projections are **active** when they are created.
- A projection can become **inactive** during its lifetime.  For example, in `x: inout T = &y`, `y` becomes inactive, and becomes active again when the lifetime of `x` ends.
- An object is **initialized** at the first completion of a `set` access on it (an `init` function is a `set` access on `self`).
- An object is **complete** when all parts[^parts] are initialized.
- An initialized or complete object becomes **incomplete** (and **uninitialized** [^init-complete]) when any part is accessed as `sink`, and returns to its prior state whenever all of its parts have returned to an initialized state.

[^temporary]: Projections can be bound to names but may also be the temporary unnamed results of expressions.
[^var]:  A `var` declaration creates a bound `sink` projection.
[^parts]: An object's parts all follow from its type declaration and do not depend on the  user-defined semantics of operations.  For example, they do not include “logical parts” that can only be reached via declared pointers, such as the elements of a dynamic array, even though its `==` operation implies that they are parts.
[^init-complete]: Every initialized object is complete, so every incomplete object is uninitialized.

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

