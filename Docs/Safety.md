## Terminology

- **Safety** in engineering is the prevention of harm through system design.

- Per [Leslie Lamport's authoritative definitions](https://lamport.azurewebsites.net/tla/safety-liveness.pdf):

  - A **behavior** is an infinite sequence of states of some system.  We will call a finite sequence of such
    states a **trace**.  (You can turn a *trace* into a *behavior* by repeating its final state forever).

  - A **property** is any predicate that applies to behaviors.  We will call these **Lamport properties**
    since *property* is already such a general term.  You can apply a *Lamport property* to a *trace* by first
    turning the *trace* into a *behavior* per the previous bullet.

  - A **safety property** is a Lamport property that once violated, cannot be “patched up.”  For example, “the
    spaceship is on its planned flight path” is not a safety property, because it could return to the planned
    flight path after having left it.  “The spaceship never left its planned flight path” is a safety property,
    because once the spaceship leaves its planned path, the property is false forever.

  - A **liveness property** is a Lamport property that can eventually be satisfied starting from
    any arbitrary trace.  For example, “nothing is printed to the console” is not
    a liveness property, because there exist traces (those that have printed to the console) that
    cannot be extended to satisfy it.  “"Hello, world" is printed to the console” is a liveness
    property, because no matter what has come before, the program can print “Hello, world”.

- An **operation** is any executable program or program fragment, from an integer addition to a whole application.

- An operation *f* **upholds** a Lamport property P iff, given a trace satisfying P whose final state satisfies
  the preconditions of *f*, applying *f* produces a trace satisfying P.  For example, this function upholds the
  safety property that nothing has ever been printed to the console, because given a trace where nothing has been
  printed, a legal application of `identity` maintains that property:

  ```swift
  /// Returns `x`.
  ///
  /// - Precondition: `x >= 0`
  func identity(_ x: Int) -> Int {
    if x < 0 { print("Precondition violated!") }
    return x
  }
  ```

  And this function upholds the liveness property that the program terminates, because given a trace where
  termination is reachable, a legal application of `identity2` maintains that property:

  ```swift
  /// Returns `x`.
  ///
  /// - Precondition: `x >= 0`
  func identity2(_ x: Int) -> Int {
    while x < 0 { /* loop forever */ }
    return x
  }
  ```

- The upholding of any Lamport property *composes*.  That is, when any two operations *f* and *g* uphold the property,
  so does *f* followed by *g*.

- An ***X* safe operation** upholds some safety property *X* **even if preconditions are violated**. [^qualification]  For example, when `a` is an array with bounds checking, `a[0] = 3` never modifies a variable not mentioned in the expression, even if `a` is empty (which violates the precondition of `a[0]`).  We might say that the operation is “expression-mutation safe.” The composition of any two *X*-safe operations is *X*-safe.

[^qualification]: note this important distinction—an operation can uphold the memory safety property but not be memory-safe by this definition, because the former depends on preconditions being satisfied but the latter does not.

- An ***X* safe language** is one where all primitive operations are *X safe*.  It follows that all non-primitive operations—and all possible programs in the language—are *X safe*. A language subset, such as “Swift programs in which no identifier contains the substring `Unsafe` or `unsafe`,” can be considered a language.

- **Memory safety** is the property that invalid memory operations such as out-of-bounds accesses and use-after-free have not occurred.

- **Type safety** is the property that an instance of one type has never been accessed as an instance of another type.

- **Thread safety** is the property that at no point in the trace can another thread cause a data race. Sometimes “thread safe” is used to mean that, additionally, deadlock has not occurred. Freedom from deadlock can also be viewed as part of a liveness property guaranteeing forward progress.

- **Data race safety** is thread safety, but explicitly excluding freedom from deadlock as a constraint.

<a name="undefined-behavior"></a>
- **Undefined behavior** is not bounded by any constraints and thus nullifies every safety property.  An operation that can have undefined behavior, or a language that includes such an operation, is never *X* safe for any *X*.

  Violations of memory safety, type safety, and data race safety have effects that can't be usefully described in terms of any portable programming language. For example, the effects of an out-of-bounds write can be understood when memory is viewed as a linear collection of bytes, but can't be described in terms of distinct variables and constants of many types, because portable languages do not specify the layout relationships among distinct stored values.  Therefore, in unsafe programming languages, these violations typically cause undefined behavior.[^java-data-race]

- A **safe operation** will never exhibit undefined behavior, even if preconditions are violated. Safety is often a consequence of type checking (you can't access `x.5` when `x` is a 2-element tuple), but sometimes runtime checks are needed, as when indexing a variable-length array. “Trapping” or otherwise stopping the program when preconditions are violated is one way to achieve safety.

- A **safe language** (such as Java or Haskell) has only safe operations, so all possible programs in the language are safe.  The distinction is important because proving a safety property of arbitrary code is tedious and sometimes very difficult, unless—as with a safe language—all code is safe by construction.

- In practice, “**memory-safe language**” is synonymous with “safe language.” Since undefined behavior invalidates all guarantees (including memory safety), a memory-safe language can have no undefined behavior and is therefore a safe language.  Because the behavior of a memory safety violation can't be defined at the language level (see the discussion after the definition of *undefined behavior*), any safe language must be memory safe.

- A **safe-by-default language** (such as Swift or Rust) contains a minority of unsafe operations that can be easily recognized by tooling and banned or flagged for extra scrutiny in code review. This arrangement provides unconditional safety in most code while allowing the direct use of primitive operations such as pointer dereferencing, without expensive validity checks.  When unsafe operations are used correctly in the implementation details of safe abstractions, the vocabulary of safe operations grows, with little compromise to overall security.  Safe-by-default languages are often casually referred to as “memory safe” despite the availability of operations that can compromise memory safety.

- The **safe subset of a safe-by-default language** is a safe language.

[^java-data-race]: Some languages, such as Java and JavaScript, define the behavior of data races, but in such a way as to be useless for most programming.
