# Prototype branches

All three branches live only in `~/specialization/hylo-new`. None was pushed, and `origin` is upstream `hylo-lang/hylo-new`.
All three are based on upstream `main` at `840aa66` ("Naming improvements from @tothambrus. (#536)").

| Branch | Head | Purpose |
|---|---|---|
| `proto/specificity-ordering` | `ee43a3c` | First prototype: specificity order for implicit resolution, plus the exploratory probes under `Notes/`. |
| `proto/overload-specificity` | `5ab4c83` | Full version: the specificity order, overload ordering (shape 1), search continuation with a step budget, 13 `specialization-*` tests, and the ambiguity diagnostic. |
| `proto/shape2-minimal` | `74d7c80` | **The candidate for upstreaming.** The smallest change that makes shape 2 work: `entails` / `isMoreSpecific` / `divergence`, a reordering in `takeSummonResults`, and the diagnostic. |

## Restoring

```sh
# in any hylo-new clone that has commit 840aa66:
git fetch Notes/specialization-archive/patches/proto-branches.bundle 'refs/heads/proto/*:refs/heads/proto/*'
# or, from the patches (SHAs will differ):
git switch -c proto/shape2-minimal 840aa66 && git am Notes/specialization-archive/patches/shape2-minimal/*.patch
```

## `proto/specificity-ordering`

```
 Notes/specialization-experiments/README.md       |  22 ++
 Notes/specialization-experiments/e1.hylo         |  18 ++
 Notes/specialization-experiments/e10.hylo        |  13 ++
 Notes/specialization-experiments/e11.hylo        |  10 +
 Notes/specialization-experiments/e12.hylo        |  12 +
 Notes/specialization-experiments/e2.hylo         |  12 +
 Notes/specialization-experiments/e3.hylo         |  15 ++
 Notes/specialization-experiments/e4.hylo         |  18 ++
 Notes/specialization-experiments/e5.hylo         |  28 +++
 Notes/specialization-experiments/e6.hylo         |  16 ++
 Notes/specialization-experiments/e7.hylo         |  11 +
 Notes/specialization-experiments/e8.hylo         |  15 ++
 Notes/specialization-experiments/e9.hylo         |  10 +
 Notes/specialization-experiments/lb.hylo         |  65 ++++++
 Notes/specialization-experiments/lb_ra_only.hylo |  56 +++++
 Notes/specialization-experiments/t1.hylo         |  14 ++
 Notes/specialization-experiments/t2.hylo         |   1 +
 Sources/FrontEnd/Typer/Typer.swift               | 154 +++++++++++-
 e2.ast                                           |  20 ++
 e3.ir                                            | 286 +++++++++++++++++++++++
 20 files changed, 794 insertions(+), 2 deletions(-)
```

### Commits (oldest first, full messages)

#### `ee43a3c` 2026-09-01 01:37 — Prototype: order implicit resolution results by specificity.

```
Implicit resolution currently returns the *smallest* derivation of a queried
witness and reports an ambiguity when several derivations tie.  That rule is
at odds with algorithm specialization: a given constrained on a finer trait
does not, in general, produce a smaller derivation than one constrained on a
coarser trait, so the specialized implementation of an algorithm either loses
or ties with the generic one.

This adds a specificity order over givens, defined by entailment between their
context clauses after matching their heads (the rule used by C++ concept
subsumption and by Siek and Lumsdaine's G), and applies it before lexical
proximity when several derivations are found.  The breadth-first search no
longer stops at the first depth that produces a result: it keeps exploring as
long as a live thread is rooted at a strictly more specific given.

Notes/specialization-experiments holds the programs used to check this.
```


## `proto/overload-specificity`

```
 .gitignore                                         |   4 +
 Notes/specialization-experiments/README.md         |  12 ++
 Notes/specialization-experiments/bench.hylo        |   6 +
 Sources/FrontEnd/Diagnostic.swift                  |  21 +-
 Sources/FrontEnd/Typer/Solver.swift                |   2 +-
 Sources/FrontEnd/Typer/Typer.swift                 | 232 ++++++++++++++++++++-
 ...zation-incomparable-givens.diagnostics.expected |  21 ++
 .../specialization-incomparable-givens.hylo        |  31 +++
 ...ation-underivable-equality.diagnostics.expected |   3 +
 .../specialization-underivable-equality.hylo       |  33 +++
 .../positive/specialization-blanket-head.hylo      |  29 +++
 .../positive/specialization-concrete-type.hylo     |  40 ++++
 .../specialization-context-sensitivity.hylo        |  36 ++++
 .../positive/specialization-deeper-derivation.hylo |  32 +++
 .../positive/specialization-lifting-given.hylo     |  33 +++
 .../positive/specialization-local-override.hylo    |  30 +++
 .../positive/specialization-overload.hylo          |  32 +++
 .../positive/specialization-own-conformance.hylo   |  28 +++
 .../positive/specialization-refinement-chain.hylo  |  28 +++
 .../positive/specialization-refinement.hylo        |  33 +++
 .../positive/specialization-witness-passing.hylo   |  27 +++
 .../specialization-witness-passing.raw-ir.expected |  17 ++
 22 files changed, 723 insertions(+), 7 deletions(-)
```

### Commits (oldest first, full messages)

#### `ee43a3c` 2026-09-01 01:37 — Prototype: order implicit resolution results by specificity.

```
Implicit resolution currently returns the *smallest* derivation of a queried
witness and reports an ambiguity when several derivations tie.  That rule is
at odds with algorithm specialization: a given constrained on a finer trait
does not, in general, produce a smaller derivation than one constrained on a
coarser trait, so the specialized implementation of an algorithm either loses
or ties with the generic one.

This adds a specificity order over givens, defined by entailment between their
context clauses after matching their heads (the rule used by C++ concept
subsumption and by Siek and Lumsdaine's G), and applies it before lexical
proximity when several derivations are found.  The breadth-first search no
longer stops at the first depth that produces a result: it keeps exploring as
long as a live thread is rooted at a strictly more specific given.

Notes/specialization-experiments holds the programs used to check this.
```

#### `dc6f1c9` 2026-09-01 01:42 — Prototype: order function overloads by constraint specificity.

```
Two functions that differ only in their context clauses are currently
reported as an ambiguous use.  This ranks them with the same specificity
order used for givens, so a call whose arguments satisfy the finer
constraints selects the more constrained overload -- concept-based
overloading in the sense of Siek and Lumsdaine's G.

As in G, the choice is still made from the static constraints of the call
site: a generic caller constrained on the coarser trait binds the coarser
overload (Notes/specialization-experiments/e13.hylo).
```

#### `7598a6e` 2026-09-01 09:31 — Add probes for concrete-head and associated-type-equality specificity.

```
e14 covers the whole chain named in the request -- a given for Arr<T> wins
over one constrained on RandomAccess, which wins over one constrained on
Bidirectional.

e15 and e16 record a limit of the search continuation.  Keeping the
breadth-first search alive past its first success makes every improvable
query behave like an exhausting one, and an exhausting query over the
built-in equality givens does not terminate -- e16 shows that divergence
already exists on main for a search that simply fails.  The specificity
*filter* alone is unaffected; only the continuation regresses here.
```

#### `3ca2a24` 2026-09-01 11:13 — Order function overloads by their parameters, not their whole type.

```
The specificity check matched the two declarations' heads as a whole, so
two overloads of an algorithm were ordered only when their return types
also happened to agree.  Compare the inputs instead -- style, labels,
passing conventions and parameter types -- and ignore the output, which
is the relation Siek and Lumsdaine define for G: g is callable from f if
f's parameters can be forwarded to it and f's constraints imply g's.

Without this, 'lower_bound(a)' with one overload returning Linear and the
other Binary stayed ambiguous.
```

#### `b25e4e3` 2026-09-01 11:14 — Turn the specialization experiments into compiler tests.

```
The exploratory programs under Notes/ are replaced by twelve test cases
named specialization-*, each carrying a header comment stating what the
program sets up, which implementation is selected, and why.

They assert the selection through a type member of the algorithm trait:
each implementation binds 'Selected' to a distinct marker type, and the
tests ascribe the expected one.  Selecting a type member forces implicit
resolution to commit to a single witness and cannot be steered by the
expected type, so a wrong selection is a type error rather than a silent
pass.  specialization-witness-passing instead pins the body of 'main' in
the lowered IR, because that is where the property it covers -- a generic
client receiving the specialized witness from its caller -- is observable.

Seven of them fail on main and so guard the new behaviour; the other five
pin selections the compiler already made, for reasons the comments give.

Two programs stay under Notes/ because they hang the compiler rather than
fail it, and so cannot be test cases.  e16 hangs on main as well: a search
over the built-in equality givens that cannot succeed does not terminate
today, which is why the first-success cutoff cannot simply be removed.
```

#### `a881b08` 2026-09-01 11:25 — Remove compiler output accidentally committed at the repository root.

```
```

#### `5ab4c83` 2026-09-01 12:17 — Bound the implicit search, and rank as the declarative rule prescribes.

```
Three fixes to the specificity order.

A search that cannot succeed did not terminate in reasonable time.  Once
the built-in reflexivity, symmetry and transitivity givens are in scope,
the number of live threads multiplies with the depth of the search: an
unsatisfiable equality reaches ~800k threads by depth nine even though
maxImplicitDepth bounds the depth at ten.  This was already reachable on
an unmodified compiler; keeping the search alive past its first success
merely made it easy to hit.  Threads are now also bounded by a budget on
the number of steps.  Resolving a witness in a well-formed program takes
a few hundred; the largest search in the test suite takes seventeen
thousand, so the budget is set at ten thousand steps per level, which the
loop may overshoot by one level's worth of work.

The condition for continuing the search was too strong.  It kept going
only while a live thread was rooted at a given more specific than *every*
incumbent, which quietly dropped incomparable roots -- exactly the ones
that should either win on lexical distance or make the query ambiguous.
It now keeps going while a root is not dominated by an incumbent, and the
ranking runs the full three-way order from the specification: specificity,
then lexical distance, then derivation size.

Ambiguity is reported with the candidates that survived, and with a note
saying that neither is more specific than the other -- which is the actual
reason no choice was made.

Also: entailment is memoized per scope, and refuses declarations that do
not form a scope of their own, since deriving one given's requirements
under another's assumptions is done by summoning them in its scope.

Notes: the penalties counter does conflate lexical distance with the shape
of a derivation, because assumed givens are grouped ahead of the visible
ones and so shift them.  Separating the two breaks two existing tests that
rely on an assumption outranking a given in an enclosing scope, and buys
nothing here: specificity has to be consulted before lexical distance
either way, which putting lexical distance first demonstrably breaks.  The
conflation is left in place, with a comment.
```


## `proto/shape2-minimal`

```
 .gitignore                                         |   4 +
 Notes/specialization-experiments/README.md         |  12 +++
 Notes/specialization-experiments/bench.hylo        |   6 ++
 Sources/FrontEnd/Diagnostic.swift                  |  21 +++-
 Sources/FrontEnd/Typer/Typer.swift                 | 119 ++++++++++++++++++++-
 ...zation-incomparable-givens.diagnostics.expected |  21 ++++
 .../specialization-incomparable-givens.hylo        |  31 ++++++
 ...ation-underivable-equality.diagnostics.expected |   3 +
 .../specialization-underivable-equality.hylo       |  33 ++++++
 .../positive/specialization-blanket-head.hylo      |  29 +++++
 .../positive/specialization-concrete-type.hylo     |  41 +++++++
 .../specialization-context-sensitivity.hylo        |  36 +++++++
 .../positive/specialization-lifting-given.hylo     |  33 ++++++
 .../positive/specialization-local-override.hylo    |  30 ++++++
 .../positive/specialization-own-conformance.hylo   |  28 +++++
 .../positive/specialization-refinement-chain.hylo  |  28 +++++
 .../positive/specialization-refinement.hylo        |  33 ++++++
 .../positive/specialization-witness-passing.hylo   |  27 +++++
 .../specialization-witness-passing.raw-ir.expected |  17 +++
 19 files changed, 547 insertions(+), 5 deletions(-)
```

### Commits (oldest first, full messages)

#### `7babb16` 2026-09-01 01:37 — Shape-2 core: the smallest change that specializes algorithms.

```
An algorithm written as its own trait, with one given per implementation
and clients constrained on the trait, needs only that overlapping givens
be *ordered*.  It does not need the search to look past its first success,
and it does not need overload resolution to change.  This branch is that
core, measured against the fuller one:

  * entails / isMoreSpecific / divergence, and a three-line reordering of
    the results of takeSummonResults;
  * the ambiguity diagnostic, which is independent but cheap.

Dropped, with the tests that cover them:

  * the search continuation and its work budget.  They buy the case where
    the specialized given's derivation is *deeper* than the generic one,
    which shape 2 does not produce: a type conforming to both the coarse
    and the fine trait yields two derivations of the same size, and the
    filter alone separates them.  They also account for the whole of the
    compile-time cost.
  * ordering function overloads, which is shape 1.
  * matchingHeads, which only matters when the heads being compared are
    arrows -- that is, only for overloads.

divergence is *not* droppable: without it the witness a client passes into
a generic function is not ordered at all, which is the case shape 2 exists
for.

Cost on a full standard-library typing run: 4.15-4.24 s against a
4.14-4.22 s baseline, where the fuller branch costs 4.32-4.38 s.

Bound the implicit search, and rank as the declarative rule prescribes.

Three fixes to the specificity order.

A search that cannot succeed did not terminate in reasonable time.  Once
the built-in reflexivity, symmetry and transitivity givens are in scope,
the number of live threads multiplies with the depth of the search: an
unsatisfiable equality reaches ~800k threads by depth nine even though
maxImplicitDepth bounds the depth at ten.  This was already reachable on
an unmodified compiler; keeping the search alive past its first success
merely made it easy to hit.  Threads are now also bounded by a budget on
the number of steps.  Resolving a witness in a well-formed program takes
a few hundred; the largest search in the test suite takes seventeen
thousand, so the budget is set at ten thousand steps per level, which the
loop may overshoot by one level's worth of work.

The condition for continuing the search was too strong.  It kept going
only while a live thread was rooted at a given more specific than *every*
incumbent, which quietly dropped incomparable roots -- exactly the ones
that should either win on lexical distance or make the query ambiguous.
It now keeps going while a root is not dominated by an incumbent, and the
ranking runs the full three-way order from the specification: specificity,
then lexical distance, then derivation size.

Ambiguity is reported with the candidates that survived, and with a note
saying that neither is more specific than the other -- which is the actual
reason no choice was made.

Also: entailment is memoized per scope, and refuses declarations that do
not form a scope of their own, since deriving one given's requirements
under another's assumptions is done by summoning them in its scope.

Notes: the penalties counter does conflate lexical distance with the shape
of a derivation, because assumed givens are grouped ahead of the visible
ones and so shift them.  Separating the two breaks two existing tests that
rely on an assumption outranking a given in an enclosing scope, and buys
nothing here: specificity has to be consulted before lexical distance
either way, which putting lexical distance first demonstrably breaks.  The
conflation is left in place, with a comment.

Remove compiler output accidentally committed at the repository root.

Turn the specialization experiments into compiler tests.

The exploratory programs under Notes/ are replaced by twelve test cases
named specialization-*, each carrying a header comment stating what the
program sets up, which implementation is selected, and why.

They assert the selection through a type member of the algorithm trait:
each implementation binds 'Selected' to a distinct marker type, and the
tests ascribe the expected one.  Selecting a type member forces implicit
resolution to commit to a single witness and cannot be steered by the
expected type, so a wrong selection is a type error rather than a silent
pass.  specialization-witness-passing instead pins the body of 'main' in
the lowered IR, because that is where the property it covers -- a generic
client receiving the specialized witness from its caller -- is observable.

Seven of them fail on main and so guard the new behaviour; the other five
pin selections the compiler already made, for reasons the comments give.

Two programs stay under Notes/ because they hang the compiler rather than
fail it, and so cannot be test cases.  e16 hangs on main as well: a search
over the built-in equality givens that cannot succeed does not terminate
today, which is why the first-success cutoff cannot simply be removed.

Order function overloads by their parameters, not their whole type.

The specificity check matched the two declarations' heads as a whole, so
two overloads of an algorithm were ordered only when their return types
also happened to agree.  Compare the inputs instead -- style, labels,
passing conventions and parameter types -- and ignore the output, which
is the relation Siek and Lumsdaine define for G: g is callable from f if
f's parameters can be forwarded to it and f's constraints imply g's.

Without this, 'lower_bound(a)' with one overload returning Linear and the
other Binary stayed ambiguous.

Add probes for concrete-head and associated-type-equality specificity.

e14 covers the whole chain named in the request -- a given for Arr<T> wins
over one constrained on RandomAccess, which wins over one constrained on
Bidirectional.

e15 and e16 record a limit of the search continuation.  Keeping the
breadth-first search alive past its first success makes every improvable
query behave like an exhausting one, and an exhausting query over the
built-in equality givens does not terminate -- e16 shows that divergence
already exists on main for a search that simply fails.  The specificity
*filter* alone is unaffected; only the continuation regresses here.

Prototype: order function overloads by constraint specificity.

Two functions that differ only in their context clauses are currently
reported as an ambiguous use.  This ranks them with the same specificity
order used for givens, so a call whose arguments satisfy the finer
constraints selects the more constrained overload -- concept-based
overloading in the sense of Siek and Lumsdaine's G.

As in G, the choice is still made from the static constraints of the call
site: a generic caller constrained on the coarser trait binds the coarser
overload (Notes/specialization-experiments/e13.hylo).

Prototype: order implicit resolution results by specificity.

Implicit resolution currently returns the *smallest* derivation of a queried
witness and reports an ambiguity when several derivations tie.  That rule is
at odds with algorithm specialization: a given constrained on a finer trait
does not, in general, produce a smaller derivation than one constrained on a
coarser trait, so the specialized implementation of an algorithm either loses
or ties with the generic one.

This adds a specificity order over givens, defined by entailment between their
context clauses after matching their heads (the rule used by C++ concept
subsumption and by Siek and Lumsdaine's G), and applies it before lexical
proximity when several derivations are found.  The breadth-first search no
longer stops at the first depth that produces a result: it keeps exploring as
long as a live thread is rooted at a strictly more specific given.

Notes/specialization-experiments holds the programs used to check this.
```

#### `74d7c80` 2026-09-03 15:54 — remove comment

```
```


## Tests added (in `Tests/CompilerTests/`)

Run them with `swift test --filter specialization`. Every test starts with a comment that says what it sets up, which implementation gets selected, and why. Most tests check the selection with a `Selected` type member, so a wrong pick fails to type-check. `specialization-witness-passing` checks the lowered IR of `main` instead.

- `Tests/CompilerTests/negative/specialization-incomparable-givens.diagnostics.expected`
- `Tests/CompilerTests/negative/specialization-incomparable-givens.hylo`
- `Tests/CompilerTests/negative/specialization-underivable-equality.diagnostics.expected`
- `Tests/CompilerTests/negative/specialization-underivable-equality.hylo`
- `Tests/CompilerTests/positive/specialization-blanket-head.hylo`
- `Tests/CompilerTests/positive/specialization-concrete-type.hylo`
- `Tests/CompilerTests/positive/specialization-context-sensitivity.hylo`
- `Tests/CompilerTests/positive/specialization-deeper-derivation.hylo`
- `Tests/CompilerTests/positive/specialization-lifting-given.hylo`
- `Tests/CompilerTests/positive/specialization-local-override.hylo`
- `Tests/CompilerTests/positive/specialization-overload.hylo`
- `Tests/CompilerTests/positive/specialization-own-conformance.hylo`
- `Tests/CompilerTests/positive/specialization-refinement-chain.hylo`
- `Tests/CompilerTests/positive/specialization-refinement.hylo`
- `Tests/CompilerTests/positive/specialization-witness-passing.hylo`
- `Tests/CompilerTests/positive/specialization-witness-passing.raw-ir.expected`

Not on shape2-minimal: `specialization-deeper-derivation` (needs the search continuation) and `specialization-overload` (shape 1).
