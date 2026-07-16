# Type inference for scalar literals

This note investigates how Hylo infers the types of scalar (integer / floating-point)
literals, why context-dependent cases such as `(1 + 1) as Int32` currently fail, how other
languages solve the same problem, and what we could do about it while staying faithful to
Hylo's implicits-based generics. It records confirmed findings, an empirical experiment run
against the current compiler, a survey of prior art, and a concrete, staged design proposal.

> Status: implemented. Sections 1–7 record the investigation and design; the **Implementation**
> section below describes what was landed and how it maps onto the design. Issue #253 and the
> `(1 + 1) as T` family are fixed, and an integer literal may now be used where a float is
> expected.

## Implementation

The design of §5 was implemented in three parts. The behaviour it produces:

* `let x = 1` → `Int`, `let x = 1.5` → `Float64` (unchanged defaults).
* `Triple(a: 3, b: 4, c: 42)` where the fields are `Int32` — the literals take the parameter
  type (issue #253); likewise any literal in argument position.
* `let x: Float64 = 1`, `1 as Float64` — an integer literal builds a floating-point value.
* `(a * b) as Wide` where `a`, `b` conform to `ExpressibleByIntegerLiteral` and `infix*` widens
  to `Wide` — the operands take the operand type and the result the ascribed type, found by
  search rather than by hard-coding operator semantics.
* Two distinct conforming types satisfying an expression equally well → an ambiguity error.

Note: the standard library's `Int32`/`Int64` do not currently define arithmetic operators, so
`(1 + 1) as Int32` still fails — not for want of inference, but because `Int32` has no `infix+`.
The inference machinery is exercised by the tests using a user type that does define one.

### Mechanism

1. **Deferral (obligation generation).** `inferredType(of:in:)` for a `LiteralExpression`
   (`Typer.swift`) keeps today's behaviour when the context supplies an expected type (so
   `1 as Int32` stays a direct construction). With no expected type it constructs the literal
   against a fresh variable and records a `LiteralConstraint` on the constructed value, tying the
   two with an equality so that pinning the value (via an argument or ascription coercion) also
   resolves the constructor. The literal's type is therefore an open variable the solver can
   choose, not a frozen `Int`.

2. **`LiteralConstraint`** (`Constraint.swift`) carries the literal's type variable, its default
   type, the literal trait, and the use scope. It is trivial once the variable is a concrete
   type; `solve(literal:)` (`Solver.swift`) postpones while the variable is open and succeeds once
   it is pinned (validity of the chosen type is enforced by the ordinary `.new(<literal>:)`
   resolution).

3. **Resolution (solver, last resort).** When no fresh goal remains, `resolveStaleLiteral`
   (`Solver.swift`) picks a stale literal that no pending coercion can still pin
   (`firstUnpinnableStaleLiteral`) and resolves it by forking, reusing the same fork machinery as
   `solve(overload:)`: it tries the **default type first** and prefers it if the whole program
   type-checks; otherwise it tries the conformers of the literal's trait
   (`Typer.literalConformers`, enumerated from the givens visible at the use scope, so conformers
   imported from other modules are included) and selects the unique one that succeeds, reporting
   an **ambiguity error** if two succeed. This runs before coercion/widening defaulting so a
   defaulted literal can unblock a constraint that depends on it (e.g. a `Movable` witness).

4. **Integer-literal → float** is a standard-library change plus one lowering case: `Float32`/
   `Float64` are given built-in `ExpressibleByIntegerLiteral` conformances
   (`isBuiltin(conformanceTo:for:)` accepts float types for that trait), and
   `loweredBuiltinIntegerLiteralConversion` (`IREmitter.swift`) emits a floating-point value for a
   float target. No compiler special-casing of numeric semantics is introduced.

### Answers to §7 (from the maintainer)

* **Ambiguity policy:** report an error for now (implemented); a resolution strategy can be added
  later.
* **Conformer set:** conformers may be imported, so enumeration uses the existing
  "givens visible from a scope" query rather than a fixed list.

### Cost and limitations

* Resolving each unconstrained literal forks the solver to try candidate types. The default is
  tried first and short-circuits, so ordinary code pays one fork per literal; only an ascription
  the default cannot satisfy triggers the conformer search. An expression containing many
  mutually-unconstrained literals is quadratic in their number in the worst case (as in other
  constraint solvers); realistic code, where operators and parameters pin most operands, is not
  affected. The full test suite runs at its previous speed.
* Making `(1 + 1) as Int32` itself succeed additionally requires arithmetic operators on the
  sized integer types in the standard library, which is out of scope here.

### Tests

`Tests/CompilerTests/positive/integer-literal-argument.hylo` (#253 + argument position and the
still-defaults case), `integer-literal-as-float.hylo`, `literal-operator-result.hylo` (the widening
search), and `Tests/CompilerTests/negative/ambiguous-literal.hylo` (ambiguity).

## 1. The problem

`1 + 1` is parsed as `(1).infix+(1)` — infix operators are always methods of the LHS. During
typing each literal `1` is elaborated to `.new(integer_literal: 1)`, i.e. a call to
`T.init(integer_literal:)` for some `T is ExpressibleByIntegerLiteral`. So the whole
expression is
`.new(integer_literal: 1).infix+(.new(integer_literal: 1))`.

The user-visible symptom (all three diagnosed today):

```
let a = (1 + 1) as Int32       // error: no conversion from 'Int' to 'Int32'
let b: Int32 = 1 + 1           // error: no coercion from 'Int' to 'Int32'
let c = (1 + 1) as Int64       // error: no conversion from 'Int' to 'Int64'
```

whereas the *leaf* cases work fine:

```
let d = 1 as Int32             // ok
let e: Int32 = 1               // ok
let f = 1 as Int64             // ok
```

### 1.1 Confirmed root cause

The literal is monomorphized to a **concrete** type at *obligation-generation* time, not at
*solve* time. In `inferredType(of:in:)` for literals
(`Sources/FrontEnd/Typer/Typer.swift`, the `LiteralExpression` overload):

```swift
let qualification = context.expectedType ?? standardLibraryType(T.defaultType)   // ~line 2332
return context.withSubcontext(expectedType: qualification) { (ctx) in
  inferredType(of: c, in: &ctx)                     // c == `.new(integer_literal: 1)`
}
```

`T.defaultType` is `Int` for `IntegerLiteral`. The chosen type is baked in as the *metatype
qualifying* the `.new`, so by the time the constraint system is built, the receiver of
`infix+` is already `Int`, not a variable.

The expected type *is* propagated to a literal when the literal is itself the checked
expression — that is why `1 as Int32` works: `Conversion` typing pushes `Int32` as the
`expectedType` of its source (`inferredType(of: Conversion.ID, …)`, ~line 2162-2171), and the
literal picks it up at line 2332. But for `(1 + 1) as Int32` the expected type `Int32` is the
expected type of the **result of `infix+`**, not of its **receiver**. The receiver `1` is the
*qualification* of the `infix+` name expression, and qualifications only receive an expected
type when they are an *implicit* qualification (the `.foo` sugar):

```swift
// inferredType(of:qualifyingNameOccurringIn:) — ~line 2842
let expected = context.expectedType.flatMap { (t) in
  if program.tag(of: q) == ImplicitQualification.self {
    return program.types.demand(Metatype(inhabitant: t)).erased
  } else {
    return nil        // <- a literal receiver lands here: no expected type
  }
}
```

So the receiver literal gets no expected type, defaults to `Int` at line 2332, `infix+`
resolves on `Int`, the result is `Int`, and the outer `Int <:< Int32` widening constraint
fails.

The trace for `(1 + 1) as Int32` (`hc --trace-inference file:line`) shows the receiver is
already a concrete `Metatype<Int>` before solving begins:

```
constraints:
- (Metatype<Int>).init =:= %0            <- receiver already committed to Int
- constructor(%0) =:= %1
- %1 applied to (integer_literal: IntegerLiteral) gives %2
- (%2).infix+ =:= %3
- … (the RHS literal, also Int) …
- %3 applied to (%6) gives %7
- %7 <:< Int32
…
- solve: Int <:< Int32
  - schedule: Int =:= Int32
- solve: Int =:= Int32
  - fail
```

The defaulting is not a solver decision that can be revisited; it is a decision frozen into
the obligations.

### 1.2 Why "push the expected type down to the leaves" is not enough

The obvious heuristic — when an arithmetic expression has an expected type, push it to the
literal leaves — is both under- and over-powered:

* It special-cases the standard-library arithmetic operators (their result type equals their
  operand type). Hylo deliberately does not want the compiler to know stdlib operator
  semantics.
* It is **wrong** for total-arithmetic operators whose result is *wider* than their operands.
  For example

  ```
  extension UInt32 { fun infix*(other: UInt32) -> UInt64 { … } }
  let x = (a * b) as UInt64
  ```

  Here the operands should be `UInt32`, not `UInt64`; pushing the expected `UInt64` to the
  leaves would pick the wrong operator (or fail). The relationship between the expected type
  and the leaf type runs *through the operator's signature*, which the compiler must not
  hard-code.

The correct framing is therefore a **search**: the leaf type is an unknown, the operator
choice is an unknown, and the expected type is one more constraint that *prunes* the space —
not a value that can be assigned to the leaves directly.

## 2. Experiment: deferring the literal to a type variable

To confirm the mechanism, line 2332 was changed to defer instead of defaulting:

```swift
let qualification = context.expectedType ?? fresh().erased   // was: standardLibraryType(.int)
```

Rebuilt `hc` and re-traced `(1 + 1) as Int32`. Result (abridged):

```
constraints:
- (Metatype<%0>).init =:= %1
- constructor(%1) =:= %2
- %2 applied to (integer_literal: IntegerLiteral) gives %3
- (%3).infix+ =:= %4
- … (RHS literal %5 …) …
- %4 applied to (%8) gives %9
- %9 <:< Int32
steps:
- … everything defers …
- solve: %9 <:< Int32
  - schedule: %9 =:= Int32
- solve: %9 =:= Int32
  - assume: %9 = Int32            <- the RESULT is pinned to Int32, as desired
  - refresh: %4 applied to (%8) gives Int32
- solve: %4 applied to (%8) gives Int32
  - defer                        <- STUCK: %4 == (%0).infix+ is stale on receiver type %0
```

Two things were learned, both important:

1. **The circularity is real and localised.** When `fresh` empties, the existing
   `refreshCoercionAndWideningConstraints` machinery turns `%9 <:< Int32` into `%9 =:= Int32`,
   so the *result* type is already known to be `Int32` at the stuck point. What remains
   unknown is only the *receiver* type `%0`. Nothing propagates `Int32` backwards through
   `infix+` to `%0`, because that would require inverting an operator whose signature is not
   yet resolved. This is exactly the dependency cycle described in the problem statement.

2. **Deferral alone is insufficient — and it also breaks the easy case.** With the change,
   plain `let x = 1 + 1` (no ascription) also fails with "not enough context to infer a
   type", because we removed the default and supplied nothing to recover it. A working
   solution therefore needs *both*:
   * a **defaulting** rule for genuinely unconstrained literals (recovers `1 + 1 : Int`), and
   * a **search** over conforming types for context-constrained literals (recovers
     `(1 + 1) as Int32`).

The good news from (1): the search is heavily prunable. At the stuck point we already know
the result must be `Int32`; the only viable receiver types are conformers `C` of
`ExpressibleByIntegerLiteral` whose `infix+` returns something unifiable with `Int32`. For the
standard numerics that uniquely selects `C = Int32`. For the total-`*` example it would admit
both `UInt32` (operands `UInt32`, result `UInt64`) and — if `UInt64` also defines `*` — `UInt64`
(operands and result `UInt64`), which is a *genuine* ambiguity the programmer should resolve,
not a compiler guess.

The experiment was reverted; the repository is unchanged.

## 3. How other languages solve this

All mature systems share one recipe: **do not commit a literal to a type eagerly; represent it
as a constrained inference variable, resolve the operator as a constraint (not by concrete
receiver dispatch), let the expected type prune the space, and apply a default only to
whatever is left unconstrained.** They differ in how much is unification vs. explicit search,
and when defaulting fires.

* **Rust.** Integer literals get a *domain-restricted* inference variable `IntVar` (`{integer}`),
  held in a separate unification table from general `TyVar`s
  (`rustc_infer`/`rustc_middle::ty::InferTy`). Built-in operators bypass method probing and
  unify LHS = RHS = result, so `let x: i64 = 1 + 1` drives `i64` into both operands.
  Unresolved `IntVar`s are defaulted to `i32` at the end of function checking
  (`rustc_hir_typeck/src/fallback.rs`). When a *method* is called on an unresolved integer
  var, the prober provisionally resolves it to the default so candidates can be found — an
  explicit acknowledgement of the same "need the receiver type to resolve the method" cycle.
  Lesson: operators should not go through the ordinary "receiver type must be known first"
  path.

* **Swift** (closest engineering reference; `lib/Sema/CS*.cpp`). A literal becomes a fresh
  type variable with a `LiteralConformsTo(ExpressibleByIntegerLiteral)` constraint. Each
  literal protocol has a *default type* (`Int`), contributed as a **binding of last resort**
  (`CSBindings.cpp`). Operators are *global overload sets*: the solver builds a **disjunction**
  over all `+` overloads and searches it under the contextual type, so `(1 + 1) as Int32` is
  solved by picking the `Int32` overload, which then constrains both literal leaves to `Int32`
  — no defaulting to `Int`. Multiple solutions are ranked by a lexicographic **score**;
  `SK_NonDefaultLiteral` penalises using a non-default literal type, so `Int` wins *ties* but
  loses to a contextually-required `Int32`. "Favored" overloads (try `(Int,Int)->Int` first)
  keep the search tractable.

* **Haskell.** `1` desugars to `fromInteger 1 :: Num a => a`; `(+) :: Num a => a -> a -> a`.
  Because the operator is itself class-polymorphic, an ascription just instantiates `a` and
  reaches the leaves by ordinary instantiation — no "receiver first" problem. Residual
  ambiguity is resolved by the **defaulting rules** (`default (Integer, Double)`): pick the
  first listed type satisfying all ambiguous constraints. This is defaulting-as-search over a
  candidate list, applied only to the unsolved residue.

* **Scala.** Commits literals early and repairs with *weak conformance* / implicit numeric
  widening conversions; `given`/`using` provide implicit search but the literal's type is not
  deferred. A cautionary contrast: a good implicit-search mechanism is *not sufficient* — you
  must also keep the literal's type open.

* **Lean 4** (closest *design* to Hylo: implicits + literal type classes + bidirectional
  elaboration). `1` elaborates to `OfNat.ofNat n` with a **postponed** instance constraint
  `[OfNat ?α n]`; `+` is `HAdd.hAdd` with `[HAdd ?α ?β ?γ]`. The expected type assigns `?α`,
  then the postponed instance is discharged. Defaulting is a `@[default_instance]` (a
  lowest-priority instance) fired only on otherwise-unconstrained metavariables. This is
  essentially the recipe below, phrased in instance-search terms.

* **Agda / Idris.** Overloaded literals via `fromNat`/`fromInteger` selected by an
  instance/interface search under the expected type — direct implicit-search realisations of
  the same pattern.

* **Theory.** A literal is the canonical *checkable* term in bidirectional typing: in checking
  mode the expected type says which numeric type to be; in synthesis mode it must fall back to
  a default. The receiver-dependent-operator cycle is a mode conflict, resolved in practice by
  replacing local syntax-directed bidirectionality with *bidirectional constraint generation +
  a solver with defaulting* (Dunfield & Krishnaswami, *Bidirectional Typing*, CSUR 2021;
  Pierce & Turner, *Local Type Inference*, TOPLAS 2000; OutsideIn(X), JFP 2011).

The transferable recipe, common to all:

1. literal → fresh variable `?T` + constraint `?T is ExpressibleByIntegerLiteral`;
2. resolve the operator as a *constraint* that tolerates an unresolved receiver, solved
   jointly with the rest — not by eager receiver dispatch;
3. propagate the expected type inward as a constraint on the operator's *result*;
4. default `?T` only if still unconstrained after solving, as a lowest-priority / scored
   choice.

## 4. What Hylo already has

Encouragingly, most of the machinery this needs already exists:

* **A backtracking, forking solver with solution scoring.** `solve(overload:)`
  (`Solver.swift`) forks the solver per candidate, solves each sub-problem, and keeps the
  best-scoring solution; `formSolution` prunes branches once their score exceeds `best`
  (branch-and-bound). This is precisely the search engine a literal disjunction would reuse.
* **A dormant penalty channel.** `SolutionScore` packs `errors` and `penalties`
  (`Solver.swift`), but `current.penalties` is **never incremented** anywhere — only
  `current.errors` is. There is a ready-made, unused slot for a soft "prefer the default
  literal type" preference, the analogue of Swift's `SK_NonDefaultLiteral`.
* **Postponable constraints and a defaulting hook.** `postpone`/`stale`/`refresh` implement
  deferral; `refreshCoercionAndWideningConstraints` is exactly the "when no more inference is
  possible, pick a bound" hook — and the experiment showed it already drives the *result* of an
  ascribed arithmetic expression to the ascribed type.
* **Implicit resolution with penalties.** `summon`/`coerced` and `SummonResult.penalties`
  already rank witnesses by cost; conformer enumeration for a trait is available through the
  `givens(visibleFrom:)` machinery.
* **A distinct literal type.** `LiteralType.integer` / `.float` already exist as internal
  types (currently only used as the `Builtin.IntegerLiteral` argument type), and could carry
  the "unresolved literal" role.

What is missing is the step that turns an unresolved literal receiver into a *bounded,
prunable search over its conforming types* instead of a frozen default.

## 5. Proposed design

Keep the fast paths; add a deferred, pruned search; default only as a last resort. Concretely:

### 5.1 Defer instead of defaulting (obligation generation)

In the literal overload of `inferredType(of:in:)`, when `context.expectedType != nil`, keep
today's behaviour (bakes the expected type in — this is what makes `1 as Int32` cheap and
correct). When there is **no** expected type, emit a fresh variable `?T` for the `.new`
qualification and attach a new obligation:

```
LiteralConstraint(variable: ?T, trait: ExpressibleByIntegerLiteral, default: Int, at: site)
```

`?T` participates in unification normally, so if surrounding context pins it (e.g.
`check<Int>(1 + 1)` unifying through the argument), no search is needed.

### 5.2 A `LiteralConstraint` that defaults, then searches

Add `LiteralConstraint` to `Constraint.swift` and a `solve(literal:)` arm to the solver:

* While `?T` is still a variable and other goals are fresh, **postpone** (it may be pinned by
  unification for free).
* When the solver would otherwise be stuck (hook it into the same point as
  `refreshCoercionAndWideningConstraints`, *after* that pass so result types like the `Int32`
  above are already known):
  1. If `?T` has been unified to a concrete type, discharge trivially (verify it conforms).
  2. Else enumerate the conformers `C₁…Cₙ` of the trait visible from the use site
     (`givens(visibleFrom:)`), and **fork** exactly like `solve(overload:)`: for each `Cᵢ`,
     assume `?T := Cᵢ` and solve the remaining goals. Add a **penalty** to every branch whose
     `Cᵢ` is not the declared `default` (`Int`), via the now-live `current.penalties`.
     Branch-and-bound (`if current > best { return nil }`) prunes non-viable and worse-scoring
     branches early; the already-known result type (`= Int32`) rejects every `Cᵢ` whose
     operator result cannot unify with it.
  3. Rank surviving solutions by score. Zero penalty (`Int`) wins ties, so unconstrained
     `1 + 1` still resolves to `Int`; a contextually-forced `Int32` beats the penalised-but-
     the-only-viable branch; two equally-scored viable branches produce an *ambiguity*
     diagnostic (correct for the total-`*` example).

This special-cases *nothing* about arithmetic or stdlib operator semantics. It only knows
"an unresolved integer literal must be some `ExpressibleByIntegerLiteral` type, preferably the
default". The operator's meaning stays entirely in its ordinary signature and is exercised by
ordinary member/call constraints inside each fork.

### 5.3 Pruning tricks (keeping the search cheap)

The concern with any conformer search is combinatorial blow-up (every literal in
`1 + 2 + 3 + …` multiplying the fork count). Mitigations, in rough priority order:

* **Try the default first, prune by score.** Order `Int` first; because it scores 0, any
  branch that also succeeds but uses a non-default type is only kept if the default branch
  failed. When `Int` is viable the other conformers are dominated and pruned immediately.
* **Prune by the known result/argument types before forking.** At the stuck point the result
  is often already pinned (§2). Filter conformers to those whose relevant member's result is
  unifiable with the known type *before* spawning a fork — cheap, and usually collapses the
  set to one. (Analogue of Swift "favored overloads" + Rust's built-in-operator shortcut, but
  derived from signatures rather than hard-coded.)
* **Share one variable per literal cluster.** The two operands of `1 + 1` need not be
  independent `?T`, `?U`: the operator's parameter type ties them. Solve per *expression*, not
  per *leaf*, so a binary op forks once, not twice.
* **Only literals defer.** Non-literal receivers keep today's exact path, so the search only
  ever touches expressions that actually contain unresolved literals.

### 5.4 Alternative / fallback designs considered

* **Eager literal disjunction (simplest to build).** At each literal with no expected type,
  emit an `OverloadConstraint` over the conformers' `init(integer_literal:)`, `Int` marked
  preferred. Reuses `solve(overload:)` verbatim and needs no new constraint kind. Downsides:
  forks eagerly even when context would have pinned `?T` for free, and multiplies per leaf
  (worse combinatorics than §5.2). A reasonable first spike to validate the scoring behaviour
  before building the deferred version.
* **Result-back-propagation heuristic (rejected).** Special-case: when an ascribed arithmetic
  expression's result type is known, assume operand type = result type. Fixes `(1 + 1) as
  Int32` in one line but is exactly the stdlib-semantics special-case the design brief rules
  out, and is wrong for total-`*`.
* **Design change: make `infix+` a trait requirement resolved by an implicit, Haskell/Lean
  style.** If arithmetic operators were requirements of a `Numeric`-like trait resolved by
  implicit search rather than concrete receiver dispatch, the expected type could bind the
  witness's `Self` late (as in Haskell/Lean), dissolving the cycle without an explicit
  conformer enumeration. This is the most principled long-term option and stays within
  implicits-based generics, but it is a larger surface change (operator resolution, overload
  interaction, coherence). Worth prototyping separately; §5.1–5.3 can ship first and coexist.

## 6. Suggested staging

1. **Spike (low risk):** the eager literal disjunction (§5.4 bullet 1) restricted to integer
   literals, to validate that scoring/penalties select `Int` by default and `Int32` under
   ascription. Wire `current.penalties` for the non-default case and confirm ranking.
2. **Real implementation (§5.1–5.3):** `LiteralConstraint`, deferred solve, conformer
   enumeration with pre-fork pruning, defaulting-by-penalty. Land behind the existing test
   suite; add positive tests for `(1 + 1) as Int32`, `let x: Int32 = 1 + 1`, `1 + 1 : Int`,
   nested `1 + 2 * 3 as Int32`, and a negative test for a genuinely ambiguous total-`*` case.
3. **Evaluate the trait-based operator design (§5.4 bullet 3)** as a follow-up if the search
   proves awkward or slow in practice.

## 7. Open questions for the maintainer

* **Ambiguity policy for widening operators.** For `(a * b) as UInt64` with a total `UInt32 *
  UInt32 -> UInt64` and an ordinary `UInt64 * UInt64 -> UInt64`, should the compiler report
  ambiguity, or should some rule (narrowest viable operand? the literal default?) break the
  tie? The search naturally *surfaces* the ambiguity; the policy is a language decision.
* **How open is the conformer set?** Enumerating conformers of `ExpressibleByIntegerLiteral`
  assumes a closed(-ish) world at the use site. Is that acceptable, or must literals resolve
  against conformers introduced later / in other modules? This bounds how aggressively §5.3
  can prune.
* **Float literals and mixed expressions.** The same design applies to `ExpressibleByFloating
  PointLiteral` (default `Float64`); confirm there are no additional coercion interactions
  (e.g. integer-literal-in-float-context).
* **Should the penalty channel also express other soft preferences** (user conversions,
  optional injection) once it is wired, to match Swift's multi-component score?

## 8. Reproduction

```
# fails today
printf 'public fun main() {\n  let x = (1 + 1) as Int32\n}\n' > /tmp/r.hylo
hc --emit typed-ast /tmp/r.hylo
# -> error: no conversion from 'Int' to 'Int32'

# inspect the constraint system / solver steps
hc --emit typed-ast --trace-inference /tmp/r.hylo:2 /tmp/r.hylo
```

Key source locations (as of this note):

* Literal elaboration and the default choice — `Sources/FrontEnd/Typer/Typer.swift`,
  `inferredType<T: LiteralExpression>(of:in:)`, ~line 2302-2336 (default at ~2332).
* Why a literal *receiver* gets no expected type —
  `inferredType(of:qualifyingNameOccurringIn:)`, ~line 2842-2856.
* Ascription / `as` typing and the widening constraint — `inferredType(of: Conversion.ID, …)`,
  ~line 2158-2198.
* Call/argument obligations deliberately not using the expected type —
  `inferredType(of: Call.ID, …)`, ~line 2072-2084.
* Solver main loop, deferral, and the coercion/widening defaulting hook —
  `Sources/FrontEnd/Typer/Solver.swift`, `solution(betterThanOrEqualTo:using:)`,
  `refreshCoercionAndWideningConstraints`, `solve(overload:)`.
* Solution scoring and the dormant penalty channel — `Solver.swift`, `SolutionScore`;
  `current.penalties` is read at ~line 568 but never incremented.
* Constraint kinds — `Sources/FrontEnd/Typer/Constraint.swift`.
* `ExpressibleByIntegerLiteral` and conformers — `StandardLibrary/Sources/Core/Numbers/`
  (`ExpressibleByIntegerLiteral.hylo`, `Int.hylo`, `Int32.hylo`, `Int64.hylo`).
