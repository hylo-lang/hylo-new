# Learning the type checker (through the scalar-literal work)

This is a self-study curriculum for the concepts behind Hylo's type checker, using the
scalar-literal inference change (`Docs/LiteralInference.md`) as the running example and final
destination. Work through it and you will be able to read, extend, and defend that change — and
the type checker generally — with confidence.

It is written to be *done*, not just read. Every module has something to run, something to
predict, something to break, and something to build. Budget real time at the keyboard.

---

## Part 0 — Methodology: how to actually learn this

Compiler internals resist passive reading. Use this loop for every concept:

1. **Name the question.** Write, in one sentence, what you don't yet understand ("how does an
   argument get its expected type?"). A vague goal produces vague learning.
2. **Read the smallest surface.** Find the one function that answers it. Read *only* that and its
   immediate callees. Resist reading the whole file — you will drown. The concept map (Part 1)
   points you at the right function for each idea.
3. **Form a falsifiable prediction.** Before running anything, write down what you expect. "The
   receiver of `infix+` will be typed `Int` before the solver runs." A prediction you can be
   *wrong* about is the only kind that teaches.
4. **Probe.** Run the compiler and check. The tools (below) make the machine's internal state
   visible. If you were right, you understood it. If you were wrong, you just found the exact
   edge of your model — the most valuable moment. Do not move on until the surprise is explained.
5. **Break it on purpose.** Change one line, predict the new behaviour, rebuild, confirm. Breakage
   with a correct prediction is proof of understanding; breakage with a wrong prediction is a
   second lesson. Revert with `git checkout`.
6. **Rebuild it.** The capstone (Part 3) is re-deriving the literal change from a clean tree. You
   don't understand a mechanism until you can reconstruct it.

Two rules that keep this honest:

- **Predict before you run, every time.** The urge to just run-and-read skips the learning.
- **One variable at a time.** Change one thing, observe, understand, then the next. Compilers have
  enough moving parts that multi-variable experiments teach nothing.

### Your instruments

You are debugging a type checker; these make its hidden state observable. (See
`Docs/LiteralInference.md` §8 and the `hc-stale-stdlib-cache` note.)

```bash
# Build the compiler once; rebuild after every source edit.
swift build --product hc

# The single most important flag: dump the constraint system AND every solver step
# for the declaration on a given line, to stdout. This is your microscope.
.build/debug/hc --no-caching --emit typed-ast --trace-inference file.hylo:LINE file.hylo

# Just the typed AST (types the program, stops before IR). NOTE: the tree is written to a
# file next to the input, named <basename>.ast — not stdout. Errors still go to stderr.
# e.g. for `let x = 1` the .ast shows:  let x: let Int = .new(integer_literal: 1)
.build/debug/hc --no-caching --emit typed-ast file.hylo   # then read file.ast

# The lowered SSA IR (written to <basename>.ir).
.build/debug/hc --no-caching --emit raw-ir file.hylo      # then read file.ir

# ALWAYS pass --no-caching to hc. Without it, hc loads a stale precompiled standard
# library and lies to you. The test harness compiles std from source, so it disagrees.

# Ground truth for whether a program *should* compile: the test suite.
swift test --filter 'test_positive_<name>$'
```

The `--trace-inference` output has two parts you must learn to read fluently:

- **`constraints:`** — the list of formulae the checker generated for the expression, *before*
  solving. Types like `%6ub` are unification variables. This is the checker's "to-do list".
- **`steps:`** — the solver working the list: `solve:` (picking a goal), `assume:` (assigning a
  variable), `schedule:` (adding a sub-goal), `defer` (postponing), `refresh:` (re-waking a
  postponed goal), `ok`/`fail`. Indentation marks recursive/forked solving.

Learning to *predict* a trace, constraint by constraint, is the concrete measure of mastery in
this codebase. Every module below asks you to.

---

## Part 1 — The concept map

The ideas this change touches, in dependency order. Each is a module in Part 2. "Anchor" is the
function to read first; line numbers drift, so search by name.

| # | Concept | Anchor (file · function) | Why it matters here |
|---|---------|--------------------------|---------------------|
| 1 | Compiler pipeline & bidirectional typing | `Typer.swift` · `InferenceContext`, `withSubcontext`, `discharge` | "expected type" (checking vs synthesis) is the whole game for literals |
| 2 | Type variables & unification | `Solver.swift` · `solve(equality:)`; `TypeStore.swift` · `unifiable`; `SubstitutionTable.swift` | a deferred literal *is* a unification variable |
| 3 | The worklist solver | `Solver.swift` · `solution(betterThanOrEqualTo:)`, `postpone`, `refresh` | "stuck vs pinnable", defaulting-when-stuck live here |
| 4 | Elaboration / desugaring | `Typer.swift` · `inferredType(of:in:)` for `LiteralExpression` | `1+1` → `.infix+`, `1` → `.new(integer_literal:)` |
| 5 | Name & member resolution | `Typer.swift` · `resolve`, `Solver.swift` · `solve(member:)` | resolving `infix+` needs the receiver type — the crux |
| 6 | Calls, coercions, widening | `Solver.swift` · `solve(call:)`, `matches`, `solve(coercion:)`, `solve(widening:)` | how the argument/ascription type reaches a literal |
| 7 | Traits, givens, implicit search | `Typer.swift` · `givens(visibleFrom:)`, `summon`, `coerced`; `literalConformers` | `ExpressibleByIntegerLiteral`; enumerating conformers |
| 8 | Overload resolution as search | `Solver.swift` · `solve(overload:)`, `SolutionScore` | the fork/score machinery my search reuses |
| 9 | Defaulting & literals (the change) | `Constraint.swift` · `LiteralConstraint`; `Solver.swift` · `resolveStaleLiteral` | everything above, combined |
| 10 | IR lowering of literals | `IREmitter.swift` · `loweredBuiltinIntegerLiteralConversion` | where a chosen type becomes machine bits (the int→float part) |

Two pieces of external theory to read once, early, and return to:

- **Bidirectional typing** — Dunfield & Krishnaswami, *Bidirectional Typing* (ACM CSUR 2021,
  arxiv.org/abs/1908.05839). Read the intro and the parts on literals. This is the vocabulary
  ("checking mode", "synthesis mode") for module 1.
- **Type inference with class constraints + defaulting** — skim the Haskell 2010 Report §4.3.4
  (defaulting rules) and the Rust reference on integer literal fallback. These are the two
  clearest real-world versions of what module 9 does. `Docs/LiteralInference.md` §3 summarises
  how Rust/Swift/Haskell/Lean each solve it.

---

## Part 2 — The learning path

Each module: **Read → Probe → Break → Build → Checkpoint.** Do them in order; later modules assume
earlier ones. A module is finished only when you can answer its checkpoint questions *out loud*,
from memory, without the code open.

### Module 1 — The pipeline and bidirectional typing

**Read.** `check(_:)` for a source file down to `discharge(_:relatedTo:)` in `Typer.swift`; then
`InferenceContext` and `withSubcontext`. Notice that type checking a declaration = generate
obligations (an `Obligations`), hand them to a `Solver`, `commit` the resulting substitutions
back onto the AST. Notice `InferenceContext.expectedType`: the *checking-mode* type pushed down
from context. Where it is `nil`, the checker is in *synthesis mode* (infer bottom-up).

**Probe.** Predict, then run `--trace-inference` on `let x: Int = 1` vs `let x = 1`. Which one
gives the `.new`'s qualification a concrete `Int` immediately, and which introduces a variable?
Tie each back to `expectedType` being present or `nil`.

**Break.** In the literal `inferredType`, temporarily force the deferral branch even when
`expectedType` is present. Predict what `let x: Int32 = 1` now does. Rebuild, confirm, revert.

**Build.** Add a comment block above `withSubcontext` in your own words: what does "sub-context"
mean, and why is `expectedType` reset to `nil` by default when entering one?

**Checkpoint.** Define checking vs synthesis mode. Point to the exact field that represents
"expected type". Explain why arguments to a call are inferred in a sub-context with no expected
type (hint: `solve(call:)` and overloading — you'll confirm this in module 6).

### Module 2 — Type variables and unification

**Read.** `TypeVariable.swift` (tiny). `EqualityConstraint` in `Constraint.swift`.
`solve(equality:)` in `Solver.swift` and `unifiable` in `TypeStore.swift`. `SubstitutionTable`.

**Probe.** In a trace, find an `assume: %N = SomeType` line. That is unification assigning a
variable. Find `=:=` in the `constraints:` block — that's an `EqualityConstraint`. Predict what
`solve(equality:)` does when both sides are variables vs one side concrete.

**Break.** Make `solve(equality:)` log the assignment it makes (a `print`), rebuild, and watch the
substitutions accumulate on a `let x = 1 + 1`. Revert.

**Build.** Exercise E1 (Part 4): a from-scratch union-find unifier for a toy type grammar, on
paper or in a scratch Swift file. You must be able to hand-simulate unification.

**Checkpoint.** What is a unification variable? What does the substitution table map, and why is
it "monotonically extended" (never retracted)? What happens when you `assume` a variable that
other constraints mention (hint: `refresh`)?

### Module 3 — The worklist solver

**Read.** `solution(betterThanOrEqualTo:using:)` — the main loop — slowly. Identify `fresh`,
`stale`, `goals`, `outcomes`. Read `postpone` (moves a goal to `stale`), `refresh` (wakes stale
goals whose variables changed), and `refreshCoercionAndWideningConstraints` (the "we're stuck,
pick a bound" step). This loop is the heart of the checker.

**Probe.** On `let x = 1 + 1`, watch the trace: which goals `defer` first and why? What event
causes a `refresh:`? Confirm your module-2 answer about assignment waking stale goals.

**Break.** Comment out the `if fresh.isEmpty { ... }` stuck-handling block entirely. Predict what
`let x = 1` reports now. Rebuild, confirm ("not enough context"), revert. This shows you *why*
last-resort defaulting exists.

**Build.** Exercise E2: add a solver goal counter and print, at the end of a discharge, how many
goals were created vs postponed. A small, safe way to feel the loop's shape.

**Checkpoint.** Draw the state machine of a single goal: fresh → (solve) → success / fail /
postpone(stale) → (refresh) → fresh. When does the loop terminate, and what happens to goals
still stale at the end?

### Module 4 — Elaboration and desugaring

**Read.** The `LiteralExpression` overload of `inferredType(of:in:)` — the literal-rewriting code
(`.new(<label>: e)`). Then find `parseInfixExpression` in `Parser.swift` to see `1 + 1` become
`(1).infix+(1)` syntactically. Elaboration = replacing sugar with a canonical, fully-explicit form
the rest of the checker understands.

**Probe.** `--emit typed-ast` on `let x = 1` and read the tree: the `1` is gone, replaced by a
`Call` to `.new`. Predict the label and the callee before you look.

**Break.** Change the elaboration to use the wrong constructor label (e.g. `"x"`), predict the
diagnostic ("no candidate matches / incompatible labels"), rebuild, confirm, revert.

**Build.** Exercise E7 (parser): add a *character* literal `'a'` that elaborates to a
`.new(unicode_scalar_literal:)` call, threading it through `LiteralExpression`. Even if you don't
finish lowering, getting it to type-check teaches the whole front-of-pipeline path.

**Checkpoint.** Why elaborate a literal into a constructor call at all, instead of giving it a
type directly? (Hint: uniformity — the literal now goes through the *same* member/call/coercion
machinery as everything else, so context propagation is free.)

### Module 5 — Name and member resolution

**Read.** `resolve(_:in:)` for a `NameExpression` in `Typer.swift`: the qualified case, and how it
handles a qualification that is still a *variable* (it postpones via a `MemberConstraint`). Then
`solve(member:)` in `Solver.swift`. Then `inferredType(of:qualifyingNameOccurringIn:)` — the
function that decides whether a qualification gets an expected type.

**Probe.** This is the crux of the whole change. On `(1 + 1) as Int32`, trace and find the
`(...).infix+ =:= %N` constraint. Ask: what is the type of the receiver at that point, and *why*
doesn't the `Int32` from the ascription reach it? Read the `flatMap` in
`inferredType(of:qualifyingNameOccurringIn:)` and explain the `ImplicitQualification` check.

**Break.** Temporarily make that function hand the expected type to *every* qualification, not just
implicit ones. Predict what `array.count` (a member on a non-literal) would do wrong. (You may not
have `Array`; reason it through and/or test with any `x.member`.) Revert. This is exactly the
"naive push-down" that `Docs/LiteralInference.md` §1.2 rejects.

**Build.** Exercise E3: make `solve(member:)` emit a *note* listing the candidate members it found
when resolution fails, to see name resolution's candidate sets.

**Checkpoint.** Why can't `infix+` be resolved before the receiver's type is known? Why is that a
*mode conflict* in bidirectional terms (module 1)? This is the sentence the entire change exists
to resolve.

### Module 6 — Calls, coercions, and widening

**Read.** `solve(call:)` and its helper `matches` in `Solver.swift`: see it build a
`CoercionConstraint` per argument (argument type → parameter type). Then `solve(coercion:)` and
`solve(widening:)`, and how `refreshCoercionAndWideningConstraints` turns a stuck coercion into an
equality (picking a bound). `CoercionConstraint`/`WideningConstraint` in `Constraint.swift`.

**Probe.** On `g(3)` where `fun g(x: Int32)`: trace and watch the argument coercion `%N ~:~ Int32`
be postponed, then simplified to `%N =:= Int32`, pinning the literal. *This* is how #253 gets
fixed by deferral alone — no search needed. Contrast with `(1 + 1) as Int32` where the pin has to
come *through* the operator.

**Break.** In `matches`, drop the argument coercion (return no sub-goals). Predict what breaks
(argument types no longer checked). Revert.

**Build.** Exercise E4: implement a compiler-known widening `given`-style coercion `Int ~> Int64`
and a test `let x: Int64 = someInt` that exercises `solve(widening:)`. (Study how `coerced`
summons a coercion witness first.)

**Checkpoint.** Distinguish `EqualityConstraint`, `CoercionConstraint`, `WideningConstraint`: when
is each generated, and what does "simplify a coercion to an equality" mean? Why does the solver
wait until it's stuck to do that simplification?

### Module 7 — Traits, givens, and implicit search

**Read.** A numeric type in `StandardLibrary/.../Numbers/` (e.g. `Int.hylo`): `given Int is
ExpressibleByIntegerLiteral { /* built-in */ }`, and `given Int is AdditiveArithmetic { fun
infix+ ... }`. Then in `Typer.swift`: `givens(visibleFrom:)`, `isBuiltin(conformanceTo:for:)`,
`summon`, `coerced`, and finally the new `literalConformers`. Implicit search = "find a witness /
conformance by searching the givens in scope", the same idea as Scala implicits / Rust trait
resolution.

**Probe.** Add `print(program.show(...))` inside `literalConformers` (or read the reasoning in
`Docs/LiteralInference.md`) and confirm which types it returns for `ExpressibleByIntegerLiteral`.
Predict the list *before* running (which stdlib types have that given?). Remove the print.

**Break.** Comment out `public given Int32 is ExpressibleByIntegerLiteral` in the stdlib. Predict
what `let x: Int32 = 1` now reports. Rebuild (needs `--no-caching`!), confirm, revert.

**Build.** Exercise E5: the int→float feature, re-derived. Remove your Float32/64 changes from the
working tree, then re-add them from scratch: the stdlib `given`s, the `isBuiltin` gate, and the
`IREmitter` case — proving you can wire a new built-in conformance end to end.

**Checkpoint.** What is a `given`? How does the checker find "all types conforming to trait P
visible here", and why must it be a *search over scope* rather than a fixed list (hint: imported
conformers)? What does `summon` return and what are its penalties for?

### Module 8 — Overload resolution as backtracking search

**Read.** `solve(overload:)` in `Solver.swift` in full. See `Self(forking: me)`, the per-candidate
recursive `solution(...)`, and how results are scored. Then `SolutionScore` (errors packed above
penalties) and the branch-and-bound `if current > best { return nil }`. This is the search engine.

**Probe.** Write a tiny overloaded function (`fun f(_ x: A)` / `fun f(_ x: B)`) and a call that is
ambiguous; trace and watch the fork, the two candidate solves, and the scoring/ambiguity verdict.
Predict which candidate "wins" and why.

**Break.** Note that `current.penalties` is *never incremented* in the solver today (grep it).
Add `me.current.penalties += 1` somewhere reachable and watch a previously-unambiguous overload
choice shift. Understand that the penalty channel is a dormant "soft preference" slot. Revert.

**Build.** Exercise E6: nothing new to write yet — instead, on paper, write the score
`(errors, penalties)` for each branch of `(1 + 1) as Int32` using a user type with `infix+` (see
`Tests/.../literal-operator-result.hylo`). This is the exact reasoning `resolveStaleLiteral`
automates.

**Checkpoint.** How does forking give the solver backtracking? Why do errors dominate penalties in
the score? What is the pruning invariant that makes branch-and-bound correct?

### Module 9 — Defaulting and literals (the change itself)

Now assemble everything. **Read**, in this order:

1. `LiteralConstraint` in `Constraint.swift` — the new goal: a literal's type variable, its
   default, its trait, its scope.
2. The deferral in `inferredType(of:in:)` — fresh variable + `EqualityConstraint` tying qualifier
   to value + `LiteralConstraint`. Re-read module 1's checkpoint about why the equality is needed.
3. `solve(literal:)` — postpone while open, succeed when pinned.
4. `resolveStaleLiteral` + `firstUnpinnableStaleLiteral` + `solution(assigning:toLiteral:)` — the
   last-resort search: default first, else conformers, ambiguity → error.
5. The loop change: `resolveStaleLiteral` runs *before* coercion/widening defaulting, and only
   for literals no coercion can still pin.

**Probe.** Predict, then trace, all of: `let x = 1` (default), `g(3)` (pinned by coercion, no
search), `(2 * 3) as Wide` with a user widening type (search finds the conformer), and the
negative ambiguity test. For each, say *which mechanism* resolved the literal (default? coercion
pin? conformer search? ambiguity?).

**Break — the instructive regressions.** Reproduce, then re-fix, the two real bugs from the
change's history (they are the best teachers):
- Attach the `LiteralConstraint` to the *qualification* variable instead of the *value* (drop the
  `EqualityConstraint(v, t)`). Predict, then observe, why an argument literal defaults to `Int`
  and then conflicts with `Int32` (`Docs/LiteralInference.md` §2 / the "qualification vs value"
  bug).
- Move `defaultStaleLiterals`/`resolveStaleLiteral` to run *after*
  `refreshCoercionAndWideningConstraints`. Predict, then observe, the `nest(1)` /
  `existentialization` regression (a `Movable` witness on the literal's type gets force-failed
  before the literal defaults). Understand the ordering fix.

**Build.** Exercises E8–E10 (Part 4): the graded features that extend the change.

**Checkpoint — this is the goal of the whole document.** Explain, unprompted:
- Why deferral alone fixes #253 but not the operator case.
- Why the operator case needs a *search*, and why naive push-down is wrong (`UInt32*UInt32→UInt64`).
- Why `resolveStaleLiteral` tries the default first, and why that keeps the common case fast.
- Why it must run before coercion defaulting, and how "unpinnable" is decided.
- What makes two conformers "ambiguous", and why the default never participates in an ambiguity.

### Module 10 — Lowering the chosen type

**Read.** `loweredBuiltinIntegerLiteralConversion` and its float sibling in `IREmitter.swift`, and
how `.new(integer_literal:)` is special-cased during lowering. This is where the *type* the
checker chose turns into actual machine bits.

**Probe.** `--emit raw-ir` on `let x: Int32 = 1` and on `let x: Float64 = 1`; find the emitted
integer vs floating-point constant. Note that Float can't currently lower to LLVM (pre-existing) —
so this is where that boundary lives.

**Checkpoint.** Trace one integer literal from source token → elaborated `.new` call → chosen type
in the solution → emitted IR constant. If you can narrate that end to end, you understand the
literal's whole lifetime.

---

## Part 3 — Capstone: re-derive the change

On a clean branch (`git stash` or a fresh checkout of the pre-change state), reconstruct the work
from scratch, using `Docs/LiteralInference.md` as the *spec* but not copying the diff:

1. **Phase A** — defer nil-expected literals to a variable; add `LiteralConstraint`; add
   last-resort defaulting in the solver. Target: `#253` and argument position pass, `let x = 1`
   still `Int`, no regressions (`swift test`).
2. **Phase C** — make `Float32/64` expressible by integer literals (stdlib + `isBuiltin` +
   `IREmitter`). Target: `let x: Float64 = 1`.
3. **Phase B** — upgrade defaulting into the conformer search with ambiguity. Target:
   `literal-operator-result.hylo` passes; `ambiguous-literal.hylo` errors.

Rules: predict each trace before running; run the full suite after each phase; when something
breaks, diagnose from the trace before looking at the reference. You will hit the two historical
bugs — good. You have "won" when your tree passes the same tests with code you can explain line by
line.

---

## Part 4 — Exercise catalogue (graded)

Difficulty: 🟢 grasp a concept · 🟡 a real change · 🔴 design + implement. Some are genuinely
useful; some are throwaway scaffolding whose only purpose is to make a concept concrete. Each names
the module(s) it reinforces.

- **E1 🟢 (m2)** Hand-write a union-find unifier for a toy grammar `T ::= Int | Bool | Var n | T→T`
  in a scratch Swift file. Unify `Var0 → Int` with `Bool → Var1`; produce the substitution.
- **E2 🟢 (m3)** Add counters to the solver for goals created / postponed / refreshed; print a
  one-line summary per discharge. Watch them on a nested arithmetic expression.
- **E3 🟢 (m5)** On member-resolution failure, attach a note listing candidate names found on the
  receiver type. Purely diagnostic; teaches candidate sets.
- **E4 🟡 (m6,7)** Add a user-defined widening coercion (a `given` producing a type equality
  witness) and a positive test that a value flows through `solve(widening:)`.
- **E5 🟡 (m7,10)** Re-derive int→float from a clean tree (stdlib `given`s + `isBuiltin` gate +
  `IREmitter` case). The end-to-end "new built-in conformance" drill.
- **E6 🟢 (m8)** On paper, compute `(errors, penalties)` per candidate for `(1 + 1) as Wide` with a
  user type; predict the winner; confirm against the trace.
- **E7 🟡 (m4)** Add a `Bool`/character/hex-integer literal form: lexer token, parser node,
  `LiteralExpression` conformance, elaboration. Get it to type-check.
- **E8 🟡 (m8,9)** Wire the dormant penalty channel: give the conformer search a real
  `SolutionScore` penalty for non-default conformers (instead of the current default-first,
  containsError selection) and reconcile it with the fast path. Compare designs; keep tests green.
- **E9 🔴 (m9)** Improve the ambiguity diagnostic to *name the candidate types* ("could be `A` or
  `B`") and point at each. Requires threading candidate info out of the search.
- **E10 🔴 (m8,9)** Implement Rust-style *restricted* literal variables: instead of enumerating all
  conformers, model an integer literal as a variable that may only unify with types in a fixed
  "integer kind" and falls back to `Int`. Compare its power and cost to the conformer search;
  write up where each wins (this is a genuine design essay backed by code).
- **E11 🔴 (real & useful, m6,7)** Add arithmetic operators (`AdditiveArithmetic`, `Numeric`,
  comparisons) to `Int32`/`Int64` in the standard library, mirroring `Int` with the right
  `Builtin` ops. This is what makes the literal *example* `(1 + 1) as Int32` finally work
  end-to-end — the one piece `Docs/LiteralInference.md` scoped out. High value.
- **E12 🔴 (m9)** Address the quadratic worst case: make `resolveStaleLiteral` avoid re-forking
  literals already known to default cleanly (e.g. resolve independent literals in one pass).
  Benchmark against a big literal tuple; prove no regression.

Suggested order: E1, E2, E3 (warm up) → E6, E7 (front-of-pipeline + scoring) → E4, E5 (coercion +
conformance) → E8, E9 (own the change) → E10, E11, E12 (design-level). Do E11 whenever you want a
satisfying, shippable win.

---

## Part 5 — Are you confident? (self-audit)

You are done when you can, from memory:

- Narrate the life of `1` in `let x: Int32 = 1` and in `(a * b) as Wide`, naming every constraint
  and solver step.
- Explain each of the 9 changed files in one sentence and why it was necessary.
- State three ways a deferred literal can get its type (context pin, default, conformer search) and
  give a program that exercises each.
- Explain the two historical bugs (qualification-vs-value; ordering vs coercion defaulting) and why
  the fixes are correct.
- Name one thing that could still go wrong (perf on literal-heavy expressions; ambiguity policy;
  the missing `Int32` arithmetic) and argue the trade-off.
- Reproduce the whole change on a clean tree with green tests.

If any of these is shaky, the module that owns it (Part 1 table) is where to go back.
