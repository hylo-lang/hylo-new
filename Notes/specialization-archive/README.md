# Algorithm specialization for Hylo — work archive

Everything on this machine about the 2026-09 algorithm-specialization work on `hylo-new`, gathered
on 2026-10-07 so it can be backed up. The code is in three local branches that were **never pushed**,
so this directory holds the only copy of the work that does not depend on this clone.

## The problem

Write `lower_bound` once for `BidirectionalCollection`, add a better one for
`RandomAccessCollection` (or for `Array`), and have the more specific one win, including inside
generic code. `Docs/State-of-Generics.md` lists this under *Known limitations → Specialization*.

Hylo compiles generics by **witness passing (existentialization)**, not monomorphization. So a
specialized implementation has to be reachable from a witness that someone passes in. It can't be a
code-generation trick.

## The result in one paragraph

On `main`, implicit resolution keeps the *smallest* derivation and calls a tie an ambiguity. The
prototype adds a **specificity order over givens**: `g` is at least as specific as `h` if `h`'s head
instantiates to `g`'s head and every requirement of `h` can be derived under `g`'s assumptions. This
is the same idea as C++20 concept subsumption, the "callable from" relation in Siek & Lumsdaine's G,
and Rust RFC 1210. Candidates are ranked by specificity first, then by lexical distance, then by
derivation size. Givens that can't be compared are still reported as ambiguous, and the error now
says why. With this order, the "algorithm as its own trait" encoding (**shape 2**) specializes across
generic boundaries without monomorphization.

### Three ways to write a specializable algorithm

| Shape | Encoding | Works across a generic boundary? | Can third parties extend it? | Cost |
|---|---|---|---|---|
| 1 | Overloads that differ only in constraints | No: the caller's static constraints decide | Yes | none |
| 2 | Algorithm as its own trait (`trait LowerBound`), one `given` per implementation, clients constrained on `LowerBound` | **Yes** | Yes | The constraint spreads to every intermediate function |
| 3 | Algorithm as a trait member, installed by a lifting given `<T is RA> => T is Bidi` | Yes | No: needs the trait's author | Breaks if the type also conforms to `Bidi` directly, which `refines` forces, and it breaks **silently** |

The `proto/shape2-minimal` branch is the smallest change that makes shape 2 work.

### Status and known gaps (as of 2026-09-03)

- Checked at the **IR level only**. The LLVM backend can't yet lower a generic client that takes a
  conformance witness (`Runtime-defined IRWitnessTable operand`, hylo-new#342), so none of these
  programs run yet.
- The test suite was green: 186/186 on the first prototype, 199/199 on `overload-specificity`.
- An **equality-constrained** given (`where T.Position == Int32`) doesn't apply, because the
  equality can't be derived from the conformance (probes e15/e16). Separately, a search that can't
  succeed over the built-in equality givens diverges, and **it already does this on `main`**. The
  fuller branch bounds it with a step budget. Shape 2 doesn't need that budget.
- When two libraries each add an equally specific given, the conflict shows up at the **client**
  that imports both. The client fixes it locally with a given whose head is a concrete type.
- Specificity outranks lexical distance, so a *conditional* local override loses to a more specific
  imported given. A local override with a concrete head still wins.
- Not yet designed or built: a `specializing fun` declaration to generate the shape-2 boilerplate
  (P4), `refines` producing lifting givens, collection traits in the stdlib (P5), and inferring the
  algorithm constraints.
- Compile-time cost on a full stdlib typing run: shape2-minimal 4.15–4.24 s; baseline 4.14–4.22 s;
  the full branch 4.32–4.38 s.

## Timeline

All on 2026-09-01 unless noted. Times are Europe/Zurich.

| When | What |
|---|---|
| 01:12 | Start: research and prototype algorithm specialization. Fresh clone of hylo-new at `840aa66`. |
| 01:17–01:40 | Probes e1–e13, `lb.hylo`, `lb_ra_only.hylo` (`probes/`). |
| 01:37 | `proto/specificity-ordering` `ee43a3c`: specificity order for implicit resolution. |
| 01:42 | `proto/overload-specificity` `dc6f1c9`: overload ordering (shape 1). |
| 09:31 | Probes e14–e16 (concrete head, associated-type equality, divergence). |
| 09:57 | Artifact **"Algorithm Specialization for Hylo"** published (design proposal, phases P0–P6). |
| 10:56 | Turned the examples into tests. `tc/` probes, then commits `3ca2a24`, `b25e4e3`, `a881b08` (twelve `specialization-*` tests). |
| 11:30–12:17 | `5ab4c83`: bounded search, full three-way ranking, ambiguity diagnostic. |
| 12:51 | Course-style write-up and multi-module review. `probes/mods/` (separately compiled `Collections`/`Client`/`Turbo`/`Both` modules). |
| 15:47 | What if a type conforms to both Bidi and RA? `q*.hylo` probes, `mods/Both3`. Artifact **"Specializing Algorithms in Hylo"**, last version 15:50. |
| 15:56–16:43 | Minimum needed for shape 2: `proto/shape2-minimal` was created, then squashed onto `main` (`7babb16`). |
| 09-03 15:54 | `74d7c80` "remove comment" on shape2-minimal. |
| 09-03 16:43 | Comparison with the expression problem. Artifact **"The Third Axis"** published at 16:50. |
| 10-07 | This archive. |

## Files in this archive

| Path | Contents |
|---|---|
| `branches.md` | The three branches: head SHAs, commits, files touched, how to restore them. |
| `patches/<branch>/*.patch` | `git format-patch main..proto/<branch>`, readable and appliable with `git am`. |
| `patches/proto-branches.bundle` | `git bundle` of all three branches with exact SHAs. Needs `840aa66` (upstream `main`) as its base. |
| `artifacts/` | Raw HTML of the three claude.ai artifacts, plus `artifacts/README.md` with their URLs. |
| `probes/` | Formerly `~/specialization/proto/`, moved into the repo: the exploratory `.hylo` programs and the `.ir`/`.ast` output used as evidence. See `probes/README.md`. |
| `related-but-not-this.md` | Other things on this machine that mention "specialization" but are about something else. |

## Prior art cited in the work

- Siek & Lumsdaine, *A Language for Generic Programming in the Large* (G): concept-based overloading,
  the `CopyRange` idiom (= shape 2), and §4.3 on dispatch inside generic code.
- Racordon, Flesselle & Pham, *On the State of Coherence in the Land of Type Classes*
  (arXiv:2502.20546): Hylo's position on overlapping and scoped conformances.
- Rust RFC 1210 (specialization). C++20 `[temp.constr.order]`, `[temp.class.order]`, `[temp.func.order]`.
- Wadler, *The Expression Problem* (1998). Zenger & Odersky (FOOL 2005). Oliveira & Cook (ECOOP
  2012). Swierstra, *Data Types à la Carte*. CLOS / AMOP. Ernst, Kaplan & Chambers, *Predicate
  Dispatching* (ECOOP 1998).
