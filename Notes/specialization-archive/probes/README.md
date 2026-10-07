# Exploratory probes

These files were in `~/specialization/proto/`, outside the repository, and were moved here on
2026-10-07. `t2` is the compiled binary of `t2.hylo`. Each probe is a small program. Results were read from `hc --emit ir` or `--emit ast`: the
conformance that `main` projects in the IR is the implementation that resolution selected. Some
probe outputs are saved next to the source as `.ir`, `.ast` or `.rawir`.

| Files | Question |
|---|---|
| `e1`–`e5`, `e8`–`e10` | Overlapping givens on Bidi and RA, plus variants. On `main` these are ambiguous; with the order, the RA given is picked. |
| `e6` | The more specific given needs a *deeper* derivation. Needs the search continuation. |
| `e7`, `e13` | Overloads that differ only by constraints (shape 1). `e13` shows the generic-caller limit known from G. |
| `e11` | Incomparable givens. Stays ambiguous, by design. |
| `e12`, `e14` | Refinement chain; concrete-head `Arr<T>` given against RA and Bidi givens. |
| `e15`, `e15a`, `e16` | Associated-type equality as the finer constraint. Hangs the search; `e16` diverges on `main` too. |
| `lb.hylo`, `lb_ra_only.hylo` (+ `lb*.ir`) | A realistic `lower_bound` with two models and two levels of generic client. |
| `t1`, `t2`, `a1`, `a2`, `bench.hylo` | Sanity checks; `bench.hylo` is the typing-time benchmark input. |
| `tc/` | Drafts of the compiler tests (`b-chain`, `c-concrete`, `d-deeper`, `e-context`, `f-own`, `g-lifting`, `h-blanket`, `i-incomparable`, `k-local`, plus overload variants `j*` and witness-passing `m`/`n`). |
| `q*.hylo` | Shape 3 when the type conforms to both Bidi and RA: lifting given against direct conformance, and local overrides. |
| `mods/` | Multi-module experiments. `Collections` is the library, `Client*` add a client-owned given, and `Both*` conform to both traits. The `.ir` files are the client IR that the artifacts quote. |

Build a module and a client like this:

    hc --module-name Collections --emit-module-to Collections.hylomodule Collections.hylo
    hc --module-name Client --module-search-path . --import Collections --emit ir -o Client.ir Client.hylo
