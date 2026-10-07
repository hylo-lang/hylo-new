# Search hits that are about something else

These turn up when you search this machine for "specialization", "monomorph" or "depolymorph". They
are not part of the algorithm-specialization work. They are listed here so nobody chases them again.

- **StableCollections work in `~/hylo-new-2` (2026-07-14).** This was about making the compiler's own Swift `StableCollections` *Swift-specializable*
  (`@inlinable`/`@frozen`, bitmask hashing) for performance. It landed as `a7c26c96` in hylo-new-2.
  It has nothing to do with Hylo-language specialization.
- **Branches `interpreter-monomorphic-functions`** (remotes in `~/hylo-new`, `hylo-new3`, `hylo-new4`,
  `interpreter/hylo-new`, …) and **`faster-depolymorphization`** (`~/RustroverProjects/hylo-new5`,
  merged upstream as #394). These are about monomorphization and depolymorphization in the
  interpreter and IR pipeline. They're useful background, since depolymorphization is the
  witness-passing model the work above builds on, but they're separate efforts.
- **Upstream docs** in this repo: `Docs/State-of-Generics.md` (lists Specialization under Known
  limitations, and is the starting point of this work) and `Docs/Depolmorphization.md`. They are
  already in git, so they aren't copied here.
