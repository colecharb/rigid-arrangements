# Rigid Arrangements

Formalizing and enumerating **rigid arrangements of tangent unit circles** in the
plane, up to isomorphism, in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

These arrangements look almost like a one-to-one match with hexominoes. Finding out
exactly where that match holds and where it fails is part of the project.

## Layout

| Path | Contents |
| --- | --- |
| `RigidArrangements/` | Lean source (definitions, theorems, enumeration) |
| `docs/problem.md` | The problem statement and open questions about the definitions |
| `docs/journal.md` | Plain-English progress notes, added at regular intervals |

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```
