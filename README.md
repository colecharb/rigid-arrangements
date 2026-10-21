# Rigid Arrangements

Formalizing and enumerating **rigid arrangements of tangent unit circles** in the plane, up to
isomorphism, in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Status

**Definitions** (details and every interpretation choice: `docs/problem.md`).
- *Rigid* means local rigidity in the sense of Asimow–Roth: treat each tangency as a bar of
  length 2; every nearby placement that keeps all tangencies is congruent to the original.
- *Isomorphic* means equal after relabeling and an isometry of the plane (reflections allowed).

**Counts.** a(n) is the number of rigid arrangements of n circles, up to isomorphism.

| n | a(n) | status |
|---|---|---|
| 1, 2 | 1, 1 | Lean (trivial: one circle, two touching circles) |
| 3–6 | 1, 1, 1, 3 | Lean, all arrangements (`card_rigidClasses_three_to_six`) |
| 7, 8 | 4, 9 | Lean, all arrangements (`card_rigidClasses_seven`, `card_rigidClasses_eight`) |
| 9, 10 | ≥ 16, ≥ 35 | Lean lower bounds; = 16, 35 conjectured |
| 11 | ≥ 70 | Lean lower bound (69 lattice + the off-lattice O11); = 70 conjectured |
| 12 | ≥ 155 | Lean lower bound; 160 conjectured |
| 13–25 | – | rigid *lattice* arrangements computed to n = 25 (exploratory, `explore/`) |

Every rigid arrangement of at most 8 circles lies on the triangular lattice (Lean). The first
off-lattice one has 11 circles.

**Main results in Lean** (no `sorry`, no `native_decide`, standard axioms only):
- structure: rigid arrangements are connected and have no cut circle; for n ≥ 3 every circle
  touches at least two others; rigidity is invariant under isomorphism;
- tools: adding a circle that touches two others keeps rigidity (Henneberg step); infinitesimal
  rigidity implies rigidity; flex certificates; a hinge-plus-bar gluing lemma;
- classification: the 7-circle flower is the only core (no circle can be peeled off) with at most
  8 circles; this gives the exact counts above;
- examples: O11 (rigid, off the lattice), R13 (a circle in no triangle), sing18 (rigid but not
  infinitesimally rigid), polyiamond corner sets are rigid, nothing on a square grid is rigid.

**Explored, not yet proved** (each claim marked proved / computed / conjectured in its doc):
- `docs/offlattice.md`: what off-lattice arrangements look like. Lattice pieces (polyiamond
  corner sets) glued at forced, algebraic angles; exact catalogue up to 14 circles; two
  30-circle examples where circles outside every triangle carry the arrangement off the lattice.
- `docs/formula-plan.md`: toward a general formula. A closed form is very unlikely; the plan
  aims at a proved growth constant (about 2.5 per circle on the lattice), more data, structure
  theorems, and exactly countable families.

**Next candidates:** move the off-lattice prototypes (`explore/offlattice/proto/`) into the
library; a constructive "cluster-merging" calculus for building rigid arrangements from smaller
rigid ones, and the arrangements it misses; the growth-constant theorem.

## Where to find things

| Path | Contents |
| --- | --- |
| `docs/problem.md` | Problem statement, definitions, interpretation decisions |
| `docs/journal.md` | Dated, plain-English progress notes (the full history) |
| `docs/cores.md` | Proof that the flower is the only core of at most 8 circles |
| `docs/offlattice.md` | Structure and catalogue of off-lattice arrangements |
| `docs/formula-plan.md` | Research plan toward a general formula |
| `docs/figures/rigid-arrangements.html` | Figure of every rigid arrangement for n ≤ 8, plus off-lattice examples |
| `RigidArrangements/` | Lean library (definitions and theorems); `Classification.lean` and `Cores78.lean` hold the headline counts |
| `explore/` | Exploratory Lean programs and their outputs (not part of the library, not built by CI) |

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```
