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
| 13–25 | – | rigid *lattice* arrangements computed to n = 25 (exploratory, `explore/`), and classified by constructibility to n = 22 |

Every rigid arrangement of at most 8 circles lies on the triangular lattice (Lean). The first
off-lattice one has 11 circles.

**Main results in Lean** (no `sorry`, no `native_decide`, standard axioms only):
- structure: rigid arrangements are connected and have no cut circle; for n ≥ 3 every circle
  touches at least two others; rigidity is invariant under isomorphism;
- tools: adding a circle that touches two others keeps rigidity (Henneberg step); infinitesimal
  rigidity implies rigidity; flex certificates; a hinge-plus-bar gluing lemma;
- frames: a rigid arrangement is off the lattice exactly when its contacts point in at least two
  directions modulo 60°; a triangle-connected arrangement lies on a lattice, and what is grown
  from one contact is rigid; "on the lattice up to ten circles" reduces to the same claim for
  cores;
- off-lattice examples by certificate: a general hinge-and-bar constructor driven by one
  decidable check, with Q13 (13 circles), ex15 (15) and DH17 (17) certified rigid and off the
  lattice, and O11 rebuilt by the same constructor; a three-body ring constructor, with T14
  (14 circles) and the lattice core R14;
- a cluster-merging calculus: relative rigidity, and four rules for combining rigid pieces into
  larger ones — two pieces sharing two circles, three pieces pairwise sharing three circles, a taut
  chain, and two pieces joined by three bars in general position. A merge certificate is replayed by
  a decidable check, so on the lattice an arrangement is certified rigid by `decide` alone with no
  geometric input;
- what the calculus can build: an inductive `Constructible` predicate seeded only by contacts, its
  soundness, the principle that a derivation inside a sub-arrangement replays in the ambient one, and
  the reduction that makes a census of cores a complete answer — if every rigid core with between 2
  and N circles is constructible, so is every rigid arrangement in that range, hence the smallest
  arrangement the calculus cannot build is a core;
- classification: the 7-circle flower is the only core (no circle can be peeled off) with at most
  8 circles; this gives the exact counts above;
- examples: O11 (rigid, off the lattice), R13 (a circle in no triangle), sing18 (rigid but not
  infinitesimally rigid), polyiamond corner sets are rigid, nothing on a square grid is rigid.

**Explored, not yet proved** (each claim marked proved / computed / conjectured in its doc):
- `docs/offlattice.md`: what off-lattice arrangements look like. Lattice pieces (polyiamond
  corner sets) glued at forced, algebraic angles; exact catalogue up to 14 circles; two
  30-circle examples where circles outside every triangle carry the arrangement off the lattice.
  Its structure theorems and certified examples are now in the library; the catalogue and the
  two 30-circle examples are still computations.
- `docs/formula-plan.md`: toward a general formula. A closed form is very unlikely; the plan
  aims at a proved growth constant (about 2.5 per circle on the lattice), more data, structure
  theorems, and exactly countable families.
- `docs/emergent.md`: which rigid arrangements the calculus cannot build. Over all 1 071 083 rigid
  lattice arrangements with n ≤ 22 there are none below twenty circles, and then 1, 12 and 99 at
  n = 20, 21, 22. The smallest is unique: the 5×5 block minus five sites, whose three joining
  contacts lie on three concurrent lines — forced by the arrangement's own mirror symmetry — so the
  rule for three bars cannot fire. Off the lattice the answer is different: H30 is emergent, E30 is
  not, and 30 is exactly minimal for both known free-circle mechanisms.
- `docs/constructible-plan.md`: counting the constructible arrangements. The calculus gives no exact
  recursive decomposition, but it is the only family here whose members carry short kernel-checkable
  certificates, which makes it the right vehicle for certified lower bounds on the growth constant.

**Next candidates:** the growth constant for the constructible class as a theorem (a build order
is already a derivation, so an existing `decide` upgrades nearly for free); whether the obstruction
that makes the smallest emergent arrangement emergent is the same one that stops the
transfer-matrix method at strip width 5; the general growth-constant theorem.

## Where to find things

| Path | Contents |
| --- | --- |
| `docs/problem.md` | Problem statement, definitions, interpretation decisions |
| `docs/journal.md` | Dated, plain-English progress notes (the full history) |
| `docs/cores.md` | Proof that the flower is the only core of at most 8 circles |
| `docs/offlattice.md` | Structure and catalogue of off-lattice arrangements |
| `docs/formula-plan.md` | Research plan toward a general formula |
| `docs/emergent.md` | Which rigid arrangements the merge calculus cannot build, and the smallest ones |
| `docs/constructible-plan.md` | Research plan toward counting the constructible arrangements |
| `docs/figures/rigid-arrangements.html` | Figure of every rigid arrangement for n ≤ 8, plus off-lattice examples |
| `RigidArrangements/` | Lean library (definitions and theorems); `Classification.lean` and `Cores78.lean` hold the headline counts |
| `explore/` | Exploratory Lean programs and their outputs (not part of the library, not built by CI) |

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```
