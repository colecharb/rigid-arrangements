# Brief: constructive rigidity, emergent arrangements, and a formula plan

For a new Claude Code session working locally. Read `CLAUDE.md`, `README.md` (status
overview), and `docs/problem.md` first. The project rules in `CLAUDE.md` apply: all math in
Lean 4 + Mathlib, a journal entry in `docs/journal.md` per milestone, no unlogged `sorry`, Conventional
Commits.

## Setup

- Start from branch `main-8l3ez7` (PR #1, not yet merged). Create your own branch from it,
  e.g. `constructible`, so you don't collide with other sessions. Open a separate PR.
- `lake exe cache get && lake build` (about 1 minute after the cache; whole library builds clean).
- Policy so far: kernel-checked only (`decide` / `decide +kernel`), no `native_decide`, standard
  axioms only. Check headline theorems with `#print axioms`.

## Context in one paragraph

Rigid = Asimow–Roth local rigidity of the contact framework (tangencies are bars of length 2).
Exact counts are proved in Lean for n ≤ 8 (1,1,1,1,1,3,4,9). Off-lattice arrangements start at
11 circles (O11, `RigidArrangements/OffLattice.lean`). `docs/offlattice.md` explains their
structure: lattice pieces ("bodies" = edge-linked families of tangent triangles) glued at forced
algebraic angles, plus two 30-circle examples (H30, E30) where circles in no triangle carry the
arrangement off the lattice. `docs/formula-plan.md` is a broader research plan (read §1–§3).

## Task 1 — move the off-lattice prototypes into the library

`explore/offlattice/proto/OffLatticeProto.lean` is kernel-checked against the library but lives
outside it. Promote, as new library files (e.g. `RigidArrangements/Frame.lean`,
`RigidArrangements/OffLatticeExamples.lean`), cleaned up to repo style:
- the frame criterion `isLattice_iff_frameInv` / `IsRigid.not_isLattice_iff` (off the lattice ⇔
  contacts in ≥ 2 directions mod 60°);
- the body lemma `isLattice_of_triGrown` (a triangle-connected arrangement lies on a lattice);
- the hinge + bar constructor and the certified examples `ex13` (Q13), `ex15`, `ex17` (DH17):
  rigid and not on the lattice;
- optionally the reduction `isLattice_of_card_le_ten_of_cores`.
Import them from `RigidArrangements.lean`, update `docs/offlattice.md` tags from
"Lean-scratch" to "Lean". Done when `lake build` is clean and axioms are standard.

## Task 2 — the cluster-merging calculus in Lean

Rules (clusters = sets of circles that move rigidly in every nearby contact-keeping motion;
atoms = single contacts):
- **R1:** two clusters sharing ≥ 2 circles merge.
- **R2:** three clusters pairwise sharing three distinct circles merge (triangle of clusters;
  must also handle the collinear/degenerate case).
- **R3:** two circles of a cluster exactly 2k apart, joined by a chain of k contacts: the chain
  is forced straight and merges.
- **R4:** two clusters joined by three contacts, not all concurrent and not all parallel, merge
  (classical body-and-bar fact).

Deliverables: a relative-rigidity notion (e.g. `Arrangement.RigidIn A S`), soundness of R1–R4,
a decidable merge-certificate checker with a theorem "certificate ⇒ `IsRigid`", and
re-certification of a few known examples (R14, T14, O11) by certificates. See
`docs/formula-plan.md` WS3 for draft statements. Watch out: R2's degenerate case, and R4's
non-degeneracy hypothesis.

## Task 3 — find and draw the smallest emergent arrangements

"Constructible" = merges to one cluster under R1–R4; "emergent" = rigid but not constructible.
- Using the exploratory census code (`explore/RigidEnum.lean`, plain Lean, compile with
  `lake env lean -c` + `leanc` for speed), classify rigid lattice arrangements by
  constructibility for n up to ~22. Previous data (R1+R2 only): all constructible for n ≤ 19,
  3 classes fail at n = 20 (two bodies + three bars, which R4 should now catch).
- Report the smallest emergent ones under R1–R4, on and off the lattice; is H30 (30 circles) the
  smallest? Search specifically for smaller H30-type examples.
- Add them to the figure `docs/figures/rigid-arrangements.html` (data-driven; see the
  `OFF_EXAMPLES` list) and write `docs/emergent.md`. Mark everything computed vs proved.

## Task 4 — a real plan toward a formula (at least for constructible arrangements)

Write `docs/constructible-plan.md`: a concrete plan to count constructible arrangements c(n).
Ideas to evaluate (not prescriptions):
- whether the merge calculus gives a recursive decomposition (unique canonical core + Henneberg
  steps is already known: `docs/formula-plan.md` WS3), and whether that yields a recursion or
  generating function for c(n) or for natural subclasses;
- transfer-matrix counts for bounded width (width-3 already has a rational GF, see
  `docs/formula-plan.md` §5);
- growth constant via gluing + Fekete (WS1), applied to c(n);
- how c(n) compares with the total and the lattice counts (data from Task 3).
Be explicit about which pieces could become Lean theorems and in what order.

## Order and reporting

Do 1 and 2 first (they can run in parallel), then 3, then 4. Commit each milestone with a
journal entry; keep `README.md`'s status section current. Report back with: what was proved,
what was computed, the smallest emergent examples, and the plan's top three next steps.
