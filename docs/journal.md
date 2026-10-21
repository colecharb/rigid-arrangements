# Research journal

Plain-English progress notes, added at regular intervals. Each entry says what was
formalized or computed, what it means, and what comes next. The Lean code is the
source of truth; this journal explains it.

---

## 2026-10-13: Environment set up

**What exists:** a Lean 4 project that uses Mathlib. It has one file,
`RigidArrangements/Basic.lean`, with the basic objects:

- **`Plane`**: the Euclidean plane ℝ².
- **`Arrangement n`**: `n` unit circles, given by their centers, where no two
  circles overlap. Concretely, every pair of distinct centers is at least 2 apart.
- **`Tangent i j`**: circles `i` and `j` touch. Their centers are exactly 2 apart.
- **`contactGraph`**: the graph with one vertex per circle and an edge for each
  tangent pair.
- **`center_injective`** (proved): two different circles never share a center.
  This sanity check confirms the definitions behave as expected.

**Not yet defined:** *rigidity* and *isomorphism*. These wait for the full
problem description (see `docs/problem.md`).

**Next:** read the full description, settle the open questions in
`docs/problem.md`, then formalize rigidity.

---

## 2026-10-14: The definition of rigidity is settled

**Decisions.** (Details and justifications are in `docs/problem.md`.)

- *Rigid* now means **locally rigid** in the standard sense of rigidity theory (Asimow and
  Roth, 1978). Picture each tangency as a bar of length 2 joining the two centers.
  The arrangement is rigid if every small motion that keeps all these bars at length 2
  merely moves the whole arrangement around without changing its shape. This is exactly
  "no wiggle room".
- The user's clause "each circle touches two others" was dropped at the user's request,
  in favor of the standard definition. For three or more circles it is automatic: a circle
  with only one contact can be swung around that contact. As a consequence, one circle
  and two tangent circles count as (trivially) rigid. Two circles rolling around each
  other is a motion of the pair *as a whole*, which does not count as wiggling.
- Two arrangements are the same if a relabeling and an isometry (rotation, translation,
  or reflection) carry one to the other. Mirror images count as the same, as the user
  confirmed.

**Lean.** Two changes, both compiled with no `sorry`.

- The plane is now modeled as the complex numbers ℂ, which makes rotations easy to
  write down.
- The rigidity notions are stated for points in any metric space, using Mathlib's own
  notion of congruence (equal pairwise distances).
- Proved so far: the equilateral triangle is rigid. Three mutually tangent circles always
  form that triangle. One circle and two tangent circles are rigid.

**Research results** (from a survey of the literature and exploratory computations in
Lean; none of this is a theorem in the repository yet):

- *Counts of rigid arrangements whose centers lie on the triangular lattice* (the
  arrangement of pennies in a honeycomb packing). Free counts for n = 3, …, 13:
  **1, 1, 1, 3, 4, 9, 16, 35, 69, 155, 328.** Several independent Lean programs agree
  on these.
  - The method: every connected set of n lattice sites (there are 3,274,826 of them
    at n = 13) was either certified rigid by an exact rank computation or shown to
    flex by an explicit motion.
  - The sequence does not appear in the OEIS. OEIS A171604 gives the first terms only,
    1, 1, 1, 1, 1, 3, 4.
- *The hexomino question.* Read "hexominoes" as **polyiamonds**: shapes glued from
  equilateral triangles. Put a circle at each corner of a polyiamond with k triangles,
  and you get a rigid arrangement, usually of k + 2 circles.
  - The counts agree exactly for 3 ≤ n ≤ 7: 1, 1, 1, 3, 4 polyiamonds against 1, 1, 1, 3, 4
    arrangements.
  - They first disagree at **n = 8, the hexiamond level**: there are 12 hexiamonds but only
    9 rigid arrangements of 8 circles. The hexagon hexiamond has only 7 corners, because
    its center is a corner of all six triangles. Three other hexiamonds put their circles
    on the same 8 points.
  - From then on, the counts drift apart: 24 against 16 at n = 9, and 66 against 35 at
    n = 10.
  - The exact correspondence is with *saturated* polyiamonds, those containing every
    triangle that their corners span. It holds for every arrangement up to 12 circles.
  - At 13 circles there is a rigid lattice arrangement that is not built from triangles
    at all: a horseshoe of 12 circles with one circle in the gap.
- *Literal hexominoes (squares) never work.* An arrangement on a square grid always
  shears. The count 35 at n = 10 equals the number of hexominoes, but the symmetry types
  differ, so this is a coincidence.
- *Off-lattice arrangements exist.* Take two copies of the 6-circle "chevron" (a fan of
  four triangles), let them share one end circle, and let their other ends touch. The
  angle between them is arccos(5/6) ≈ 33.6°, which is not a multiple of 60°. This
  11-circle arrangement is infinitesimally rigid but lies on no triangular lattice. So
  from n = 11 on, the lattice counts are only lower bounds. A hand proof (not yet checked
  by machine) says every rigid arrangement of at most 9 circles lies on the lattice.

**Next.** Prove the structural facts in Lean: rigidity is unchanged by isomorphism,
flexibility certificates, adding a circle that touches two others, and infinitesimal
rigidity as a certificate. Then certify the small counts.

---

## 2026-10-14: Basic structure theory of rigid arrangements

Four new Lean files, all proved with no `sorry`. Each was checked by an independent
reviewer.

**Isomorphism behaves as expected** (`Isometry.lean`).

- Suppose two finite sets of points have the same pairwise distances. Then some isometry
  of the plane (a rotation or reflection followed by a translation) carries one onto the
  other. Mathlib did not have this, so we proved it.
- Consequence: "isomorphic" really means "the same picture after relabeling and moving
  it rigidly".
- Isomorphic arrangements are both rigid or both not, and they have isomorphic contact
  graphs.
- So it makes sense to count rigid arrangements up to isomorphism.

**Ways to show an arrangement is NOT rigid** (`Flex.lean`). There are two kinds of
explicit wiggle.

- *Rotation:* if a group of circles is attached to the rest only through contacts with
  a single circle c, swing the group around c.
- *Shear:* if all contacts between a group and the rest point in the same direction,
  slide the group sideways.

Consequences, all proved:

- A rigid arrangement is connected.
- Removing any single circle leaves it connected (no "cut circle").
- With three or more circles, every circle touches at least two others. This recovers
  the user's original clause as a theorem rather than an assumption.
- Two circles are rigid exactly when they touch.
- Three circles are rigid exactly when all three touch each other, so the equilateral
  triangle is the only rigid arrangement of three circles. This is the user's example,
  now proved from the standard definition.
- Four circles touching in a ring (like a square) are never rigid.

**Building rigid arrangements one circle at a time** (`Henneberg.lean`).

- Add a new circle touching two circles of a rigid arrangement, and the result is rigid.
  In rigidity theory this is a "Henneberg step".
- Conversely, suppose a circle touches exactly two others, and those two are less than 4
  apart (not on opposite sides of it). Removing it keeps the arrangement rigid.
- Example: the rhombus (two triangles sharing an edge) is rigid.

These two facts reduce the classification to arrangements in which no circle can be
removed this way ("cores").

**The linearized test** (`InfRigid.lean`).

- An arrangement is *infinitesimally rigid* if no first-order motion keeps every contact
  length, except moving the whole arrangement.
- Proved: infinitesimally rigid implies rigid. The proof is an elementary estimate that
  needs no implicit function theorem. This is the tool for certifying rigidity by
  computation.
- Also proved: a circle squeezed between two circles exactly opposite each other, with
  no other contacts, makes the arrangement fail the linearized test. Such an arrangement
  can still be rigid, which is why the definition uses the nonlinear notion.

**Next.** Certify the lattice counts for small n by computation in Lean. Then classify all
rigid arrangements with at most 6 circles, including off-lattice ones, using a geometric
argument about extreme circles. Finally, formalize the 11-circle off-lattice example.

---

## 2026-10-14: Complete classification up to six circles; certified lower bounds

Everything below is proved in Lean with no `sorry`. The only axioms used are Lean's three
standard ones. In particular there is no `native_decide`: every computation is checked by
Lean's kernel.

**Complete classification for n ≤ 6** (`Classification.lean`). Up to isomorphism, the rigid
arrangements are:

| circles | count | the arrangements |
|---|---|---|
| 3 | 1 | the triangle |
| 4 | 1 | the rhombus (two triangles sharing an edge) |
| 5 | 1 | the trapezoid (three triangles in a row) |
| 6 | 3 | the parallelogram (four triangles in a row), the chevron (four triangles fanned around one circle), the big triangle |

The table covers *every* arrangement of unit circles, not just those on a lattice. As a
corollary, every rigid arrangement of at most 6 circles lies on the triangular lattice.

The proof has two halves.

1. *No small cores* (`CoreBound.lean`). Recall that a circle is *removable* if it touches
   exactly two others and those two are not on opposite sides of it. Claim: every rigid
   arrangement of 4 to 6 circles has a removable circle.
   - Choose six directions 60° apart. In each direction, look at the circle that sticks
     out furthest.
   - That circle's neighbors all lie on one side of it, at least 60° apart as seen from
     it. So it touches at most 3 others.
   - If it touches exactly 2, it is removable.
   - If no circle is removable, the six extreme circles are all different and each touches
     exactly three others. That needs at least 6 circles.
   - With exactly 6 circles, the contact graph has every circle touching exactly three
     others. There are only two such graphs on 6 vertices: the complete bipartite graph
     K₃,₃ and the triangular prism. Neither can be drawn with unit circles.
2. *Growing back* (`Small.lean`). Remove a removable circle. What is left is rigid, and by
   induction it is one of the known shapes. The removed circle sat at one of the two points
   at distance 2 from both of its neighbors. A finite check by computer then lists the
   possible results.

**Lower bounds for 7 to 12 circles** (`LatticeCert.lean`).

- For each n we wrote down a catalogue of lattice arrangements and checked by machine two
  things:
  - each one can be built one circle at a time, every new circle touching two earlier
    ones, which proves it rigid;
  - no two are isomorphic. They are told apart by their tables of pairwise distances.
- Result: at least **4, 9, 16, 35, 69, 155** rigid arrangements of 7, 8, 9, 10, 11, 12
  circles.
- These match the exploratory counts of all *lattice* arrangements. Whether they are
  exact needs the classification of cores of 7 or more circles.

**An off-lattice arrangement** (`OffLattice.lean`).

- The 11-circle arrangement O11 is two chevrons that share one end circle and whose other
  ends touch.
- It is proved rigid using a general "hinge plus bar" lemma: two rigid bodies sharing one
  circle and joined by one more contact are rigid.
- It lies on no triangular lattice. The proof: two lattice points at distance 2√3 from a
  common lattice point are never exactly 2 apart.
- So there are **at least 70** rigid arrangements of 11 circles.
- O11 is also a *core*: no circle can be removed. So cores really do appear from n = 11
  on. This is why the method above stops being purely mechanical.

**The polyiamond analogy, made precise** (`Polyiamond.lean`).

- Proved: put a circle at every corner of a polyiamond (any edge-connected set of lattice
  triangles), and the arrangement is rigid.
- Proved: the hexagon hexiamond and the 5-triangle fan have the same 7 corners.
- Proved: the 12 hexiamonds give exactly 10 different arrangements, up to isomorphism.
  One is the hexagon's 7 circles, and the other nine have 8 circles each. The list of 12
  hexiamonds is the classical one; we did not reprove that it is complete.
- This is where "almost 1:1" first fails.
- Square hexominoes have no rigid analogue. Proved: no arrangement of 3 or more circles on
  a square grid is rigid.

**Two examples of where the polyiamond picture fails** (`LatticeCert.lean`).

- *R13* (13 circles) is rigid, yet one of its circles lies in no triangle.
- *sing18* (18 circles) is rigid but fails the linearized test. Its circle at the middle
  of three in a straight line is held only "to second order".

**Next.**

- Classify the cores of 7 and 8 circles. The research suggests the only one is the
  7-circle "flower" (a hexagon around a center). That would turn the lower bounds 4 and 9
  into exact counts for n = 7 and n = 8.
- Push the hull argument further, toward n = 9 and 10.

---

## 2026-10-15: A paper proof that the flower is the only core of 7 or 8 circles

A *core* is an arrangement in which no circle can be peeled off, i.e. no circle touches
exactly two others that are less than 4 apart. Every rigid arrangement is a core with circles
added one at a time, so classifying rigid arrangements reduces to classifying cores.

**Claim** (`docs/cores.md`, *hand proof, not yet in Lean*): if every circle touches at least
two others and no circle can be peeled off, then 7 or 8 circles force exactly 7 circles in
the **flower**, a hexagon of six circles around a seventh. Consequently there are exactly
4 rigid arrangements of 7 circles and 9 of 8, all on the triangular lattice.

How the proof goes, in words:

- Look at the circles that stick out furthest in some direction ("corners"). Each touches
  exactly three others (this was already proved in Lean for the six-circle case).
- If there are at least seven corners, a "sweeping" argument shows that the one remaining
  circle would have to touch all the others, which is impossible: a corner touches only
  three circles, and no circle touches more than six.
- If there are exactly six corners, they form a convex hexagon whose turning angle is
  exactly 60° at every corner, and each corner's three neighbours sit at 0°, 60° and 120°
  from its outgoing side. With at most two circles besides the corners, every side must
  have length 2, and the six corners all touch one common circle in the middle: the flower.

Three independent drafts (a graph case analysis, a convex-hull argument, and the
corner argument above) were written and each was checked by two adversarial referees; all
three survived with only repairable gaps, and the corner argument was chosen as the one to
formalize. A remark: the method stops at exactly ten circles, where the 10-circle lattice
core appears.

**Next.** Formalize it in Lean (three new files: corners, the six-corner frame, and the
7/8-circle classification), then derive the exact counts 4 and 9 with the existing
extension machinery.

---

## 2026-10-15: Exact counts for 7 and 8 circles

The hand proof of the previous entry is now a Lean theorem (`Cores78.lean`, on top of
`CornerBasics.lean`, `LemmaE.lean` and `SixCorners.lean`, about 2,500 lines, no `sorry`,
kernel-checked only):

- **The flower is the only small core.** If every circle touches at least two others and no
  circle can be peeled off, and there are at most 8 circles, then there are exactly 7 and they
  form the flower (`card_eq_seven_and_iso_flower_of_card_le_eight`). This uses nothing about
  rigidity except "every circle touches two others".
- **Exact counts.** Growing the 6-circle shapes one circle at a time, and adding the flower as
  the one new core, the computer check finds exactly **4** rigid arrangements of 7 circles and
  **9** of 8 (`card_rigidClasses_seven`, `card_rigidClasses_eight`). Every rigid arrangement of
  at most 8 circles lies on the triangular lattice (`IsRigid.isLattice_of_card_le_eight`).

The sequence of exact counts is now, for n = 1, …, 8:

  **1, 1, 1, 1, 1, 3, 4, 9**

with certified lower bounds 16, 35, ≥ 70, 155 for n = 9, 10, 11, 12. At n = 8 the count 9
differs from the 12 hexiamonds: this is where "almost 1:1" first fails, now as a theorem about
all arrangements.

The figure `docs/figures/rigid-arrangements.html` shows all of them.

**Next.** A plan for a general formula (or good bounds) for the number of rigid arrangements of
n circles.

---

## 2026-10-15: A plan toward a general formula

`docs/formula-plan.md` is a research plan for the number a(n) of rigid arrangements of n
circles. It came from four investigations (literature, data, structure, exactly countable
families), three competing plans, and a judge who rechecked the numbers. Nothing in it is a new
theorem; the numbers marked *computed* come from exploratory Lean programs, kept in `explore/`.

What the exploration found:

- **Data.** An exploratory census of rigid *lattice* arrangements reached n = 25:
  1, 1, 1, 3, 4, 9, 16, 35, 69, 155, 328, 740, 1655, 3816, 8761, 20411, 47461, 111219, 260968,
  615428, 1454493, 3449768, 8198486 for n = 3, …, 25. (Independent programs agree up to
  n = 15; beyond that the counts rest on one code lineage.)
- **Growth.** The counts grow by a factor of roughly 2.5 per added circle, much slower than
  polyiamonds (about 3.04 per added triangle). The best guess is a(n) ≈ C · μⁿ / n with
  μ ≈ 2.5 ± 0.1 for the lattice count.
- **The polyiamond picture fades.** Rigid lattice arrangements that are not "triangle-closed
  polyiamond corner sets" appear at 13 circles and make up 24% by 25 circles, and their share is
  still rising. A polyiamond whose corner set is not triangle-closed first appears at 26 circles.
  Off-lattice arrangements (like O11) also appear to grow quickly; floating-point searches suggest
  they become a large share by about 17 circles.
- **Exact formulas exist only for thin families**, for example arrangements confined to three
  rows of the lattice (a rational generating function, growth about 1.43ⁿ), or "combs" (growth
  φⁿ, the golden ratio).

What kind of answer to expect: a closed formula is very unlikely, for the same reasons that none
is known for polyiamonds or polyhexes. The realistic targets, in order of priority:

1. **A theorem that the lattice growth constant μ exists**, with rigorous bounds, by a gluing
   argument (two rigid arrangements can be glued at one circle) and Fekete's lemma.
2. **More data**, to n = 28, with predictions for n = 26, 27 written down *before* computing them.
3. **Structure theorems:** every rigid arrangement peels down to a unique core; a merging calculus
   for rigid clusters; a "line-sum" test for infinitesimal rigidity on the lattice.
4. **Exactly solvable families as theorems**, giving certified exponential lower bounds.

The plan ends with questions for the user (which count to target, whether `native_decide` and
compiled Lean may be used for large certificates, OEIS submission, naming).

---

## 2026-10-15: What off-lattice arrangements look like

Prompted by the user's picture, "non-lattice arrangements are lattice substructures attached at
non-lattice angles", an exploration (structure theory, an exact catalogue, an adversarial search,
Lean prototypes, each independently verified) produced `docs/offlattice.md`. In short:

- **Lattice pieces.** Group the tangent triangles into maximal families linked through shared
  edges. Each family (a *body*) lies on its own rotated copy of the triangular lattice: it is the
  corner set of a polyiamond. *[proved; kernel-checked prototype]*
- **When an arrangement is off the lattice.** Exactly when its contacts point in at least two
  directions modulo 60°. *[kernel-checked prototype in `explore/offlattice/proto/`]*
- **The user's picture is right below 30 circles.** Every off-lattice arrangement found (169 of
  them with at most 14 circles: 1, 5, 29, 134 for n = 11, …, 14) consists of two or three lattice
  bodies sharing *hinge* circles, locked by one extra contact (a *bar*), by a third body closing a
  ring, or by a second shared circle. *[exact computation, relative to the completeness of the
  searches]*
- **The angles are forced.** For a hinge plus a bar, cos θ = (p + q − 1)/(2√(pq)), where 2√p and
  2√q are the distances from the hinge to the bar's ends. O11 has p = q = 3, angle arccos(5/6). The
  rotations that occur are algebraic, of two kinds: ones that bring in a new square root (√11 for
  O11, √5 for the 13-circle core Q13) and "coincidence" rotations such as arccos(13/14), under which
  the two lattices share a sublattice and no new square root appears.
- **The strong form fails at 30 circles.** Two 30-circle arrangements, H30 and E30, have every
  triangle in a single lattice piece and still leave the lattice, through circles that lie in no
  triangle: a braced rhombus (H30) and a taut straight chain (E30). So the precise statement is: an
  arrangement is off the lattice iff two bodies lie in differently rotated lattices, or some
  triangle-free circles lie off the lattice of the bodies. Only the first happens below 30 circles
  in everything found.
- **Candidate counts of all rigid arrangements** (conjectural): a(11) = 70, a(12) = 160,
  a(13) = 357, a(14) = 874.

Kernel-checked prototypes of the frame criterion, the body lemma, a reduction of "on the lattice up
to 10 circles" to a statement about cores, and three more certified off-lattice examples (13, 15
and 17 circles) are in `explore/offlattice/proto/OffLatticeProto.lean`, ready to be moved into the
library. The figure now has a gallery of off-lattice examples, colored by direction class.

## 2026-10-21: The off-lattice prototypes are now library theorems

The kernel-checked prototypes in `explore/offlattice/proto/` have been cleaned up and moved into
the library as two new files. Nothing here is new mathematics: these are the statements
`docs/offlattice.md` has been carrying as *Lean-scratch* since 2026-10-15, now built by `lake
build` and checked by CI. All eighteen headline theorems depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), and there is no `sorry` and no `native_decide`.

**`RigidArrangements/Frame.lean`** — when an arrangement lies on the triangular lattice.

The *frame invariant* of a contact is the sixth power of the vector joining the two centres. Its
modulus is always 64, and raising to the sixth power forgets exactly a rotation by a multiple of
60°, so the invariant records which rotated copy of the triangular lattice the contact points
along. The theorem is that this is the whole story: a connected arrangement lies on a lattice
**iff** all its contacts have the same frame invariant. Since rigid arrangements are connected,
a rigid arrangement is off the lattice exactly when its contacts point in at least two directions
modulo 60°. That is the criterion the off-lattice exploration had been using informally.

The file also proves the *body lemma*. Say a circle is *grown* from a seed if it can be reached
by repeatedly adding a circle touching two already-grown circles less than 4 apart. Growth from
a seed on the lattice stays on the lattice; the seed may be a single contact; and so a
triangle-connected arrangement lies on a lattice. Conversely, what is grown from one contact is
rigid, by a chain of Henneberg steps. Together these say that the triangle-connected pieces of
any arrangement — its *bodies* — are rigid polyiamond corner sets, each sitting in a lattice of
its own. Finally, two decidable tests turn the criterion into `decide` calls on integer data
(`normTriangle`, which asks whether a lattice triangle with given side norms exists, and
`frameCompatible`, which asks whether two bodies' bar vectors can be put in one frame by a
lattice symmetry), and `isLattice_of_card_le_ten_of_cores` reduces the conjecture "every rigid
arrangement of at most ten circles is on the lattice" to the same claim about cores only, using
that adding a removable circle never takes an arrangement off the lattice.

**`RigidArrangements/OffLatticeExamples.lean`** — certified off-lattice arrangements.

`OffLattice.lean` builds one off-lattice arrangement, O11, by hand, with its coordinates written
out in ℚ(√3, √11). This file replaces the hand work by a constructor. Give two polyiamonds as
lists of lattice sites, both with their hinge at the origin, and name the two ends of the bar.
The bar then forces the angle between the two bodies, and a single Boolean check `hbCheck`
decides whether the result is a genuine arrangement: it verifies the bar closes, and — this is
the part that needs care — that no two circles of the two bodies overlap. Every squared distance
across the hinge has the form `A + B√(3D)` with `A` and `B` rational and computable, so
comparing it with 4 is a decidable sign test on `p + q√M`. When the check passes, the
arrangement is rigid by the hinge-and-bar lemma.

Two criteria then show the result is off the lattice. The first is the `normTriangle` test: if no
lattice triangle has the hinge triangle's side norms, the arrangement cannot be on a lattice.
The second is needed because the first is not enough — in `ex15` the hinge and both bar ends
*are* lattice points of the first body, and the hinge angle is a lattice angle, yet the second
body is turned by a "coincidence" rotation under which the two lattices share a sublattice of
index 7. When the discriminant `D` is three times a square, that turn lies in ℚ(ρ) and the
question "is the turn a sixth root of unity?" becomes a decidable statement about Eisenstein
integers.

The instances: O11 rebuilt by the constructor (a check on the machinery), and three new certified
examples — `ex13`, the 13-circle core Q13; `ex15`, the 15-circle coincidence-rotation example;
and `ex17`, the 17-circle double hinge DH17, entered as a hinge and a bar. Each is rigid and not
on the lattice. The catalogue in `docs/offlattice.md` is retagged accordingly.

**What this does not settle.** T14 and the other three-body rings are still only computations:
the constructor glues two bodies, not three. H30 and E30, the two 30-circle arrangements whose
off-lattice information is carried by circles in no triangle, are still outside Lean. And the
completeness claims — that the catalogue of off-lattice cores up to 14 circles is exhaustive —
remain computations relative to the searches that produced them.

**Next.** The cluster-merging calculus: a relative-rigidity notion and merge rules, so that
rigidity of a large arrangement can be certified by a short combinatorial certificate rather
than by a hinge-and-bar construction tailored to each case.
