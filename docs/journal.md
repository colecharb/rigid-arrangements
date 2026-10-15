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
