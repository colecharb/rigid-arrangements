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
