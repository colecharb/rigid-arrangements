# Off-lattice rigid arrangements

> **Status (2026-10-21).** This page brings together four exploratory investigations: structure theory, an exact catalogue, an adversarial search, and a Lean prototype. An independent verifier rechecked each one. The prototype has since been promoted into the library: the frame criterion, the body lemma, the peeling and C5 reductions, the two decidable tests and the hinge-and-bar constructor with its certified examples now live in `RigidArrangements/Frame.lean` and `RigidArrangements/OffLatticeExamples.lean`, so the results this page used to mark as kernel-checked-but-not-in-the-repository are now marked **[Lean]**. All exploratory programs are compiled Lean; see §12. **Update (2026-10-27).** R14 and the arithmetic of three-body rings are now in the library; case (b) is known to be exactly minimal at n = 30; and H30 and E30 have been classified against the cluster-merging calculus of `docs/emergent.md`, where they fall on opposite sides. Three corrections to this page are folded in below, at T14 in §4.1 and in §12.

**Units and notation.**
- Circles have radius 1, so touching centres are exactly 2 apart.
- The triangular lattice is Λ = {2a + b(1 + i√3) : a, b ∈ ℤ}; in Lean this is `latticePoint (a, b)`.
- Write ω = e^{iπ/3}, so Λ = 2ℤ[ω]. The norm is N(a + bω) = a² + ab + b², Lean `eNorm`. A lattice vector of norm N has length 2√N.

**Status tags.**
- **[Lean]**: a theorem in the repository.
- **[proved]**: a complete paper proof, rechecked by a verifier.
- **[computed-exact]**: exploratory Lean using exact integer, rational or algebraic arithmetic, or rigorous interval arithmetic.
- **[computed-float]**: floating-point computation.
- **[cited]**, **[conjecture]**, **[speculation]**: as named.

---

## 1. Summary

1. **Every arrangement is built from lattice pieces.** [proved]
   - Take the tangent triangles of an arrangement and group them into maximal families linked through shared edges. Each such family (a *body*) lies on its own rotated copy of the triangular lattice. It is the corner set of a polyiamond.
   - A rigid arrangement is off the lattice exactly when its contacts point in at least two directions modulo 60° [Lean].
2. **Below 30 circles the user's picture holds exactly** [computed-exact, relative to the searches in §6].
   - This covers all 169 known off-lattice arrangements with n ≤ 14, and every off-lattice core found up to n = 17.
   - Each consists of two or three rigid lattice bodies that share *hinge* circles. They are locked by one extra contact (a *bar*), by a third body closing a ring, or by a second shared circle.
3. **The angles are forced, not chosen.** [proved]
   - For a hinge plus a bar, cos θ = (p + q − 1)/(2√(pq)), where 4p and 4q are the squared distances from the hinge to the bar ends.
   - So the possible angles form a countable set of algebraic numbers.
   - Only seven relative rotations occur among the cores with n ≤ 15:
     - arccos(5/6) and arccos(7/8), from hinge + bar;
     - the two rotations of the ring T14, 24.736° and 49.471°;
     - the two rotations of the ring Ring15, 22.819° and 30.516° (its own field, with √7);
     - and the Σ7 coincidence rotation arccos(13/14), which needs no new square root.
   - II15b adds the Σ49 coincidence rotation arccos(47/49) = 2·arccos(13/14). (Its two bodies are 43.574° apart mod 60°, which is −arccos(47/49); the 21.787° in its frame list is the bar.)
4. **Three refinements of the hypothesis are needed.**
   - The relevant angle is the *relative rotation of the two lattices*, not the visible angle at the hinge.
   - Non-lattice rotations come in two arithmetic kinds:
     - *incommensurate*: a new square root appears, such as √11 in O11;
     - *coincidence*: the rotation is rational in ℚ(√3), and the two lattices share a sublattice.
   - A "lattice piece" can be as small as one contact.
5. **The strong form of the hypothesis is false.** [computed-exact / proved]
   - The strong form says that every off-lattice rigid arrangement contains two rigid lattice bodies at a non-lattice angle.
   - Two 30-circle arrangements, **H30** and **E30**, have every triangle in one lattice. Their off-lattice information is carried by triangle-free *free circles*: a braced rhombus in H30, a taut straight chain in E30.
6. **Candidate counts of all rigid arrangements** [conjecture]: a(11) = 70, a(12) = 160, a(13) = 357 (and a(14) = 874).
   - The off-lattice parts 1, 5, 29 (134) are exact for the cores found.
   - Completeness rests on searches, not on a proof (§6).

The off-lattice world is the third place where the polyiamond analogy of `docs/problem.md` breaks. Here the pieces are still polyiamond corner sets, but they are glued at algebraic angles.

---

## 2. Vocabulary

**Building blocks**
- **Triangle.** Three mutually touching circles. Two triangles are *adjacent* if they share two circles.
- **Body.** The set of circles of one connected component of the triangle-adjacency graph: a maximal family of triangles linked through shared edges.
- **Frame.** An isometric copy of Λ. Each body lies in exactly one frame (Theorem 1).
- **Direction class of a contact.** Its direction modulo 60°. All contacts of one body lie in one class.

**Joints between bodies**
- **Hinge.** A circle lying in two bodies.
- **Bar.** A contact lying in no triangle. It is *internal* if both ends are in one body, and a *cross bar* otherwise.
- **Free circle.** A circle lying in no triangle.
- **Port norms.** Take a hinge h and a bar end x in body B. Then p = N((x − h)/2), computed in B's frame, so |hx|² = 4p.
- **Relative rotation ζ of two frames.** The rotation, modulo 60°, that takes the directions of one frame to those of the other. Reflections are absorbed because Λ is mirror-symmetric.

**Cores**
- **Core** (Lean `IsCore`). An arrangement with no *removable* circle. A removable circle is one that touches exactly two circles, and those two are less than 4 apart.
- **Irreducible.** Deleting any one circle leaves a flexible arrangement. A *reducible* core contains a smaller off-lattice rigid arrangement.

---

## 3. Structure theorems

**Theorem 1 (bodies are lattice pieces).** [proved; Lean `isLattice_of_triGrown`, `isRigid_of_grown_pair`]
Let {a, b, c} be any triangle of a body B. Then L = a + ℤ(b − a) + ℤ(c − a) is the unique frame containing B. Moreover, B is congruent to the corner set of an edge-connected polyiamond, so it is rigid (Lean `IsPolyiamond.isRigid`) and infinitesimally rigid.

*Proof.*
- Walk along a spanning tree of the triangle-adjacency graph.
- A triangle {u, v, w'} glued to {u, v, w} along the edge uv has its new apex at w' = u + v − w. This is the only other point at distance 2 from both u and v, and it lies in L.
- Uniqueness: two shortest vectors at 60° generate any frame that contains them. ∎

**Theorem 2 (frame criterion).** [proved; Lean `isLattice_iff_frameInv`, `IsRigid.not_isLattice_iff`]
A connected arrangement lies on a lattice iff (p_j − p_i)⁶ takes the same value for every contact ij, that is, iff all contacts point in the same direction modulo 60°. Rigid arrangements are connected (Lean). So a rigid arrangement is off the lattice iff it has contacts in at least two direction classes.

The connected pieces of each direction class are lattice pieces. They can be tiny: O11 has three classes, namely two chevrons and the bar.

**Lemma 3 (hinges).** [proved]
- Around any circle, neighbour directions are at least 60° apart. A run of directions at exactly 60° is a *fan*.
- A circle lies in at most two bodies.
- A hinge lies in exactly one fan of each of its two bodies, with at most 3 triangles in total.
- Every neighbour of the hinge in one body makes an angle strictly greater than 60° with every neighbour in the other body. An angle of exactly 60° would create a triangle joining the two bodies.

**Lemma 4 (free circles).** [proved; key step Lean `exists_mem_latticeApexes`]
A circle touching two circles of one frame L lies in L.
- The two neighbours are at most 4 apart, so their squared distance is 4N with N ∈ {1, 3, 4}.
- Every point at distance 2 from both of them is a point of L.

Consequently, a circle off a frame touches at most one circle of that frame.

**Theorem 5 (the two ways to be off the lattice).** [proved]
Let A contain a triangle. A lies on a lattice iff all of its bodies lie in one frame L and every free circle lies in L. So A is off the lattice iff one of the following holds:
- **(a)** two bodies lie in different frames; or
- **(b)** all bodies lie in one frame L, and some free circles lie off L.

In case (b), each off-L circle touches at most one circle of L. If A is infinitesimally rigid, more is true: every connected cluster C of off-L circles is triangle-free, has at least 4 circles, and contains a cycle.
- Pinning L, the motions of C are killed only if e(C) + e(C, L) ≥ 2|C|.
- A triangle-free plane graph has e(C) ≤ 2|C| − 4.
- By Lemma 4, e(C, L) ≤ |C|.

**Corollaries.**
- **Translation lemma.** [proved; checked exactly]
  - Suppose two bodies' frames differ only by a translation. If the bodies share a circle, or are joined by bars with at least two different bar vectors, they lie in one frame. The reason: two radius-2 circles about distinct lattice points at most 4 apart meet only at lattice points.
  - If all bar vectors are equal, the second body slides (shear flex, Lean `not_isRigid_of_shear`).
  - So for *directly* joined bodies, "different frame" means "non-lattice relative rotation".
- **Peeling.** [proved; Lean `isLattice_of_removable`, `isLattice_of_card_le_ten_of_cores`]
  - Adding a removable circle never takes a lattice arrangement off the lattice.
  - So every off-lattice rigid arrangement peels (Lean `IsRigid.erase`) to an off-lattice rigid core.
  - Conjecture C5 below 11 therefore reduces to one claim: every rigid core with 9 or 10 circles lies on the lattice.
- **Triangles must exist.** [proved, paper]
  - Contacts never cross (Lean `disjoint_segment_of_adj`), so the contact graph is plane.
  - With m contacts, Euler's formula gives at least 2 + 2(m − 2n + 3) triangular faces when m ≥ 2n − 3.
  - So every infinitesimally rigid arrangement with n ≥ 3 contains a body.
  - No triangle-free rigid arrangement exists on the lattice [proved]. Off the lattice none is known [conjecture: none exists].
- **Degrees of freedom.** [proved; generic sufficiency cited: Laman 1970, Tay 1984]
  - Bodies have 3 degrees of freedom and free circles 2. A hinge removes 2 and a cross bar removes 1. So DOF = 3b + 2f − 2H − m.
  - Hinge + bar: 6 − 2 − 1 = 3, rigid.
  - Ring of three bodies: 9 − 6 = 3, rigid.
  - Two bodies sharing two circles: 6 − 4 = 2, over-braced by one.
  - Ring of k bodies: k − 3 degrees of freedom.

---

## 4. How lattice pieces lock at non-lattice angles

### 4.1 Hinge + bar: the closing formula [proved]

**Set-up.**
- Bodies B1 and B2 share the hinge h, and x ∈ B1 touches y ∈ B2.
- In half-scale complex coordinates with h = 0, let α = (x − h)/2 ∈ ℤ[ω] in B1's frame and β = (y − h)/2 ∈ ℤ[ω] in B2's own frame. Write p = N(α) and q = N(β).
- B2 is placed by a rotation ζ. For a mirrored placement, replace β by β̄.

**Result.** The bar condition |α − ζβ| = 1 forces:
- cos ∠xhy = (p + q − 1)/(2√(pq));
- a realization exists iff Δ = 4pq − (p + q − 1)² ≥ 0;
- **ζ = τ_s/(ᾱβ)** with τ_s = ((p + q − 1) + s·i√Δ)/2, where s = ±1 records the side of the line hx on which y lies.

Each choice of bodies and ports has 4 realizations: two sides s times two orientations of B2. Their lattice status can differ. A realization is on a lattice iff ζ⁶ = 1. The off-lattice direction is Lean: `hbArr_not_isLattice`, `hbArr_not_isLattice_of_turn`.

### 4.2 Two kinds of non-lattice rotation [proved]

- **Type I, incommensurate (Δ ≠ 3k²).**
  - Here ζ ∉ ℚ(ω). The two frames share only the hinge, and the coordinates need √Δ.
  - O11: (p, q) = (3, 3), Δ = 11. Q13: (4, 4), Δ = 15.
  - A lattice triangle with side norms (p, q, 1) exists iff Δ = 3k² [proved both ways; checked for all norms ≤ 150]. This gives the decidable test `not_isLattice_of_normTriangle_eq_false` [Lean].
- **Type II, coincidence rotation (Δ = 3k² but ζ⁶ ≠ 1).**
  - Here ζ ∈ ℚ(ω). Writing ζ = μ/ν in lowest terms, the two frames share a sublattice of index Σ = N(μ). All prime factors of Σ are ≡ 1 (mod 3).
  - Σ = 7 gives arccos(13/14) ≈ 21.787°, the Σ7 grain-boundary rotation of hexagonal crystals. Σ = 49 gives arccos(47/49) ≈ 16.426°.
  - All coordinates stay in ℚ(√3). **"Non-lattice" does not mean "irrational".**
  - Type II needs a prime ≡ 1 (mod 3) dividing pq.
  - Two bodies can share two circles (at least 2√7 apart) and lock *without any bar*.
- **The hinge angle is not the invariant.** [proved; Lean `ex15_not_isLattice`] In ex15 (§5) the hinge and both bar ends are lattice points of the first body. Its hinge angle arccos(5/(2√7)) ≈ 19.107° is a lattice angle. Yet the second body is turned by the Σ7 rotation.

### 4.3 Which port norms can give an off-lattice angle [proved; checked exhaustively for norms ≤ 100]

Let p ≤ q be Eisenstein norms with Δ ≥ 0.
- **Every realization is on a lattice** exactly for:
  - (p, q) ∈ {(1, 1), (1, 3), (3, 4)};
  - collinear pairs (Δ = 0, p = m², q = (m + 1)²) with m(m + 1) free of primes ≡ 1 (mod 3): (1, 4), (4, 9), (9, 16), (16, 25), (25, 36). The pair (36, 49) is already mixed.
- **Otherwise some realization is off-lattice.**
  - Type I iff Δ ≠ 3k²: (3, 3), (4, 4), (9, 9), (9, 12), (12, 12), (12, 16), …
  - Type II otherwise: (3, 7), (4, 7), (7, 7), (7, 9), (7, 12), (7, 13), (9, 13), (12, 13), …
- **Mixed pairs** [computed-exact]. (3, 7) and (4, 7) split 2 lattice + 2 off-lattice realizations; (7, 7) splits 1 + 3. The lattice realizations of a mixed pair often overlap, so they are not arrangements at all.

**Smallest off-lattice two-body hinge + bar core for each pair** [computed-exact, two independent programs]:

| (p, q) | (3,3) | (4,4) | (4,7) | (7,7) | (3,7) | (7,9) | (9,9) |
|---|---|---|---|---|---|---|---|
| smallest n | 11 (6 + 6) | 13 (5 + 9) | 15 (5 + 11) | 15 (8 + 8) | 16 | 17 | 17 |

**Why O11 comes first** [computed-exact].
- The smallest body with a hinge and a bar end at norm p, all other circles having at least 3 contacts, has s(p) circles. For p = 1, 3, 4, 7, 9, 12, 13, 16, … the sizes are s(p) = 7, 4, 5, 6, 7, 8, 8, 9, …
- The only off-lattice pairs with s(p) + s(q) − 1 ≤ 11 are (3,3), (4,4), (3,7), (4,7) and (7,7). All have hinge angles below 34°.
- Lemma 3 requires the two bodies' fans at the hinge to be more than 60° apart. Within 11 circles only chevron + chevron achieves this, and that is O11.

### 4.4 Other locking patterns

**Ring of three bodies.** [proved]
- Let the hinges be H12, H13 and H23, with norms a = N(H13 − H12) in B1, b = N(H23 − H12) in B2 and c = N(H23 − H13) in B3.
- Then τ = ((a + b − c) + s·i√D)/2, with D = 2ab + 2bc + 2ca − a² − b² − c² (16 times the squared area of the hinge triangle).
- The rotations are ζ12 = τ/(ᾱβ₂) and ζ13 = (τ − a)/(ᾱβ₃).
- The ring is on a lattice iff both rotations are sixth roots of unity.
- It is rigid whenever the three hinges are distinct: the three hinge distances are fixed, and each body is pinned by two hinges. It is infinitesimally rigid iff the hinges are not collinear.
- Hinge + bar is the special ring whose third body is the two-circle rod {x, y}.

**Two bodies sharing two circles (double hinge).** [proved]
- Two rigid bodies sharing two circles are rigid together, by the same pinning argument as Lean `IsLocallyRigid.of_hinge`.
- Off the lattice this is possible only for type II rotations, with the shared circles 2√N apart and N ≥ 7 divisible by a prime ≡ 1 (mod 3).
- Counts [computed-exact]:
  - first at n = 17 (DH17), none for n ≤ 16, and 12 classes at n = 18 (two independent programs);
  - 79 and 377 classes at n = 19 and 20 (one program).

**Three bars and no hinge.**
- [proved] Place B2 by z ↦ t + ζz. The bars say that t is the circumcentre, with radius 1, of the three points x_i − ζy_i. This is a trigonometric polynomial of degree 3 in arg ζ, so there are at most 6 assembly modes per orientation.
- [computed-float] No off-lattice core with n ≤ 14. Two independent searches agree for n ≤ 12; one search covers n = 13 and 14, with about 1.04 million bar triples.
- The one apparent hit, at n = 14, is a hinge + bar in disguise.

**Free connectors.** [computed-float] None of these gives an off-lattice arrangement:
- a hinge plus a touching pair of free circles bridging the two bodies, for n ≤ 13;
- a lattice body of at most 10 circles plus a free 4-ring, for n ≤ 14.

### 4.5 Degenerate cases [proved]

- **Collinear hinge + bar (Δ = 0).** Rigid, since Lean `IsLocallyRigid.of_hinge` needs no non-collinearity, but not infinitesimally rigid.
- **Three bars.**
  - They are infinitesimally flexible iff the three bar lines are concurrent or all parallel. Such configurations can still be rigid at second order.
  - Only equal bar vectors give a genuine motion (shear).
- **Collinear rings.** Rigid but not infinitesimally rigid.

### 4.6 Correction to the plan's frame test (formula-plan WS8) [proved; counterexamples computed-exact and Lean]

WS8 states: "the union is a lattice set iff some lattice symmetry g has eNorm(u − g·v) = 1". Only one direction is true.
- **True direction.** If no g works, the union is off-lattice (Lean `not_isLattice_of_frameCompatible_eq_false`).
- **False direction.** ex15 and S15 pass the test and are off-lattice. The bar closure has two roots. When one root is a lattice symmetry, the other is its reflection in the line hx, and that reflection is off-lattice unless hx points along a multiple of 30°.
- **Correct exact test.** ζ⁶ = 1 for the particular realization. Use T1 for type I, and the turn test `hbArr_not_isLattice_of_turn` for type II.

---

## 5. Catalogue of off-lattice cores

**Notes on the catalogue.**
- *Rotation* means the relative frame rotation modulo 60°.
- *Contacts* is the number of contacts; 2n − 3 means isostatic.
- Exact rank 2n − 3 implies infinitesimal rigidity, hence rigidity (Lean `isRigid_of_isInfRigid`).

| n | core | pattern | norms | rotation(s) | field | contacts | status |
|---|---|---|---|---|---|---|---|
| ≤ 10 | none | | | | | | Lean for n ≤ 8; searched for 9, 10 (§6) |
| 11 | **O11** | chevron + chevron, hinge + bar | (3,3), Δ = 11 | arccos(5/6) = 33.557°, type I | ℚ(√3, √11) | 19 | Lean: rigid, core, off-lattice. computed-exact: irreducible, infinitesimally rigid, unique at 11 |
| 12 | none new | | | | | | computed |
| 13 | **Q13** | trapezoid (5) + 9-circle body, hinge + bar | (4,4), Δ = 15 | arccos(7/8) = 28.955°, type I | ℚ(√3, √5) | 23 | Lean: rigid, off-lattice. computed-exact: core, irreducible, only new core at 13 |
| 14 | **T14** | ring: chevron, trapezoid, chevron | hinges (3,4,3), D = 32 | 24.736° and 49.471° | ℚ(√2, √3) | 25 | computed-exact: core, irreducible |
| 14 | three flower cores | chevron + 9-circle body = O11 + 3 circles completing a hexagonal flower | (3,3) | as O11 | as O11 | 26 | computed-exact: cores, but reducible (contain O11) |
| 15 | **ex15** | trapezoid + 11-circle body, hinge + bar | (4,7), Δ = 12 | arccos(13/14) = 21.787° (≡ 38.213°), Σ = 7 | ℚ(√3) | 27 | Lean: rigid, off-lattice. computed-exact: core |
| 15 | **S15** | two 8-circle bodies, hinge + bar | (7,7), Δ = 27 | arccos(13/14), Σ = 7 | ℚ(√3) | 27 | computed-exact; only 2 direction classes, since the bar lies in B2's frame |
| 15 | **II15b** | two 8-circle bodies, one mirrored | (7,7), Δ = 27 | arccos(47/49) = 16.426° (≡ 43.574°), Σ = 49 | ℚ(√3) | 27 | computed-exact |
| 15 | **Ring15** | ring: trapezoid, 5-circle body, 8-circle body | hinges (4,4,7), D = 63 | 22.819°, 30.516° | ℚ(√3, √7) | 27 | computed-exact |
| 15 | I15 | trapezoid + 11-circle body | (4,4) | as Q13 | ℚ(√3, √5) | 28 | computed-exact; a core, but reducible |
| 16 | 13 two-body hinge + bar cores; 3 ring cores | | | | | | computed-exact; ring count corrected, §10 |
| 17 | 27 two-body hinge + bar cores; **DH17** | DH17: 8- and 11-circle bodies sharing two circles 2√7 apart, no bar | N = 7 | arccos(13/14), Σ = 7 | ℚ(√3) | 32 = 2n − 2 | Lean (as `ex17`): rigid, off-lattice. computed-exact: first double hinge |
| 30 | **H30**, **E30** | case (b): one body plus free circles | | §8 | | 57 / 52 | computed-exact / proved |

**Aliases.** Across the reports these cores have other names:
- Q13 = "T13" = Lean `ex13`.
- T14 = "Ring14".
- The three flower cores = "H14a–c".
- ex15 = "II15a", and S15 = "II15c". Both identifications were checked by equal distance multisets [computed-float].

The two-body core counts 1, 0, 1, 3, 4, 13, 27 for n = 11 to 17 were found by two independent exact enumerators, with no off-lattice core for n ≤ 10.

### Exact coordinates

Radius-1 units. Points are written (x, y). Contacts are pairs at distance exactly 2.

**O11.** Hinge c4, bar c5–c10.
- Chevron 1: c0 = (0, 0), c1 = (1, √3), c2 = (1, −√3), c3 = (2, 0), c4 = (3, √3), c5 = (3, −√3).
- Chevron 2:
  - c6 = (11/2 + √33/6, √3/6 + √11/2)
  - c7 = (14/3 + √33/3, −2√3/3 + √11/3)
  - c8 = (14/3, √3 + √11/3)
  - c9 = (23/6 + √33/6, √3/6 + √11/6)
  - c10 = (3 + √33/3, −2√3/3)
- |c4c5|² = |c4c10|² = 12, and cos ∠c5c4c10 = 5/6.
- Direction classes: chevron 1 at 0°, chevron 2 at 33.557°, bar at 16.779°.
- This is congruent to the repository's `o11`.

**The five off-lattice arrangements of 12 circles.** O11 plus one circle c11 at one of the following:
- (−1, √3), (−1, −√3), (2, 2√3) or (2, −2√3). Each extends a chevron to a 7-circle body.
- (7/2 + √33/6, −5√3/6 − √11/2). This puts a triangle on the bar, giving three pairwise-hinged bodies and no bar.

**Q13.** Hinge c0, bar c2–c12.
- Body 1: c0 = (0, 0), c1 = (1, √3), c2 = (2, 2√3), c3 = (2, 0), c4 = (3, √3).
- Body 2, together with c0:
  - c5 = (−21/8 − 3√5/8, 7√3/8 − 3√15/8)
  - c6 = (−7/4 − 3√5/4, 7√3/4 − √15/4)
  - c7 = (−7/8 − 9√5/8, 21√3/8 − √15/8)
  - c8 = (−7/4, −√15/4)
  - c9 = (−7/8 − 3√5/8, 7√3/8 − √15/8)
  - c10 = (−3√5/4, 7√3/4)
  - c11 = (7/8 − 9√5/8, 21√3/8 + √15/8)
  - c12 = (7/4 − 3√5/4, 7√3/4 + √15/4)
- Body 2's frame is turned by ζ = (7 + i√15)/8.
- Lattice twin: the same 9-circle body with arms (3, 4) instead of (4, 4) gives Δ = 12, a 30° angle, and the lattice core R14 [Lean, `RigidArrangements/Ring.lean`]. R14 shares body 2 and the bar end with Q13 exactly; only body 1 changes, from the five-circle trapezoid with arm norm 4 to a six-circle chevron with arm norm 3. The discriminant drops 15 → 12, and 12 = 3·2² is three times a square, which is what turns a type-I off-lattice angle into a lattice one.

**T14.** Ring with hinges c4, c5 and c6.
- B1 = c0 to c5, the same chevron as in O11.
- B2 = {c4, c6, c7, c8, c9}:
  - c6 = (3 + 4√6/3, −√3/3)
  - c7 = (3 + 2√6/3, √3/3)
  - c8 = (4 + √6, √2)
  - c9 = (4 + √6/3, 2√3/3 + √2)
- B3 = {c5, c6, c10, …, c13}:
  - c10 = (4 + 2√6/3, −2√3/3 − 2√2)
  - c11 = (11/3, −√3 − 4√2/3)
  - c12 = (11/3 + 4√6/3, −√3/3 − 4√2/3)
  - c13 = (10/3 + 2√6/3, −2√3/3 − 2√2/3)
- The hinge triangle has squared sides 12, 16, 12. Its angles are arccos(1/√3) ≈ 54.736° (twice) and arccos(1/3) ≈ 70.529°.
- **All 91 squared distances lie in ℚ(√6)**, not merely in ℚ(√2, √3), and all are ≥ 4 [computed-exact, re-verified 2026-10-27 in exact ℚ⟨1, √2, √3, √6⟩ arithmetic]. The √2 and √3 components all vanish. This is an instance of the general fact proved for rings in `RigidArrangements/Ring.lean`: the discriminant D of the hinge triangle is symmetric in the three hinge norms, so the relative turn of any two bodies is a turn of the same kind with the norms cyclically shifted, and the *same* √D serves everywhere. Hence a single `nonnegSqrt _ _ (3D)` decides every separation, exactly as `hbCheck` does for two bodies — the two radicals of the coordinate field never multiply, because a squared distance pairs the turn against its own conjugate.
- **T14 has five pairs of circles at distance exactly 4**, not one: (c1, c5), (c2, c4), (c4, c6), (c5, c12), (c6, c11) [computed-exact]. So each of the three bodies contains an internal taut pair, a separation test for T14 must be weak rather than strict, and T14 is a candidate for being rigid without being infinitesimally rigid in several places at once.

**ex15.** Hinge c0, bar c2–c14.
- Body 1 = the trapezoid c0 to c4 of Q13.
- Body 2, together with c0:
  - c5 = (−4, 2√3)
  - c6 = (−26/7, 6√3/7)
  - c7 = (−24/7, −2√3/7)
  - c8 = (−17/7, 19√3/7)
  - c9 = (−15/7, 11√3/7)
  - c10 = (−13/7, 3√3/7)
  - c11 = (−11/7, −5√3/7)
  - c12 = (−6/7, 24√3/7)
  - c13 = (−4/7, 16√3/7)
  - c14 = (1, 3√3)
- The hinge triangle c0, c2, c14 is a lattice triangle. Body 2 is mirrored and then turned by (13 − 3√3 i)/14.

**S15.** Hinge c7, bar c6–c14.
- B1: c0 = (0, 0), c1 = (1, √3), c2 = (2, 2√3), c3 = (1, −√3), c4 = (2, 0), c5 = (3, √3), c6 = (4, 2√3), c7 = (3, −√3).
- B2, together with c7:
  - c8 = (8, 0)
  - c9 = (45/7, −5√3/7)
  - c10 = (34/7, −10√3/7)
  - c11 = (54/7, 8√3/7)
  - c12 = (43/7, 3√3/7)
  - c13 = (32/7, −2√3/7)
  - c14 = (41/7, 11√3/7)
- c8 is a lattice point of both frames.

**II15b.** Hinge c6, bar c0–c9.
- B1: c0 = (−5, √3), c1 = (−4, 2√3), c2 = (−3, √3), c3 = (−2, 2√3), c4 = (−1, √3), c5 = (0, 2√3), c6 = (0, 0), c7 = (1, √3).
- B2, together with c6:
  - c8 = (−236/49, −62√3/49)
  - c9 = (−37/7, −√3/7)
  - c10 = (−142/49, −78√3/49)
  - c11 = (−165/49, −23√3/49)
  - c12 = (−48/49, −94√3/49)
  - c13 = (−71/49, −39√3/49)
  - c14 = (23/49, −55√3/49)

**Ring15.** Hinges c0, c4 and c5.
- Trapezoid: c0 = (−4, 0), c1 = (−3, √3), c2 = (−2, 0), c3 = (−1, √3), c4 = (0, 0).
- Other circles:
  - c5 = (−1/2, −3√7/2)
  - c6 = ((−3 + 3√21)/8, (−√3 − 9√7)/8)
  - c7 = (−1/4, −3√7/4)
  - c8 = ((−1 + 3√21)/8, (−√3 − 3√7)/8)
  - c9 = ((−21 − 9√21)/28, (−21√3 − 39√7)/28)
  - c10 = ((−49 − 3√21)/28, (−7√3 − 27√7)/28)
  - c11 = ((−14 − 3√21)/7, (−7√3 − 6√7)/7)
  - c12 = ((−42 − 3√21)/14, (−7√3 − 6√7)/14)
  - c13 = ((−91 − 15√21)/28, (−35√3 − 9√7)/28)
  - c14 = ((−119 − 9√21)/28, (−21√3 + 3√7)/28)
- The hinge triangle has squared sides 16, 16, 28, with cos = 1/8 at c4.

**DH17.** Shared circles c6 and c7, which are 2√7 apart.
- Body 1: c0 = (−4, −2√3), c1 = (−3, −√3), c2 = (−2, 0), c3 = (−3, −3√3), c4 = (−2, −2√3), c5 = (−1, −√3), c6 = (0, 0), c7 = (−1, −3√3).
- Body 2, together with c6 and c7:
  - c8 = (4, −2√3)
  - c9 = (26/7, −6√3/7)
  - c10 = (24/7, 2√3/7)
  - c11 = (17/7, −19√3/7)
  - c12 = (15/7, −11√3/7)
  - c13 = (13/7, −3√3/7)
  - c14 = (11/7, 5√3/7)
  - c15 = (6/7, −24√3/7)
  - c16 = (4/7, −16√3/7)
- There is no contact between the two bodies outside c6 and c7. The smallest cross squared distance is 48/7.

---

## 6. Counts

| n | lattice a_L(n) | off-lattice | by core | candidate a(n) | Lean lower bound |
|---|---|---|---|---|---|
| 11 | 69 | 1 | O11 | **70** | 70 (`seventy_le_card_rigidClasses_eleven`) |
| 12 | 155 | 5 | 5 from O11 | **160** | 155 |
| 13 | 328 | 29 | 28 from O11, 1 = Q13 | **357** | none yet |
| 14 | 740 | 134 | 120 from O11, 10 from Q13, T14, 3 flower cores | 874 | none yet |
| 15 | 1655 | ≥ 554 | Types A, C, E and composites only | ≥ 2209 | none yet |

**What is exact.**
- Lattice column [computed]: the repository's census. Independent programs agree up to n = 15.
- Off-lattice column [computed-exact]: the Henneberg closure of the cores found, computed in exact field towers.
  - Every member has exact rank 2n − 3, so it is infinitesimally rigid.
  - Every member is exactly off-lattice.
  - Members are pairwise non-congruent, certified exactly for 10, 406 and 8911 pairs at n = 12, 13 and 14.
  - An independent floating-point closure reproduces 1, 5, 29, 134 and 554.
  - All two-body and ring assemblies lie inside this closure.

**Why a(11..13) = 70, 160, 357 are still conjectures.** The off-lattice counts are complete only relative to the families searched:
- **Exact families:**
  - A: two bodies, hinge + bar, over all rigid lattice bodies of 3 to 12 circles, both roots and both orientations.
  - C: rings of three bodies.
  - E: two shared circles.
  - Composite bodies made from O11 and the n = 12 arrangements.
- **Floating-point families:** three bars, and a free pair of circles.
- **A family-free floating-point "bond-breaking" search.**
  - It starts from every known rigid arrangement, breaks one or two contacts, and follows the motion until a new contact forms.
  - Number of traces: 8,326, 20,914, 55,070 and 146,130 for n = 11 to 14. Of these, 4, 27, 76 and 239 failed (singular point or step limit).
  - Run blind from lattice sets only, it rediscovers exactly 1, 5 and 29 off-lattice arrangements at n = 11, 12, 13, and nothing else.
  - The verifier checked its output files but did not rerun it.

**What is not covered.**
- **Case (b).** No argument excludes it below 30 circles. The searches for small case-(b) designs found nothing, but they are floating point:
  - a lattice body of at most 10 circles plus a free 4-ring, n ≤ 14;
  - a hinged pair plus a free pair, n ≤ 15;
  - hole shapes of 4 to 8 sites.
- **Singular off-lattice arrangements.** None appear in the O11 closure up to n = 15 [computed-float].

**C5 status** (no off-lattice arrangement below 11; O11 unique at 11; 5 at 12).
- Lean for n ≤ 8.
- For n = 9 and 10 it reduces, in Lean, to "every rigid core of 9 or 10 circles lies on the lattice".
- Strongly supported for n ≤ 12 by the exact families and the blind search.
- Not proved.

**Earlier floating-point counts.** The list 1, 5, 29, 134, 554, 2100, 7529 for n = 11 to 17 is confirmed exactly (relative to the families) for the first five terms. The values 2100 and 7529 were not rechecked. They omit double hinges (from n = 17), three-bar cores and case (b), so they are at best lower bounds.

**Two-body subfamily** (all arrangements, not only cores) [computed-exact]:
- 1, 4, 23, 89 classes at n = 11 to 14, from two independent programs.
- 323 and 1034 at n = 15 and 16, from one program; these are lower bounds by distinct exact distance keys.

---

## 7. The user's hypothesis

> "Non-lattice arrangements must be composed of lattice substructures that are then attached at non-lattice angles."

**Read weakly, it is a theorem, but carries no information.** Bodies are lattice pieces (Theorem 1), and off-lattice means at least two contact directions modulo 60° (Theorem 2). Read this way, "lattice pieces with a non-lattice angle somewhere" is just a restatement of "off the lattice".

**Read strongly, it is true for every known example below 30 circles and false in general.** The strong reading H\* is: *every off-lattice rigid arrangement contains two rigid lattice bodies, each with a triangle, at a non-lattice relative rotation.*
- H\* holds for all 169 off-lattice arrangements with n ≤ 14, and for every core found up to n = 17.
- It fails for H30 and E30 (§8).

**The precise statement.** [proved] Let a rigid arrangement contain a triangle. It is off the lattice iff one of these holds:
- **(a)** Two bodies have a non-lattice relative rotation. For directly joined bodies, a pure translation offset is impossible by the translation lemma.
- **(b)** All bodies share one frame, and some triangle-free free circles lie off it. Each off-frame circle touches at most one frame circle. If the arrangement is infinitesimally rigid, the off-frame circles form triangle-free clusters of at least 4 circles, each containing a cycle.

Case (a) is the only one seen below 30 circles.

**Refinements within case (a).**
1. *The angle that matters is the relative frame rotation ζ, not the hinge angle* (ex15).
2. *Angles are forced by closing equations.*
   - Hinge + bar: cos θ = (p + q − 1)/(2√(pq)).
   - Rings: the law of cosines on three lattice distances.
   - Three bars: a degree-3 trigonometric polynomial.
   - So the possible angles form a countable set of algebraic numbers.
3. *Two arithmetic kinds of rotation.*
   - Incommensurate (type I): a new square root, frames sharing only the hinge, and a lock needed.
   - Coincidence (type II, Σ = 7, 13, 19, …): coordinates in ℚ(√3), with a shared sublattice. The pieces may share two circles and need no bar (DH17).
4. *"Attached" means hinged and locked.*
   - A single shared circle leaves a turning motion.
   - The lock can be a bar (O11), a third body closing a ring (T14), or a second shared circle (DH17).
   - Bodies joined by bars alone give no off-lattice core with n ≤ 14 [computed-float].
5. *Pieces can be tiny.*
   - O11's third direction class is the bare bar.
   - A free circle can sit on no body's lattice while its contacts stay in old directions. An example is O11 with a circle g added at lattice point (1, 0) of the left chevron's frame and then a circle f = c10 + 2, at n = 13.
   - At n = 15, two of the 550 one-circle extensions add a circle touching two bodies at a non-lattice distance. This creates five direction classes [computed-exact].
6. *Lattice and off-lattice arise from one mechanism.* Q13 and the lattice core R14 use the same 9-circle body, with arms (4, 4) and (3, 4) respectively. Every off-lattice arrangement with n ≤ 13 is reached from a lattice arrangement by breaking one or two contacts and flexing until a new contact forms [computed-float]. Examples: O11 from lattice set L11#2, Q13 from L13#322.

**Counterexamples to H\*: case (b) is real.**
- H30 (infinitesimally rigid) and E30 (rigid, singular).
- Under a loose reading E30 still fits the hypothesis: its chain, with both anchors, is a straight row of 8 circles attached at the Σ7 angle. H30 does not fit: its free circles form no lattice piece of 3 or more circles, and its contacts fall into five direction classes.

---

## 8. Case (b) examples

**H30.** [computed-exact by rigorous interval arithmetic; found by floating-point search and greedy shrinking]

*Body.* Lattice site (a, b) maps to the point (2a + b, √3·b). The body has 26 sites:
(−2,1), (−2,2), (−2,3), (−1,−1), (−1,0), (−1,1), (−1,2), (−1,3), (0,−2), (0,−1), (0,0), (0,2), (0,3), (1,−3), (1,−2), (1,2), (1,3), (2,−3), (2,−2), (2,2), (2,3), (3,0), (3,1), (3,2), (4,0), (4,1).

*Anchors.* x1 = (0, 0), x2 = (4, 2√3), x3 = (6, 0), x4 = (2, −2√3).

*Free circles.* With c = (3, 0), p = (u, v) and q = (s, t):
- w1 = c + p, w2 = c + q, w3 = c − p, w4 = c − q;
- v = √(4 − (u + 3)²);
- t = −3u(u + 3)/(v − 2√3u);
- s = 9 + 3u − 2√3t;
- u is the root in (−1.055627, −1.055427) of (s − 1)² + (t − 2√3)² = 4, namely u = −1.0555272350889452772…

*Decimals.*
- w1 ≈ (1.944472764911, 0.468001780466)
- w2 ≈ (3.661917731281, 1.492883621212)
- w3 ≈ (4.055527235089, −0.468001780466)
- w4 ≈ (2.338082268719, −1.492883621212)

*Shape.*
- Each w_i touches its anchor x_i.
- w1w2w3w4 is a rhombus of side 2. Its angles are ≈ 70.522° and 109.478°, which is not arccos(1/3). Also |w1 − w3|² ≈ 5.3326536421 ≠ 16/3.

*What was certified.* Two independent interval programs, plus the intermediate value theorem for the root, show:
- 57 = 2n − 3 contacts, and no other ring pair closer than d² ≈ 5.33;
- the body has exact rank 49 = 2·26 − 3;
- the 8 × 8 Jacobian of the ring relative to the body is nonsingular, so the total rank is 57: infinitesimally rigid;
- it is a core;
- it is off-lattice.

*Structure.*
- One body and four free circles.
- Five direction classes: the body; two rhombus-edge directions, ≈ 30.83° and ≈ 41.35° mod 60°; and two tether directions, ≈ 13.53° and ≈ 20.27° [computed-float].
- Because H30 is isostatic, every rigid sub-arrangement with a triangle lies in the body.

**E30.** [proved; integer data computed-exact]

*Body.* 24 lattice sites, listed in build order:
(0,0), (−1,0), (−1,1), (−2,1), (−2,2), (−1,2), (−2,3), (−1,3), (−2,4), (−1,4), (0,3), (0,4), (−1,5), (0,5), (−1,6), (0,6), (1,5), (1,6), (0,7), (1,7), (2,6), (2,7), (3,6), (3,5).

*Chain.* c_j = (11j/7, 5√3j/7) for j = 1 to 6. It runs from P = (0, 0) to Q = (11, 5√3), and |PQ| = 2√N(3 + 5ω) = 2·7 = 14.

*Properties.*
- **Rigid.** The body is rigid (Henneberg build), so |PQ| = 14 stays fixed. Seven links of length 2 spanning 14 must then be straight.
- **Off the lattice.** 7 ∤ j(3 + 5ω) in ℤ[ω].
- **Chain direction.** arg(3 + 5ω) = arccos(11/14) ≈ 38.213°, which is −21.787° mod 60°: the Σ7 angle.
- **Contacts.** 52 < 57, with float rank 51, so not infinitesimally rigid (Lean `not_isInfRigid_of_taut`).
- **A core.**
- **Six chain circles is the minimum** for a non-lattice taut chain. The anchor vector must have norm (k + 1)² without being a multiple of a unit, which needs k + 1 to be divisible by a prime ≡ 1 (mod 3). Hence k + 1 ≥ 7 [proved].

**Earlier, larger instances of the same two mechanisms.**
- **CB35** (35 circles). A free rhombus inside a three-body lattice ring in one frame. Certified by a Krawczyk test in rational interval arithmetic.
- **TC49** (49 circles). The same chain as E30 inside a 43-circle ring, with exact rank 83 for the lattice part.

---

## 9. What is proved, computed, conjectured

| statement | status |
|---|---|
| Bodies lie in unique frames; triangle-grown sets are rigid and on the lattice | proved; Lean |
| Off the lattice ⇔ two contact directions mod 60° (connected / rigid case) | proved; Lean |
| ≤ 2 bodies per circle; hinge fan angles > 60° | proved (paper) |
| A circle touching two circles of a frame is in it | proved; key step Lean |
| Off the lattice ⇔ (a) or (b); infinitesimally rigid case (b) needs triangle-free off-frame clusters of ≥ 4 circles with a cycle | proved (paper) |
| Translation lemma for directly joined bodies | proved (paper + exact check) |
| Peeling preserves lattice-ness; C5 reduces to cores of 9 and 10 circles | proved; Lean |
| ≥ 2n − 3 contacts ⇒ a triangle exists | proved (paper; Euler) |
| Hinge + bar closing formula; types I and II; port-pair classification | proved (paper); classification checked to norm 100 |
| Hinge + bar constructor, rigid and off-lattice; O11, Q13, ex15, DH17 certified | Lean |
| T1 (normTriangle) and T2 (frameCompatible) off-lattice tests | Lean |
| WS8 "iff" frame test | **false** (ex15, S15) |
| Catalogue of cores for n ≤ 14: O11, Q13, T14, three reducible flower cores | computed-exact (relative to the searches) |
| No off-lattice core for n ≤ 10; O11 unique at 11 | Lean for n ≤ 8; otherwise computed (exact families + float searches) |
| a(11..13) = 70, 160, 357 | conjecture |
| H30 exists and is infinitesimally rigid | computed-exact (rigorous intervals) |
| E30 is rigid, singular and off-lattice | proved (paper) + exact integer data |
| H\* fails | proved (via H30 and E30) |
| No triangle-free rigid arrangement exists | proved on the lattice; conjecture off it |
| Smallest case-(b) arrangement is well above 14 | speculation |

---

## 10. Corrections to earlier claims

These were refuted, or corrected, by the verifiers.
1. **WS8 frame-compatibility "iff".** False in the "if" direction (§4.6).
2. **"If Δ = 3k², some orientations are lattice and some are not."** False. For (3, 4) and (1, 1) every orientation is on the lattice. Δ = 3k² only makes the lattice case *possible*.
3. **The (7, 7) split.** It is 1 lattice + 3 off-lattice, not 2 + 2. The 2 + 2 split holds for (3, 7) and (4, 7).
4. **II15a (= ex15).**
   - The bar end is c6 = (−5, −√3) in that report's labelling, not c8.
   - Its two "lattice realizations" make circles coincide, so they are not arrangements.
5. **Ring cores at n = 16.** There are **3** (2 type I, 1 type II), not 2. A bookkeeping bug counted an internal contact of the third body as extra. The missed ring is O11 with a flower glued on the bar edge.
6. **Ring14 / T14 labels.** The B2–B3 hinge is the circle −2 − 2√2 i in that report's frame, not c9.
7. **ex13 / Q13 description.** Body 2 has no circle at the midpoint of the hinge and its bar end. Only body 1's arm is a straight row of three.
8. **Taut-chain direction.** It is the Σ7 direction, not "Σ49". 49 is the norm of the anchor vector.
9. **Rediscovery counts.** The "lattice rediscovery" numbers of the three-bar and free-pair searches are raw hit counts, not distinct classes.
10. **Necessary conditions for locking.** "No concurrent or parallel bars" is necessary only for *infinitesimal* rigidity.
11. **"Every rigid lattice sub-arrangement of H30 lies in the body."** True only for sub-arrangements with at least 3 circles.

**Left unclear, not independently recomputed:**
- the bond-breaking search;
- the two-body counts 323 and 1034 at n = 15 and 16;
- the double-hinge counts 79 and 377 at n = 19 and 20;
- the floating-point free-circle bracing and bars-only searches.

---

## 11. Open questions

1. **The smallest case-(b) arrangement** (at most 30). Does H\* hold for every off-lattice rigid arrangement with fewer than 30 circles?
2. **C5.** Prove that every rigid core of 9 or 10 circles lies on the lattice (WS9 route: corner method plus frames).
3. **Completeness.** Is there a body-graph lemma saying that every off-lattice core is one of: hinge + bar, ring, double hinge, three bars, or a case-(b) linkage? This would turn a(11..13) into theorems.
4. **Triangle-free rigid arrangements.** Do any exist off the lattice? Does every *singular* rigid arrangement contain a triangle?
5. **Linkage-held translations.** Can three or more bodies at lattice rotations but non-lattice translations be held rigidly through free-circle linkages? [speculation]
6. **Growth.** How fast do off-lattice counts grow (C6)? The floating-point share is at least 46% at n = 17, but those counts are lower bounds.
7. **Exact verification beyond n = 14.** Double hinges from n = 17, and case (b), must be included.

---

## 12. Lean targets and files

**In the library** (promoted 2026-10-21; no `sorry`, no `native_decide`, standard axioms only):
- `RigidArrangements/Frame.lean`: the frame theorem (Theorem 2), the body lemma (Theorem 1), the
  peeling and C5 reductions, and the two decidable tests T1 (`normTriangle`) and T2
  (`frameCompatible`);
- `RigidArrangements/OffLatticeExamples.lean`: the hinge-and-bar constructor (`hbCheck`, `hbArr`,
  `hbArr_isRigid`), the two off-lattice criteria (`hbArr_not_isLattice`,
  `hbArr_not_isLattice_of_turn`), and the instances `o11'`, `ex13` (Q13), `ex15`, `ex17` (DH17).

- `RigidArrangements/Ring.lean` (2026-10-27): the lattice core **R14** of §4.1, with its rigidity
  certified twice — by the hinge-and-bar lemma and by the merge rule R2 — and with its contact count,
  degree sequence, triangle count and two-body split all kernel-checked; and the arithmetic of
  three-body rings (`ringD`, `ringTau`, `ringApex`, `conj_ringApex_mul`, `ringTau_mul_eis_re`), which
  establishes that one radical suffices for a ring, as recorded in the T14 entry of §4.1.

Still to do in Lean: the ring *constructor* and T14 itself (a three-body generalization of
`hbCheck`, for which `Ring.lean` settles the arithmetic and leaves the assembly), the case-(b)
examples H30 and E30, and the completeness statements of §11.

**Case (b) is now known to be exactly minimal at n = 30** [computed-exact, 2026-10-27,
`explore/caseb/`]. Over all 237 anchor 4-cycle classes and all 8 sign branches there is exactly one
geometrically legal, off-lattice, infinitesimally rigid closure — H30's rhombus — and its minimum
lattice part is exactly 26 sites, so H30's 30 circles cannot be beaten by that mechanism. For the
taut-chain mechanism, k = 6 is forced, the anchor displacement (3, 5) is forced up to symmetry, and
an exhaustive search over bodies of 11 to 23 sites rediscovers E30's 24-site body exactly as a set;
larger k is excluded by a span bound. Not covered: clusters of five or more free circles, where the
cluster shape is no longer forced, and singular case (b) outside the E30 chain family. The search is
driven by the run identity e(S) = 3|S| − R₁ − R₂ − R₃ [proved], which bounds |S| below by the number
of maximal straight runs and, unlike a connectivity bound, says something about *excluded* sites.

**H30 and E30 fall on opposite sides of the cluster calculus** [computed-exact]. E30's taut chain is
precisely R3's hypothesis — its anchors are 14 = 2·7 apart and joined by a chain of 7 contacts — so
E30 is *constructible*. H30 is **emergent**: no rule fires on the body together with the atoms at its
free circles, and R4 fails for a counting reason (each free circle has exactly one contact into the
body, so no two clusters have three cross bars), which makes H30's emergence independent of the
delicate 70.522° / arccos(1/3) near-miss. So the smallest off-lattice arrangement and the smallest
arrangement the calculus cannot build are different questions; see `docs/emergent.md` §6.

**Exploratory files** (kept in `explore/offlattice/`; plain Lean, not part of the library):
- `explore/offlattice/proto/OffLatticeProto.lean`: the original prototypes, now superseded by the
  two library files above; kept for the record.
- `explore/offlattice/catalogue/`: exact catalogue, closure, verification, and the bond-breaking search.
- `explore/offlattice/structure/TwoBody.lean`, `Rings.lean`, `Fan.lean`: structure-theory enumerators.
- `explore/offlattice/adversary/H30CertI.lean`, `ChainExact.lean`: H30 and E30.
- The independent verifiers' scratch files were not kept; their verdicts are recorded in §10.
- `explore/offlattice/Figs.lean`: floating-point recheck of the figure data. It covers contacts, overlaps, rank and direction classes.