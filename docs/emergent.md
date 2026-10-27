# Emergent arrangements

> **Status (2026-10-27).** New page. It answers the question "which rigid arrangements can the
> cluster-merging calculus build, and which can it not?" over all 1 071 083 rigid lattice
> arrangements with n ≤ 22, and off the lattice for the two known 30-circle examples. The headline:
> the smallest arrangement the calculus cannot build has **20 circles**, not 30. The census was
> written independently of the enumeration it classifies, audited adversarially by a second
> implementation, and its key completeness step is a Lean theorem rather than an assumption.

**Status tags**, as in `docs/offlattice.md`:

- **[Lean]**: a theorem in the repository.
- **[proved]**: a complete paper proof, rechecked by a verifier.
- **[computed-exact]**: exploratory Lean using exact integer, rational or algebraic arithmetic, or
  rigorous interval arithmetic.
- **[computed-float]**: floating-point computation.
- **[conjecture]**, **[speculation]**: as named.

---

## 1. Summary

1. **The smallest emergent arrangement has 20 circles.** [computed-exact]
   It is unique up to isomorphism, and it is a lattice arrangement. This page calls it **S20**. Under
   the full calculus R1–R4 there are no emergent arrangements at all below n = 20, and then 1, 12
   and 99 of them at n = 20, 21 and 22.
2. **H30 is not the smallest emergent arrangement, and E30 is not emergent at all.** [computed-exact]
   The two 30-circle off-lattice arrangements behave differently under the calculus: E30's taut chain
   is exactly R3's hypothesis, so E30 *is* constructible; H30 is emergent. "Smallest off the lattice"
   and "smallest emergent" are therefore different questions with different answers, and conflating
   them gives 30 instead of 20.
3. **It is enough to look at cores.** [Lean]
   Constructibility is inherited along a Henneberg step: if `S` is a cluster and a new circle touches
   two distinct circles of `S`, then `S` together with the new circle is a cluster, by one application
   of R2. Hence a rigid arrangement with a removable circle is constructible as soon as its peeling
   is, so a minimal emergent arrangement has no removable circle — it is a core. This is what makes
   "nothing emergent below 20" a complete statement about *all* rigid arrangements rather than a
   statement about the ones the search happened to visit.
4. **Emergence is not only a degeneracy.** [computed-exact]
   S20 itself is singular: its rigidity matrix has rank 36 where 2n − 3 = 37, with a one-dimensional
   infinitesimal flex and a one-dimensional self-stress, so S20 is rigid only by the second-order
   criterion. But at n = 21 four of the twelve emergent arrangements are isostatic — rank exactly
   2n − 3 — and at n = 22 forty-four of the ninety-nine are. So there exist genuinely infinitesimally
   rigid, isostatic, irreducible cores that R1–R4 cannot build. The calculus is more incomplete than
   a "it only fails on the singular set" story would suggest.
5. **Emergence begins at width 5.** [computed-exact]
   Every rigid arrangement that fits in a strip of 3 or 4 lattice rows is constructible, and all 112
   emergent classes found at n ≤ 22 have minimum width 5 (61 of them) or 6 (51). The width-5 obstruction
   and S20's obstruction are the same phenomenon — a projective concurrency that drifts by a fixed
   parabolic map as a pattern repeats — which is also why the transfer-matrix method that works at
   widths 3 and 4 fails at width 5. See `docs/constructible-plan.md` §3.
6. **R4 is the rule that matters, and it is now proved.** [Lean]
   R1 and R2 alone leave 3, 33 and 248 emergent classes at n = 20, 21, 22. Adding R4 removes two
   thirds of them. Adding R3 as well removes one more at n = 21 and eight more at n = 22. The counts
   are in §3.

---

## 2. What "constructible" means

The cluster-merging calculus is defined in `RigidArrangements/Cluster.lean` and described in the
journal entry of 2026-10-27. A set `S` of circles of an arrangement `A` is a **cluster** when every
nearby placement that keeps all of `A`'s contacts keeps all the mutual distances within `S`
(`Arrangement.RigidIn`). The rules are:

- **R1** — two clusters sharing two distinct circles merge. [Lean]
- **R2** — three clusters pairwise sharing circles, three distinct ones in all, merge. [Lean]
- **R3** — if two circles of a cluster are at distance exactly 2k and are joined by a chain of k
  contacts, the chain is forced straight and merges into the cluster. [Lean]
- **R4** — two clusters joined by three contacts whose lines are neither concurrent nor all parallel
  merge. [Lean]

R4 demonstrably does work no earlier rule does. **W20** — the 4 × 6 block minus (0,0), (1,2), (2,3),
(3,5) — has twenty circles, 37 contacts, minimum degree 3, and splits into two ten-circle bodies with
exactly three contacts crossing between them: one too few for R1, the wrong shape for R2. Its three
cross bars lie on the lattice lines a = 0, a + b = 4, a = 3 — two parallel, one crossing, determinant
3 — and R4 fires. W20 is certified rigid in the library by a lattice certificate whose last step is
R4, closed by a single `decide +kernel` with the determinant discharged inside it. [Lean] It is the
exact counterpart of S20, which has the same shape of join and a vanishing determinant.

An arrangement is **constructible** when, starting from its *contacts* as two-element clusters and
applying the rules until no rule fires, the result is a single cluster containing every circle. It is
**emergent** when it is rigid but not constructible.

> **The atoms matter, and only the atoms.** Constructibility must be defined as the closure of the
> contact atoms. `Cluster.lean` also provides `rigidIn_of_comap`, which says that a rigid
> sub-arrangement is a cluster; taken with the identity map it says that *every* rigid arrangement is
> a cluster, so if arbitrary rigid sub-arrangements were admitted as starting pieces, everything would
> be constructible and this page would be empty. `rigidIn_of_comap` is a tool for proving a particular
> set is a cluster once one knows its sub-arrangement is rigid — it is not a rule of the calculus.
> Where this page says a body is a cluster, that is shorthand for "the body is built from its own
> contacts by R1 and R2", which is checked, not assumed.

Two further warnings, both established while auditing the census:

- **The calculus certifies local rigidity, not infinitesimal rigidity.** R2 merges a configuration
  that is infinitesimally flexible when the three representative circles are collinear, and R3 always
  merges a first-order-flexible configuration. Both are nevertheless sound for local rigidity,
  because the clusters involved already fix all the relevant distances and a degenerate triangle with
  fixed side lengths cannot deform. The calculus must not be reused as an infinitesimal-rigidity
  certificate. [proved]
- **Constructibility is not monotone in the arrangement.** Adding circles to a constructible
  arrangement can leave it emergent and vice versa; the census classifies each isomorphism class on
  its own.

---

## 3. The census

`explore/Constructible.lean` classifies every rigid lattice arrangement up to n = 22 by
constructibility. It reuses the enumeration of `explore/RigidEnum.lean` verbatim — the first 1522
lines are byte-identical, which is what makes the reproduced rigid counts meaningful — and adds the
fixpoint classifier and its cross-checks. Output: `explore/constructible22.txt`.

| n | rigid classes | constructible R1+R2 | R1+R2+R4 | R1–R4 | emergent R1+R2 | R1+R2+R4 | **R1–R4** |
|---:|---:|---:|---:|---:|---:|---:|---:|
| ≤ 19 | 47 461 (at 19) | all | all | all | 0 | 0 | **0** |
| 20 | 111 219 | 111 216 | 111 218 | 111 218 | 3 | 1 | **1** |
| 21 | 260 968 | 260 935 | 260 955 | 260 956 | 33 | 13 | **12** |
| 22 | 615 428 | 615 180 | 615 321 | 615 329 | 248 | 107 | **99** |

Everything in the table is [computed-exact]: integer arithmetic throughout, exact rank by Bareiss
elimination, no floating point anywhere in the classification.

**What was checked, and how.** The classifier was audited by a second agent that wrote its own
independent implementation, and the audit found no bug that changes any verdict. Specifically:

- The rigid counts reproduce `explore/orderly25.txt` on all twenty per-n lines, field for field,
  including search node counts.
- R2's encoding of "three clusters pairwise sharing three *distinct* circles" was checked
  exhaustively against a brute-force system-of-distinct-representatives test over all 4096 triples of
  subsets of a 4-set: 0 mismatches. Three clusters meeting in one single circle do not merge.
- R4 uses the homogeneous *line* row `(P_b − Q_b, Q_a − P_a, P_a Q_b − P_b Q_a)`, which vanishes at
  both endpoints and so really is the line through them. Concurrency and parallelism are projective
  notions and the lattice-to-Euclidean map is a linear isomorphism, so the rank test is valid in
  lattice coordinates. (The velocity row would be the same triple with its first two entries rotated;
  it happens to have the *same* determinant — see §9 — but the line form is the one whose
  transformation law is visible.)
- Every verdict in the run was computed by running the fixpoint on that class: `verifyAll=true` at
  every n, and the number of fixpoint tests equals the full rigid count at every level. No verdict
  was inherited from a smaller arrangement.
- All 112 emergent verdicts were re-derived against the *unpruned* cluster closure, which cannot
  manufacture a false emergent; none is a pruning artefact, and none came back inconclusive.
- The most dangerous classes — all 10 irreducible cores at n ≤ 19 and both singular n = 18 landmarks,
  the places where emergence would first appear if it appeared early — were classified by the
  independent implementation. All are constructible, in fact already under R1+R2.

---

## 4. S20, the smallest emergent arrangement

**The sites.** S20 is the 5 × 5 lattice block `{(a,b) : 0 ≤ a, b ≤ 4}` with five sites deleted:

    S20 = {(a,b) : 0 ≤ a,b ≤ 4} \ {(4,4), (4,0), (2,3), (1,2), (0,0)}

Twenty circles, 37 contacts, minimum degree 3 — no circle has only two neighbours, so S20 has no
removable circle and is an irreducible core. [computed-exact]

**Its rigidity.** Rank 36, generic rank 37, 2n − 3 = 37. So S20 is *not* infinitesimally rigid: it
carries a one-dimensional infinitesimal flex and a one-dimensional self-stress, and its rigidity is
certified by the second-order criterion. [computed-exact] At n = 20 exactly one rigid core needs that
criterion, and S20 is it: the census's one `singular2ndOrder` class at this level is S20 site for
site, with a 1-dimensional space of nontrivial motions and a 1-dimensional space of self-stresses.

So the smallest emergent arrangement and the only n = 20 core whose rigidity is not infinitesimal are
the same arrangement — and this is *not* a coincidence. **The flex and R4's failure are one fact seen
from two sides.** [proved] The nontrivial infinitesimal flex is exactly the rotation of the 4-circle
rhombus about the circle (0,4): each of the three joining contacts has its line through (0,4) *and*
through that contact's rhombus endpoint, so under that rotation each rhombus endpoint starts out
moving perpendicular to its own bar, and all three bars have first-order length rate zero. The
concurrency that kills R4 and the flex that costs the rigidity matrix its last unit of rank are the
same three lines through the same point. The isostatic emergent examples at n = 21 show the
*equivalence* does not generalise — there R4 fails while the arrangement is infinitesimally rigid —
but at n = 20 it is exact.

**And the concurrency itself is forced, not accidental.** [proved] S20 is invariant under the lattice
reflection (a, b) ↦ (4 − b, 4 − a), which maps all twenty sites into S20 and fixes (3,1), (2,2),
(1,3), (0,4). Its axis is the line a + b = 4 — precisely the line of the middle joining contact
(2,2)–(1,3) — and it exchanges the other two joining contacts. Two mirror-image lines meet on the
axis, so all three lines pass through one point. A first draft of this page called the vanishing
determinant a happy accident; it is a theorem about this arrangement.

**Why no rule fires.** Running R1–R4 to saturation leaves **five** clusters, of sizes 16, 4, 2, 2 and 2:

- a 16-circle body;
- a 4-circle body, the rhombus `{(1,4), (1,3), (0,4), (0,3)}` — two triangles sharing an edge;
- the three joining contacts, each left as an unmerged two-circle atom.

The two bodies are disjoint and together cover all twenty circles. Then:

- **R1** cannot fire: it needs two shared circles, and the bodies share none. The surviving atoms each
  share exactly one circle with each body.
- **R2** cannot fire: it needs three clusters pairwise sharing three distinct circles. Each atom
  bridges the two bodies, so any triple of clusters either repeats a circle or fails to meet.
- **R3** cannot fire: it needs two circles of one cluster at distance exactly 2k joined by a chain of
  k contacts, and no such taut chain runs through a circle outside the cluster.
- **R4** cannot fire, and this is the interesting one. The three joining contacts are

      (2,4)–(1,4),   (2,2)–(1,3),   (0,3)–(0,2)

  whose lines in lattice coordinates are `b = 4`, `a + b = 4` and `a = 0`. **These three lines are
  concurrent**, meeting at `(0,4)` — which is itself a circle of S20, a corner of the small body. So
  the 3 × 3 determinant of their homogeneous line coordinates vanishes and R4's non-degeneracy
  hypothesis fails. [computed-exact; also a `decide`-checked Lean theorem, `barDetZ_s20_cross_bars`]

That single vanishing determinant is the whole reason the smallest emergent arrangement has 20
circles and not 30. If the three bars had been in general position, R4 would have merged the two
bodies and S20 would be constructible like everything below it — and, as the previous paragraphs
record, they are not in general position because S20's own mirror symmetry forbids it, and that same
degeneracy is what makes S20 singular.

The unpruned closure on S20 derives 145 distinct clusters and never reaches the full set — under
R1+R2, under R1+R2+R4 and under R1–R4 alike. [computed-exact, reproduced independently]

A picture is in `docs/figures/rigid-arrangements.html`.

## 5. Twenty-one and twenty-two circles

| n | emergent (R1–R4) | isostatic (rank = 2n−3) | singular (rank = 2n−4) |
|---:|---:|---:|---:|
| 20 | 1 | 0 | 1 |
| 21 | 12 | 4 | 8 |
| 22 | 99 | 44 | 55 |

The isostatic ones are the more striking objects: an isostatic irreducible core is infinitesimally
rigid, has exactly the minimum number of contacts, cannot be peeled, and still cannot be assembled by
any sequence of the four rules. The smallest is at n = 21, with 39 contacts and cluster sizes
`{9, 10, 2, 4, 2}`:

    {(4,3), (4,2), (3,4), (3,3), (3,2), (3,1), (3,0), (2,5), (2,4), (2,2), (2,1), (2,0),
     (1,5), (1,4), (1,3), (1,1), (1,0), (0,4), (0,3), (0,2), (0,1)}

All twelve n = 21 and all ninety-nine n = 22 emergent classes are printed in full in
`explore/constructible22.txt`, each with its contact count, exact rank, generic rank, core and
irreducibility flags, and the sizes of the clusters the calculus gets stuck on. The printed lists for
*R1+R2* emergence are capped at twelve per level by design and must not be read as exhaustive; the
R1–R4 lists are complete.

**The growth is fast.** Emergent counts 1, 12, 99 grow by a factor of about 3.5 per circle, against
about 2.35 per circle for the rigid counts themselves. Extrapolating, constructibility stops being
overwhelming somewhere around n ≈ 28–30. This matters for counting: see
`docs/constructible-plan.md` §5.

---

## 6. Off the lattice

The two known 30-circle arrangements whose off-lattice information is carried by circles lying in no
triangle (`docs/offlattice.md` §8) fall on opposite sides of the line.

**E30 is constructible.** [computed-exact] Its two anchor circles P = (0,0) and Q = (3,5) of the
24-site body are at squared distance 196 = 14², i.e. exactly 14 = 2·7 apart, and they are joined by a
chain of exactly 7 contacts through the 6 free circles. That is precisely R3's hypothesis, with
k = 7, so the chain is forced straight and merges into the body. The body itself is R2-constructible
from its own contacts: its back-degrees in build order are 0, 1, 2, 2, …, 2, which is a Henneberg
build from a single contact, and it has 45 = 2·24 − 3 contacts.

**H30 is emergent.** [computed-exact + one hand argument] Its 26-site body is a cluster (it peels to a
single contact, so it is R1/R2-constructible from its atoms — worth checking separately, since 26 is
outside the range where "every rigid lattice set is R1+R2-constructible" was computed). The four free
circles form a braced rhombus. On the collection consisting of the body together with the eight atoms
at the free circles, all four rules are dead: maximum pairwise cluster overlap is 1, so R1 fails; all
84 candidate triples fail R2; and R4 fails for a *counting* reason — each free circle has exactly one
contact into the body, and no derivable cluster contains three free circles, so no pair of clusters has
three cross bars at all. The maximum over all 36 cluster pairs is 2.

That counting argument is worth stating because it makes H30's emergence independent of the delicate
arithmetic. H30's free circles sit at an angle whose cosine is 0.33333… against arccos(1/3)'s
0.333333…, a near-miss that a floating-point line-rank computation could easily get wrong; the
certificate resolves it with about twenty digits to spare, `|w₁−w₃|² ∈ [5.3326536421346866…, …]`
against 16/3 = 5.3333…. But since R4 never gets three bars to test, that near-miss never enters the
argument.

R3 does have to be checked for H30, and the obvious check is not sufficient. The anchors x₁ and x₃ are
at squared distance 36, i.e. exactly 6 = 2·3 apart — exactly R3's taut condition for k = 3. The right
test is that a taut chain is straight, so every interior circle of it is the midpoint of its two
neighbours; all twelve midpoint defects at a free circle exceed 1/4, the smallest being 0.3616. And a
free circle cannot serve as a chain *endpoint*, because R3 needs both endpoints in one cluster and the
only clusters containing a free circle are two-element atoms of diameter 2, forcing k = 1.

**The caveat.** The fixpoint check for H30 presumes that the body's 49 atoms merge first. R1, R2 and
R3 are monotone in each cluster, so starting from the whole body is never worse for them; R4 is not
monotone, and the argument that dropping a sub-cluster is safe (`explore/Constructible.lean:1546-1558`)
is a hand proof, read and believed but not formalised. H30's emergence is therefore
**[computed-exact + hand argument]**, not [Lean].

**Thirty is exactly minimal for case (b).** A separate exhaustive search this round settled the
question the brief asked — whether some smaller H30-like arrangement exists. [computed-exact]
Over all 237 anchor 4-cycle classes and all 8 sign branches there is exactly one geometrically legal,
off-lattice, infinitesimally rigid closure, and it is H30's rhombus; its minimum lattice part is
exactly 26 sites, found by a branch-and-bound that ran to completion in 34 993 977 nodes and returned
H30's own 26-site body site for site, never having been given it. For the taut-chain mechanism, k = 6
is forced, Q − P = (3,5) is forced up to symmetry, and the exhaustive search over bodies of 11 to 23
sites rediscovers E30's 24-site body exactly as a set; larger k is excluded by a span bound. So
**n = 30 exactly** for both known case-(b) mechanisms. What is *not* covered: clusters of five or more
free circles, where the shape is no longer forced and a body of ≤ 24 sites is not obviously out of
reach, and singular case-(b) arrangements other than the E30 chain family. See `explore/caseb/README.md`.

The key enabling identity, worth recording on its own: for a lattice set S, writing R₁, R₂, R₃ for the
numbers of maximal straight runs in the three lattice directions,

    e(S) = 3|S| − R₁(S) − R₂(S) − R₃(S),

so infinitesimal rigidity (e ≥ 2|S| − 3) forces **|S| ≥ R₁ + R₂ + R₃ − 3**. H30's body is tight: 26
sites, 49 contacts, ΣR = 29 = 26 + 3. Unlike a connectivity bound this one says something about
*excluded* sites, since excluding a site splits a run and raises ΣR at once, and that is what carried
the search from "no body of ≤ 20 sites" to the exact answer. [proved]

---

## 7. Why cores suffice

The census searches cores and extends them, so a bare statement of its results would be relative to
that search strategy. It is not, because of the following.

**Constructibility is inherited along a Henneberg step.** [Lean] If `S` is a cluster of `A` and a
circle `w` is tangent to two *distinct* circles `a, b ∈ S`, then `S ∪ {w}` is a cluster. The proof is
one application of R2, to the three clusters `S`, `{w,a}`, `{w,b}` with representatives `a`, `w`, `b`.

Three features of this are worth recording, all of them contrary to what one would guess:

- `w ∉ S` is not needed; `w ≠ a` and `w ≠ b` come free from tangency. The only real hypothesis is
  `a ≠ b`.
- **Collinear Henneberg steps are covered.** There is no hypothesis bounding the distance from `a` to
  `b`. The familiar `dist(a,b) < 4` side condition belongs to the *reverse* direction only: peeling a
  straight step can destroy rigidity, but adding one never does.
- `w` touching more than two circles of `S` is harmless; pick any two distinct ones.

**Hence the smallest emergent arrangement is a core.** Let `A` be emergent with n minimal. If `A` is
not a core it has a removable circle `w`; then `A − w` is rigid with n − 1 circles, hence constructible
by minimality; hence `A` is constructible by the inheritance step — a contradiction. One peel, one
inheritance step. [proved; the inheritance step is Lean]

An earlier draft of this argument routed through a canonical core `K(A)`, which presupposes that
peeling is confluent — a claim tagged `[paper]` in `docs/formula-plan.md`, not proved. The
minimal-counterexample form above needs no confluence, and that is how it should be stated.

Independently, the census verified the inheritance step **exhaustively**: across all 1 071 083 rigid
classes with n ≤ 22 it found 0 violations. [computed-exact]

**In the library.** `RigidArrangements/Constructible.lean` carries all of this. `Constructible` is an
inductive predicate with one constructor per rule, seeded only by tangent pairs, and
`Constructible.rigidIn` is its soundness. The **replay principle** — that a derivation inside a
sub-arrangement is a derivation in the ambient one — is `Constructible.image_comap`, by induction on
the derivation. The reduction comes in a form stronger than the minimal-counterexample statement:
`constructible_univ_of_isRigid_of_cores` says that if every rigid *core* with 2 ≤ m ≤ N circles is
constructible then so is every rigid arrangement with 2 ≤ m ≤ N circles, which is what makes a census
of cores a complete answer rather than a sample; `no_emergent_iff_no_emergent_core` is the same as an
iff, and `isCore_of_least_emergent` is the statement above.

Two precisions from formalising it, both of which change what one may say:

- **The n ≥ 2 restriction is load-bearing, not cosmetic.** Every derivation produces at least two
  circles, so at n ≤ 1 *nothing at all* is constructible and every arrangement is vacuously emergent.
  An unrestricted "least emergent arrangement" would therefore always be the empty one and the theorem
  would say nothing. At n = 2 constructibility is a genuine theorem (a rigid pair is a tangent pair,
  hence an atom); at n ≤ 1 it is a convention with nothing behind it, and the census makes the same
  choice by fiat. "Smallest" means fewest circles among arrangements with at least two.
- **The census enumerates lattice arrangements, so the lattice-relativized statements are the ones to
  cite.** The unrestricted theorem quantifies over all arrangements, off-lattice ones included; pointing
  it at the census needs the peel to stay on the lattice, which it does (a sub-arrangement of a lattice
  arrangement is one). `constructible_univ_of_isRigid_of_lattice_cores`,
  `no_emergent_iff_no_emergent_lattice_core` and `isCore_of_least_emergent_lattice` are the matching
  forms. Citing the unrestricted versions alongside the census would claim more than any enumeration
  has covered.

Also worth recording: a removable circle forces at least three circles (itself and its two distinct
neighbours), so every arrangement of at most two circles is a core — which is why the base case of the
induction is where it is. And the Lean predicate currently means the R1+R2+R3 closure; R4 is a
one-constructor addition in exactly three places (the constructor, its case in soundness, its case in
replay), and no statement downstream mentions a rule, so nothing else changes when it is wired in.

---

## 8. Width

A strip of bounded width is where the counting problem is tractable, so it is worth knowing where
emergence sits relative to width. [computed-exact]

- Every rigid width-3 class up to n = 32 is constructible under R1+R2 alone.
- Every infinitesimally rigid width-4 class up to n = 23 is constructible under R1+R2+R4; R3 is never
  needed. R1+R2 alone first fails inside width 4 at n = 20, on 1, 3, 11, 22 classes at n = 20…23. The
  width-4 family is therefore a small, self-contained test bed for R4.
- All 663 certified singular-rigid width-4 sets are constructible under R1+R2 alone.
- **All 112 emergent classes at n ≤ 22 have minimum width 5 (61 of them) or 6 (51).** None has width
  ≤ 4.

So emergence begins at width 5, at n = 20, and the two facts are connected: the reason the
transfer-matrix method closes at width 4 and fails at width 5 is a projective hinge point that drifts
by a fixed parabolic map per repeated column and never returns — the same concurrency degeneracy that
makes S20 emergent. S20 has width 5.

One related landmark found along the way: the **smallest singular rigid lattice arrangement has width
exactly 4** and 18 circles, namely
`{(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)}`
with 33 = 2n − 3 contacts and rank 32. For width ≤ 4 and n ≤ 17, rigidity and infinitesimal rigidity
coincide — checked unconditionally, by certifying every one of the 6.2 M non-infinitesimally-rigid
candidates at n = 17 as flexible. [computed-exact]

---

## 9. Status of every claim on this page

| claim | status |
|---|---|
| R1, R2, R3, R4 are sound | [Lean] |
| A certificate implies rigidity, decidably, on the lattice | [Lean] |
| Constructibility is inherited along a Henneberg step | [Lean] |
| S20's three cross bars have vanishing line determinant | [Lean] (`decide`) |
| S20's concurrency is forced by its mirror symmetry | [proved] |
| S20's flex is the rotation of the small body about the concurrency point | [proved] |
| W20 is rigid by a certificate whose last step is R4 | [Lean] (`decide +kernel`) |
| A certificate's replay keeps every cluster relatively rigid | [Lean] |
| A derivation in a sub-arrangement replays in the ambient arrangement | [Lean] |
| If every rigid core with 2 ≤ m ≤ N circles is constructible, so is every rigid arrangement | [Lean] |
| The smallest emergent arrangement is a core | [proved], inheritance step [Lean] |
| Emergent counts 0 (n ≤ 19), 1, 12, 99 under R1–R4 | [computed-exact] |
| S20 is the unique smallest emergent arrangement | [computed-exact] |
| S20 is singular, rank 36, rigid by the second-order criterion | [computed-exact] |
| 4 of 12 and 44 of 99 emergent classes are isostatic | [computed-exact] |
| The inheritance step has no violations for n ≤ 22 | [computed-exact], exhaustive |
| E30 is constructible by R3 | [computed-exact] |
| H30 is emergent | [computed-exact] + one hand argument (R4's non-monotonicity) |
| 30 is exactly minimal for both case-(b) mechanisms | [computed-exact], within the stated window |
| Emergence begins at width 5 | [computed-exact] for n ≤ 22 |
| The run identity e(S) = 3\|S\| − ΣR | [proved] |
| R2/R3 certify local, not infinitesimal, rigidity | [proved] |

**Three briefing errors corrected while doing this work**, recorded so they are not repeated:

1. R2 was expected to need a separate collinear case. It does not — see §2.
2. The three bars at S20's join were expected to be in general position, so that R4 "should catch" all
   three n = 20 classes that R1+R2 misses. They are concurrent, so R4 catches two of the three and S20
   survives.
3. The velocity-row form of a bar's row was expected not to survive the change to lattice coordinates.
   It does: the velocity row is the line row with its first two entries swapped and one negated, a
   signed permutation, so the two 3 × 3 determinants are *equal*, and both scale by the same factor 12
   under the lattice-to-Euclidean map. The reason to prefer the line form is only that its
   transformation law is visible. [Lean]

**Known gaps.**

- H30's emergence depends on a hand argument about R4's non-monotonicity under cluster pruning.
- The Lean `Constructible` predicate carries R1, R2 and R3; R4 is still to be wired in, which is one
  constructor plus its case in soundness and in replay, with nothing downstream affected. Until then
  the Lean statements are about R1–R3-emergence.
- Even with R4 wired in, "S20 is emergent" would remain a computation rather than a theorem: a
  *positive* verdict is a certificate and is checkable, but a negative one asserts that **no**
  derivation exists, which needs the fixpoint computation and its pruning argument inside Lean. The
  replay principle, the piece the reduction needed, is now proved; this is the piece that is not.
- Case (b) with five or more free circles, and singular case (b) outside the E30 chain family, are not
  covered by the minimality search.
- The published rigid counts (…, 47 461, 111 219, 260 968, 615 428) were checked against this
  repository's own earlier enumeration, not against an external source.

---

## 10. Reproducing

    # the census (compiled Lean, native binary; about two minutes of compute)
    lake env lean -c /tmp/c.c explore/Constructible.lean
    lake env leanc -O3 /tmp/c.c -o /tmp/constructible
    /tmp/constructible orderly 22 22

See `explore/README.md` for the exact link flags and for the other modes (`cores`, which additionally
runs the soundness guard that reports a violation if the calculus ever merges a set carrying a flex
certificate). The case-(b) search is `bash explore/caseb/build.sh <outdir>`; the width and
generating-function programs are in `explore/gf/`.
