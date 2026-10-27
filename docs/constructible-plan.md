# Counting the constructible arrangements: plan

> **Status (2026-10-27).** A plan, written after the cluster calculus R1–R4 and the census of
> `docs/emergent.md` existed, so unlike `docs/formula-plan.md` it starts from data rather than from
> hope. Its main conclusion is a change of target: **c(n) is not the quantity to chase, but the
> constructible class is exactly the right vehicle for certified lower bounds on a(n)**, because
> every constructible arrangement carries a short kernel-checkable certificate and no other family in
> this project does. Three recommended next steps are in §8.

**Notation**, extending `docs/formula-plan.md`:

- **a(n), a_L(n), f_L(n):** rigid arrangements; rigid lattice arrangements; lattice sets counted up to
  translation only ("fixed"), about 12·a_L(n).
- **c(n), c_L(n), f_C(n):** the same three counts restricted to *constructible* arrangements — those
  the calculus R1–R4 assembles from their own contacts. See `docs/emergent.md` §2 for the definition
  and for why the atoms, and only the atoms, may be the starting pieces.
- **e(n) = a(n) − c(n):** the emergent count.
- **μ_L, μ_C:** the growth constants lim f_L(n)^{1/n}, lim f_C(n)^{1/n}.
- **T_w(n), C_w(n):** rigid lattice sets of b-span exactly w, fixed and free respectively.

**Status tags** as in `docs/formula-plan.md`: [Lean], [paper], [computed], [cited], [conj], [spec].

---

## 1. Where we stand

| n | a_L(n) | c_L(n) (R1–R4) | e_L(n) | e_L/a_L | cores | emergent cores |
|---:|---:|---:|---:|---:|---:|---:|
| ≤ 19 | 47 461 (at 19) | = a_L | 0 | 0 | 90 (at 19) | 0 |
| 20 | 111 219 | 111 218 | 1 | 9·10⁻⁶ | 128 | 1 |
| 21 | 260 968 | 260 956 | 12 | 4.6·10⁻⁵ | 236 | 6 |
| 22 | 615 428 | 615 329 | 99 | 1.6·10⁻⁴ | 501 | 7 |

All [computed]; see `docs/emergent.md` §3 for how it was checked. Three readings of this table matter
for the plan.

**c_L(n) = a_L(n) for every n ≤ 19.** So for two thirds of the range the project can enumerate, the
counting problem for the constructible class is the counting problem, full stop. Any formula for c(n)
that is honest about its domain is a formula for a(n) on n ≤ 19 and a different thing afterwards.

**The correction is small but grows about 3.5× per circle**, against 2.35× per circle for a_L itself.
Linear extrapolation of log e_L against n puts e_L/a_L at a few per cent around n = 28–30 and at order
1 in the mid-thirties. [spec] So c(n) and a(n) part company exactly in the range where the project's
other workstreams (WS2's series to n = 28) are aimed. A generating function for c(n) fitted on n ≤ 22
is fitted entirely inside the region where c = a to five decimal places, which is a reason for
caution, not for confidence.

**Emergence lives at cores, but not only at cores.** At n = 21, 6 of the 12 emergent classes are
cores and 6 have a removable circle; at n = 22 it is 7 and 92. The non-core emergent classes are
exactly accounted for by §3's inheritance theorem.

---

## 2. What kind of answer to expect

Two framings, and the plan recommends the second.

**(a) c(n) as a counting target in its own right.** Defensible only if the calculus is close to
complete, and the data says it is not: e_L(n) is growing faster than a_L(n), four of twelve emergent
classes at n = 21 are isostatic irreducible cores, and R1–R4 is a fixed finite list of rules that
nobody has argued is complete for any n. Counting c(n) exactly, in the sense of a closed form or a
rational generating function, is therefore counting an artefact of a particular rule set. Worth doing
only where it is cheap (bounded width, §4).

**(b) c(n) as the certified-lower-bound machine for a(n).** This is where the constructible class
earns its place. Every constructible arrangement has a *certificate*: a list of contacts and a list of
merge steps, which `RigidArrangements/MergeCert.lean` replays decidably, with integer side conditions
on the lattice. So a lower bound on a(n) of the form "here are N constructible classes" is
kernel-checkable at a cost linear in N and in the certificate length, with no analysis and no
floating point. Nothing else in this project has that property: the hinge-and-bar constructor needs a
bespoke algebraic check per example, and the second-order criterion needs rank computations.

This is a real reframing, so state it plainly: **the point of counting constructible arrangements is
that constructible arrangements can be counted *in Lean*.** c(n) ≤ a(n) always, with equality for
n ≤ 19, so every certified count of constructible classes is a certified count of rigid classes, and
μ_C ≤ μ_L, so every certified lower bound on μ_C is a certified lower bound on μ_L. The direction of
the inequality is the one we want.

---

## 3. Does the merge calculus give a recursive decomposition?

This was the brief's first question. The answer is **no, not an exact one**, and the reason is worth
recording so nobody tries again.

The calculus is a **closure operator**, not a grammar. From the contact atoms one generates a
collection of clusters, closed under the four rules; constructibility asks whether the full set
appears in the closure. Derivations are massively non-unique, clusters overlap, and the closure is a
lattice of subsets rather than a tree, so there is no canonical parse to count. The usual route from a
grammar to a generating function — unique decomposition into smaller objects of the same kind — is not
available.

What *is* available, and is genuinely useful:

**Inheritance, downward closure of emergence.** [Lean] If `S` is a cluster and a circle `w` touches
two distinct circles of `S`, then `S ∪ {w}` is a cluster, by one application of R2. Contrapositive: if
`A` is emergent then `A − w` is emergent for every removable `w`. So the emergent family is *downward
closed under peeling*, every emergent arrangement peels to an emergent core along every peeling
sequence, and the smallest emergent arrangement is a core (`docs/emergent.md` §7). This is what makes
the census's "nothing below 20" a theorem about all rigid arrangements rather than a report on a
search.

**So the canonical-core decomposition does give an inequality.** Writing `E_K(n)` for the number of
rigid sets at n whose canonical core is `K`, as in `docs/formula-plan.md` WS3,

    e(n) ≤ Σ over emergent cores K of E_K(n),

because every emergent arrangement peels to an emergent core. **Whether it is an equality is open**,
and it is open for a specific, checkable reason: equality fails exactly when some Henneberg extension
of an emergent core is constructible — when the circles that peeling would remove supply a rule
application the core itself lacked. The data bounds the question tightly at n = 21. S20 is the only
emergent core at n = 20, and a 21-circle emergent arrangement with a removable circle must peel to an
emergent 20-circle one, hence to S20; there are 6 such classes. So `E_{S20}(21) ≥ 6`, and **the
inequality is strict at n = 21 if and only if S20 has more than six rigid Henneberg children.**
Counting them is a few seconds of computation on data the census already produces, and it is the
cheapest unanswered structural question on this page.

A partial answer by hand, for one direction: adding a degree-2 circle `w` to S20, touching `a` and
`b`, appears never to help. If `a` and `b` are adjacent then `{a,b}` is already an atom of S20 and `w`
contributes nothing a rule can use; if they are 2√3 apart then `w` only creates the path `a–w–b`, and
R2 applied to the two new atoms needs a cluster containing both `a` and `b`, which is what one was
trying to produce. [paper, not exhaustive — it is an argument about the shapes of rule applications,
not a verification over all children.]

**Emergence is not, however, monotone in the arrangement.** Add the circle at site (2,3) to S20,
filling one of its two interior holes. It is adjacent to (1,3) and (1,4) of the 4-circle body and to
(2,4), (3,3), (2,2), (3,2) of the 16-circle body, so two R2 steps attach it to each body in turn; the
two enlarged bodies then share that one circle, and a third R2 on the two enlarged bodies and the
surviving cross atom {(2,4), (1,4)} — shared circles (2,3), (1,4), (2,4), distinct — completes the
set. So S20 + (2,3) is constructible, hence rigid: a 21-circle rigid *superset* of an emergent
arrangement that is not emergent. [paper, by the argument just given; a one-line `decide` once §7's
Lean `Constructible` predicate exists] Note this is consistent with everything above, because (2,3)
has degree 6, so S20 + (2,3) has no removable circle: it is itself a core, it does not peel to S20,
and it is therefore not an instance of `E_{S20}(21)`. The practical consequence is that one may not
prune a search by "contains an emergent subset"; the sound pruning is the peeling one of the next
paragraph.

**A side benefit worth taking.** Since every peel of an emergent arrangement is emergent, an
emergence search need only extend *emergent* arrangements — a pruning that is sound by a Lean theorem
rather than by a heuristic. For n = 23, 24 that turns an enumeration of ~1.5 M and ~3.5 M rigid
classes into an extension of 99 and then a few hundred emergent ones, plus a core search. **This is
the cheapest way to push the emergent census to n ≈ 26, and it is step 1 of §8.**

---

## 4. Bounded width: where exact counting does work

[computed, all of this] A *line* is a maximal straight run of the set in one of the three lattice
directions. Writing L for the number of lines and E for the number of contacts, the identity

    e(S) = 3|S| − R₁(S) − R₂(S) − R₃(S)

(the "run identity"; R_i counts runs in direction i, so L = ΣR_i) and the relation u₀ − u₁ + u₂ = 0
among the three plane directions give a local criterion: an infinitesimal flex is exactly one scalar
per line subject to `x_{l₀} − x_{l₁} + x_{l₂} = 0` at each site, so nullity = L − rank, and
infinitesimal rigidity is nullity 3. Scanning columns, only `2W − 1` lines can still grow, so the
state of a transfer matrix is (column mask, the subspace of admissible restrictions to the open slots,
the dimension of partial solutions vanishing on all of them). That is a finite state *when the state
set closes*.

| width | status | growth | GF |
|---:|---|---:|---|
| 3 | exact, closed | 1.429108 | rational, denominator (1−x)(1−x²−x³−x⁵); series to n = 2000 |
| 4 | exact, closed: **91 states**, BFS depth 6 | 1.709227 | rational, order 27, recurrence valid from n = 33, validated over 1200 terms |
| 5 | does **not** close; layered DP exact instead | 1.884269 (300 exact terms) | no linear recurrence of order ≤ 70 fits; probably irrational [conj] |
| 6 | layered DP, n ≤ 52 | ≈ 2.019, still falling | — |

Two results here matter for constructibility.

**For width ≤ 4, constructible = rigid.** Every rigid width-3 class to n = 32 is constructible under
R1+R2 alone; every infinitesimally rigid width-4 class to n = 23 is constructible under R1+R2+R4, with
R3 never needed; all 663 certified singular-rigid width-4 sets are constructible under R1+R2. And all
112 emergent classes at n ≤ 22 have width 5 or 6. So **c_w(n) = a_w(n) for w ≤ 4** on everything
computed, and the exact width-3 and width-4 generating functions above are generating functions for
the constructible class for free.

**Width 5 fails for the same reason S20 is emergent.** The state set does not close, and the way it
fails to close is diagnostic: new states appear at ~113 per column forever, and the denominators of
the subspace coordinates grow *linearly*, exactly `6⌊d/2⌋ − 11` for every depth d from 8 to 352
(complete enumeration, still matching at depths 405, 485, 616 and 792). Linear rather than exponential
denominator growth is the signature of a parabolic recursion: a projective hinge point that drifts by
a fixed parabolic map per repeated column and never returns. That is the same projective-concurrency
degeneracy that makes S20 emergent, and S20 has width 5. **The width-5 obstruction and the emergence
obstruction are one phenomenon.** [conj, with the two independent computations above as evidence]

Also found: the smallest singular rigid lattice arrangement has width exactly 4 and 18 circles, and
for width ≤ 4, n ≤ 17 rigidity and infinitesimal rigidity coincide (checked unconditionally against
6.2 M candidates at n = 17). So T_4 begins to undercount rigid sets at n = 18, by 1, 3, 11, 22, 47, 87
certified singular-rigid classes at n = 18…23.

**Deliverables.** (i) Commit the width-3/4 series and the two programs — done, `explore/gf/`.
(ii) The run identity as a Lean theorem: it is the engine of both this section and the case-(b)
minimality search of `docs/emergent.md` §6, and it is elementary. (iii) The width-4 transfer matrix as
a Lean-verified finite automaton is *possible* (91 states, small integer entries, denominators ≤ 2)
but is a large `decide`; park it behind (ii).

---

## 5. The growth constant for the constructible class

This is the most valuable piece of the plan after §3's pruning, because it is nearly free.

`docs/formula-plan.md` WS1 proves μ_L exists by concatenation: order sites by row then column, let `t`
be the last site of `A`, translate `B` so its first site lands on `t`, and glue. The union is rigid
either by the hinge-and-bar lemma (if some contact joins `A∖t` to `B∖t`) or after adding one connector
circle at `DR` or at `L`. **Every step of that argument stays inside the constructible class**, which
was checked case by case this round [paper, verified independently]:

- the hinge case is R2 with `S₁ = A`, `S₂ = B`, `S₃ = {x,y}` the joining contact itself, shared
  circles `t`, `x`, `y`, distinct because `A ∩ B = {t}` — exactly the pattern by which O11 is
  certified;
- the connector case is a Henneberg step on `A` (the connector touches `t` and one other circle of
  `A`, so R2 by §3's inheritance) followed by a second R2 with the bar from the connector into `B∖t`;
- Fekete also needs **monotonicity** `f_C(n) ≤ f_C(n+1)`, which WS1 gets by "add UL if L is occupied,
  else R" — and that step must *also* be a Henneberg step. It is: UL touches `t` and `L`; and if `L` is
  absent then `D` and `DR` are both present, and `R` touches `t` and `DR`. This hypothesis was missing
  from my first write-up and is the only gap the referee found in the argument;
- the Fekete base carries over: `f_C(3) = 2`, the triangle being R2 from its three atoms;
- decoding and injectivity are purely combinatorial statements about site sets and are untouched.

So `f_C(m)·f_C(n) ≤ f_C(m+n−1) + f_C(m+n)`, hence μ_C exists, with `f_C(n) ≤ 2·μ_C^n` and
`μ_C ≥ (f_C(N)/2)^{1/N}` for every N — the same package as WS1, on the same budget.

**And the certified lower bound is nearly free.** WS1's plan reaches `μ_L ≥ 1.7518` from
`fixedCount_twelve_ge : 1671 ≤ fixedCount 12`, a `decide` over `latticeCatalogue12` times the 12
lattice symmetries. For the constructible version one needs a *constructibility* witness per counted
class, not merely a rigidity witness — and there is a cheap route: every set the Henneberg generator
produces has a build order by construction, and **a build order is a constructibility derivation**, by
§3's inheritance step plus induction. So if the catalogue members carry (or can be re-derived with)
their build orders, the same `decide` yields `1671 ≤ f_C(12)` and hence `μ_C ≥ 1.7518`, which by
`μ_C ≤ μ_L` is again a certified lower bound on μ_L. The peel/build check is very cheap — a 26-site
body peels in a fraction of a second.

Note what this does and does not give. `f_C ≤ f_L` gives `μ_C ≤ μ_L`, so lower bounds transfer upward
but the upper bound `f_C(n) ≤ 2μ_C^n` says nothing about `f_L`. Nothing known shows `μ_C = μ_L`; by
§1's extrapolation they are probably equal if and only if the emergent share stays `o(1)`, which the
data suggests it does not. **`μ_C < μ_L` is the natural conjecture.** [conj]

Independent support for the value: the per-width growth constants 1.429108, 1.709227, 1.884269, ≈2.019
rise toward μ_L, and an Aitken extrapolation of the four gives ≈ 2.46–2.56, consistent with the
project's μ_L ≈ 2.5. [computed, weak]

---

## 6. How c(n) compares with a(n), and one place the hexomino analogy breaks

For n ≤ 19, c_L = a_L exactly. For n = 20, 21, 22 the deficits are 1, 12, 99 — relative deficits
9·10⁻⁶, 4.6·10⁻⁵, 1.6·10⁻⁴, a factor ≈ 3.5 per circle against a_L's ≈ 2.35. Of the emergent classes,
0, 4 and 44 are isostatic (rank exactly 2n − 3); the rest are singular.

Off the lattice the picture is different in kind: both known case-(b) arrangements have 30 circles, and
exactly one of them is emergent (H30; E30's taut chain is R3's hypothesis verbatim). So the off-lattice
emergent count begins at 30, ten circles later than the lattice one, and the first off-lattice emergent
example is *infinitesimally rigid* while the first lattice one is singular.

**Where the hexomino analogy breaks.** The project's working analogy is between rigid lattice
arrangements and polyiamonds/polyhexes, and the user's standing suspicion is that the match is not
exact. Here is a clean place where it fails, and the failure is structural rather than numerical.
Constructibility has **no combinatorial shadow at all**: every polyiamond is built one cell at a time
by definition, so a "constructible polyiamond" is every polyiamond, and the emergent family corresponds
to nothing on the combinatorial side. The obstruction that creates it — three bar lines concurrent — is
projective, not combinatorial: it depends on the actual positions of three contacts, is invisible to the
adjacency structure, and is exactly what the transfer-matrix state space cannot absorb at width 5. So
any claimed correspondence between the two counting problems must either stop at n = 19 or explain a
correction term that has no cell-counting meaning. [paper]

A refinement worth recording, because it points at where the correction term might come from. For S20
the concurrency is *forced by a symmetry of the arrangement*: S20 is invariant under the lattice
reflection (a, b) ↦ (4 − b, 4 − a), the axis of that reflection is the line of one of the three
joining contacts, and the reflection exchanges the other two — so their lines meet on the axis and all
three are concurrent. [proved] The same degeneracy is S20's infinitesimal flex, the rotation of the
small body about the point of concurrency (`docs/emergent.md` §4). If emergence at the smallest sizes
is generally symmetry-forced in this way, then the emergent count is a count of *symmetric* lattice
configurations of a particular kind, which is a combinatorial question after all and would be
tractable by Burnside-style arguments — the same machinery the width-3 generating function already
uses. Whether this persists is the open question; the isostatic emergent cores at n = 21 are where to
look, since there the flex is absent and so the symmetry argument, if any, must be different. [spec]

---

## 7. What can become a Lean theorem, in order

The ordering is by dependency, and each item is small enough to be one file or one addition.

1. **A `Constructible` predicate** — an inductive over the contact atoms with one constructor per
   rule, plus soundness `Constructible S → RigidIn S` by cases. Without it, "S20 is emergent" is a
   statement about a program, not about the calculus. **Done** (all four rules).
2. **The replay principle** — a derivation inside a sub-arrangement is a derivation in the ambient
   arrangement. Mechanical (atoms transfer because tangency depends only on centres; the rules are
   statements about the ambient arrangement), but every item below needs it. **Done.**
3. **Inheritance and "the smallest emergent arrangement is a core"**, in the minimal-counterexample
   form of §3 — no confluence needed. **Done**, and in the stronger cores-reduction form, with
   lattice-relativized variants to match the census.
4. **R4's constructor in the certificate checker**, so that a lattice certificate using R4 closes by
   `decide` with the `barDetZ ≠ 0` side condition discharged by integer arithmetic. **Done**, with
   W20 as the first certified arrangement that needs R4.
5. **Build order ⇒ constructible.** One induction on the build order using (3). This is the key that
   unlocks item 6 and converts the project's existing rigidity catalogues into constructibility
   catalogues at no extra cost.
6. **`1671 ≤ f_C(12)`, hence `μ_C ≥ 1.7518`, hence `μ_C ≤ μ_L` gives a certified lower bound on μ_L.**
   The same `decide` as WS1's, plus item 5.
7. **Concatenation stays constructible**, hence submultiplicativity, hence μ_C exists with
   `f_C(n) ≤ 2μ_C^n`. The three cases of §5, each one R2 application; plus the monotonicity step.
8. **The run identity `e(S) = 3|S| − ΣR`** and the consequence `|S| ≥ ΣR − 3` for an infinitesimally
   rigid set. Elementary, self-contained, and the engine of §4 and of the case-(b) minimality search.
   Can be done at any time and does not depend on 1–7.
9. **Decidable emergence for a given lattice set.** Needs the fixpoint to be *the* closure, i.e. the
   maximal-cluster pruning argument (currently a hand proof read and believed, and the one hand
   argument H30's emergence rests on). Hardest item here; do it last, and only if the emergent census
   is to be published as theorems rather than computations.

Items 1–4 are done. Items 5–7 are now the highest value per line of Lean in the whole project: they
turn an existing `decide` into a certified growth bound. Item 8 is free. Item 9 is a research task,
and note what it is *not* — a positive constructibility verdict is already a checkable certificate;
what needs the fixpoint inside Lean is a *negative* verdict, the assertion that no derivation exists.

---

## 8. Top three next steps

1. **Push the emergent census to n ≈ 26 using the Lean-backed pruning of §3.** Because every peel of an
   emergent arrangement is emergent, it suffices to extend the known emergent classes and to search
   cores at each level — not to enumerate all rigid classes. At n = 22 that is 99 classes plus a core
   search instead of 615 428. The payoff is the shape of e(n): whether the ≈ 3.5× ratio holds, whether
   the isostatic share keeps rising (0, 4/12, 44/99), and whether the width stays at 5–6. Everything in
   §1's extrapolation currently rests on three data points. While the machinery is open, print
   `E_{S20}(21)` — the number of rigid Henneberg children of S20 — which settles §3's open inequality
   at the first level where it can be tested, and costs one extra line of output.
2. **Items 5, 6 and 7 of §7: build order ⇒ constructible, then `μ_C ≥ 1.7518` as a theorem, then
   concatenation.** This is the one place where the constructible class buys something no other family
   in the project does, and the referee's observation that build orders are already derivations makes
   the first certified bound nearly free.
3. **Settle whether the width-5 obstruction and emergence are literally the same obstruction.** The
   evidence is two independent computations pointing at a parabolic drift of a projective hinge point:
   the width-5 state set's linearly growing denominators, and S20's three concurrent bar lines. If they
   are the same, there is a theorem of the form "a rigid lattice set in a strip of width ≤ 4 is
   constructible" with a transfer-matrix proof, and the emergent family gets a geometric
   characterisation instead of a census. That is the most interesting mathematics on this page.

---

## 9. Conjectures

- **C1.** `μ_C < μ_L`. [conj] Equivalent to the emergent share not being `o(1)`, which §1's growth
  rates suggest.
- **C2.** Every rigid lattice arrangement of width ≤ 4 is constructible. [conj; verified for width 3 to
  n = 32 and width 4 to n = 23]
- **C3.** The emergent share e_L(n)/a_L(n) reaches order 1 in the mid-thirties. [spec]
- **C4.** The width-5 transfer-matrix generating function is not rational. [conj; no recurrence of
  order ≤ 70 fits 300 exact terms]
- **C5.** No finite list of merge rules of the R1–R4 kind — finitely many clusters, finitely many
  shared circles, one non-degeneracy condition — is complete for local rigidity on the lattice. [spec]
  The isostatic emergent cores at n = 21 are the evidence that the failures are not confined to a
  degenerate set; a proof would presumably come from a family of emergent cores of unbounded size.
- **C6.** Off the lattice, 30 is the smallest emergent arrangement, and H30 is the unique one at 30.
  [conj; the case-(b) minimality search of `docs/emergent.md` §6 proves this for the two known
  mechanisms within the searched window, leaving clusters of ≥ 5 free circles and singular case (b)
  outside the E30 family uncovered]
