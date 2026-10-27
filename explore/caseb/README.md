# Case (b): is there an off-lattice arrangement smaller than H30?

Exploratory Lean (plain Lean + Std, no Mathlib, no theorems, nothing imported by the library), in
the style of `explore/README.md`. It searches for **case-(b)** off-lattice rigid arrangements —
all bodies in one frame `L`, some triangle-free free circles off `L` (`docs/offlattice.md`
Theorem 5) — smaller than the two known examples H30 and E30, which have 30 circles each.
`docs/offlattice.md` §6 and §11 record that no exhaustive search below 30 had been done, that the
small searches attempted were floating point, and that "the smallest case-(b) arrangement is well
above 14" was only **speculation**.

## Answer

**Nothing beats 30.** Both known mechanisms are now exactly minimal, within the search ranges
stated under "What is and is not covered".

| mechanism | result |
|---|---|
| `\|C\| = 4` braced rhombus (H30 type, infinitesimally rigid) | H30's rhombus is the **unique** legal mechanism over all 237 anchor classes, and its minimum lattice part is **exactly 26** sites, so **n = 30** exactly. |
| taut chain (E30 type, rigid but singular) | `k = 6` is forced, `Q − P = (3,5)` is forced up to symmetry, and the minimum body is **exactly 24** sites, so **n = 30** exactly. |

Both minima are attained by the published examples, and in both cases the search rediscovers the
published body site-for-site without being given it.

## Files

| file | what it is |
|---|---|
| `Lattice.lean` | Site arithmetic (`eN`), the 12 lattice symmetries, the exact integer rank of the rigidity matrix in the affine `(a,b)` coordinates, floating-point plane geometry, and `z⁶ − 64` (the frame criterion of `docs/offlattice.md` Theorem 2). Holds the `import`s, so it must come first. |
| `Body.lean` | Minimum rigid lattice sets inside a punctured window: an exact node-weighted Steiner tree, the **run bound** (see below), a Steiner/median bound on the sites still needed, and a branch and bound that is exact when it completes. Sets are `UInt64` masks, so a window holds at most 64 sites — every driver now refuses a wider one instead of printing nonsense. |
| `Corners.lean` | The same minimisation from the other side: exhaustive minimum-**corner** search over edge-connected cell families (polyiamonds) in the window, with the anchor set selectable, which is what bounds the "two bodies joined by bars" and "anchor hung off the body" variants. |
| `Rhombus.lean` | The `\|C\| = 4` case-(b) search: enumeration of anchor 4-cycles up to translation, the 12 lattice symmetries and D₄; the closure function `F(θ) = \|w₃ − x₃\|² − 4` on eight sign branches; the geometric tests; the exact detection of lattice closures; and the **flat audit**. |
| `Interval.lean` | Rational interval arithmetic at `2^160` (same scheme as `explore/offlattice/adversary/H30CertI.lean`) and `certify`, which brackets the root, proves a sign change (so an exact root exists by the intermediate value theorem), encloses `w₁ … w₄`, and certifies the diagonals, clearances, off-latticeness and the nonsingularity of the 8×8 ring matrix. |
| `Chain.lean` | E30-type taut chains, entirely in exact integer arithmetic: `49 d² = (14a + 7b − 11j)² + 3(7b − 5j)²` for the clearance between a body site and the `j`-th chain circle. |
| `Main.lean` | Drivers: `count`, `h30`, `tuple`, `ring`, `corner`, `chain`, `scan`. |

## The three things that make this work

### 1. The combinatorics of `|C| = 4` are forced

For an infinitesimally rigid case-(b) arrangement, let `C` be a connected cluster of free circles
off `L`. `docs/offlattice.md` Theorem 5 and Lemma 4 give

    e(C) + e(C,L) ≥ 2|C|,   e(C) ≤ 2|C| − 4,   e(C,L) ≤ |C|,

so at `|C| = 4` all three are tight: the four free circles form a **side-2 rhombus** and each is
tethered to exactly one body circle. Two elementary facts then make the search finite:

* a closed side-2 quadrilateral is automatically a rhombus (centrally symmetric, perpendicular
  diagonals), so `|w₁w₃|² + |w₂w₄|² = 16` and, with no overlap, both diagonals lie in `[2, 2√3]`;
* hence `|xᵢ − xᵢ₊₁| ≤ 6` for adjacent anchors (`eN ≤ 9`) and `|x₁ − x₃| ≤ 4 + 2√3 < 7.47` for
  opposite ones (`eN ≤ 13`). Adjacent anchors must differ (equal ones would make a triangle);
  opposite anchors may coincide. That leaves **237 anchor classes**, and the scan finds exactly
  **one** legal closure among them: H30's.

Also: every side-2 rhombus *on* the lattice has a diagonal of exactly 2, i.e. contains a
triangle. So a triangle-free closed rhombus is never a lattice rhombus, one of its edges leaves
the lattice directions, and the arrangement is off the lattice by the frame criterion. The
`z⁶ − 64` test is computed anyway, as a check.

### 2. The run bound

Every contact of a lattice set points along one of the three lattice directions, and along one
line in one direction the set is a union of maximal runs, a run of `p` sites carrying `p − 1`
contacts. Summing over the three directions gives the **exact identity**

    e(S) = 3·|S| − R₁(S) − R₂(S) − R₃(S),

`R_d` being the number of maximal runs along the lines of direction `d` (lines of constant `b`,
of constant `a`, and of constant `a + b`). Infinitesimal rigidity needs `e ≥ 2|S| − 3`, hence

    |S| ≥ R₁ + R₂ + R₃ − 3.

H30's own body makes this tight: 26 sites, 49 contacts, `ΣR = 78 − 49 = 29 = 26 + 3`. The bound is
monotone in both the chosen and the excluded sites, which is what the branch and bound needed:
the connectivity bounds say almost nothing about an *exclusion* branch, whereas excluding a site
splits a run and raises `ΣR` at once. Adding it is what carried the site search from `m ≤ 20` to
`m ≤ 25` — the whole gap between the previous lower bound and H30's body.

By hand, the same identity shows the hole in H30's window already forces three run splits (the
anchor pairs `(0,0),(3,0)` on `b = 0`, `(0,0),(2,-2)` on `a + b = 0`, and `(1,2),(3,0)` on
`a + b = 3` each straddle hole sites), so every candidate body satisfies
`m ≥ Δa + Δb + Δ(a+b) + 3`.

### 3. The flat audit

The scan finds closures as sign changes of `F(θ)`, and 39 of the 237 anchor classes have branches
on which `F ≡ 0` — the closed rhombus *flexes* there, so float noise produces a sign change at
almost every step (152446 of them at 32000 steps per branch). Discarding those on a slope
threshold is the one place where a tolerance could silently throw away the answer, so the
threshold is no longer trusted: **every** discarded flat sign change is built into a candidate
and put through the same tests. None of them is even a legal arrangement, let alone a rigid one —
the closest comes to `worstFail = +0.0034` at 32000 steps and `+0.00083` at 131072, i.e. it
overlaps or contains a triangle by a wide margin.

This makes the threshold **not load-bearing in either direction**. A flat branch wrongly called
transversal is bisected and then fails the tests like any other closure. A transversal root
wrongly called flat is still built — at the midpoint of its bracketing step, which at 131072
steps is within `2.4e-5` of the root — and still put through `Cand.ok`; since the one real answer
clears the geometric tests by margins of 3.7 and 6.7, such a candidate would show up in the
`flatOk` count, and `flatOk = 0`. (For the record the two populations do not overlap either, but
they are converging as the resolution rises: `0.000975` against `0.001104` at 32000 steps,
`0.000998` against `0.001019` at 131072, around the `0.001` cut. Hence the audit rather than the
threshold.)

Among the *transversal* closures that are rejected, the smallest failure margin is `0.79`, so the
`1e-7` screening tolerance is nowhere near binding.

**Resolution stability.** The whole scan was run at 32000 and at 131072 `θ`-steps per branch. The
closure census changes (16173 against 65854 transversal closures, 195 against 198 exact lattice
rhombi, 36 against 37 triangle-free) but the answer does not: **one** legal closure, the same
anchor class, the same `θ`, and the same diagonals, clearance, `z⁶ − 64` and `det8` to every
printed digit.

## What is and is not covered

**Covered, exhaustively** (all `[computed-exact]` except the closure root itself, which is
`[computed-interval]`):

* all 237 anchor 4-cycle classes, all 8 sign branches, `|C| = 4`;
* for H30's anchors, the **exact** minimum infinitesimally rigid lattice site set inside the
  radius-8 window about the ring centre (52 allowed sites): started from an upper bound of 27 the
  branch and bound runs to completion in 34,993,977 nodes and returns 26, H30's own body
  site-for-site. This is over *any* structure, not just polyiamonds, so two bodies joined by bars
  and anchors hung off the body as Henneberg-1 sites are included. `caseb verify` is the
  soundness check for the bounds the search prunes on;
* the same at radius 7 (40 allowed sites), with the same answer;
* for the E30 chain, every infinitesimally rigid lattice set of at most 23 sites in the band
  `49·perp² ≤ 2100`, `−3 ≤ along ≤ 17` (62 allowed sites).

**Not covered:**

* **`|C| ≥ 5`.** At `|C| = 5` the bounds stop being tight. They give
  `e(C) + e(C,L) ≥ 10`, `e(C) ≤ 6`, `e(C,L) ≤ 5`, so `e(C) ∈ {5, 6}` and there are at least three
  shapes — `C₅` with five tethers, `C₄` with a pendant and five tethers, and `K₂,₃` with four
  tethers — instead of the single forced one. The cluster is no longer rigid-by-shape either, so
  the closure is a system in more unknowns and the search needs a new idea. To beat 30 such an
  arrangement would need a body of at most 24 sites, which is not obviously out of reach.
* **Singular (non-infinitesimally-rigid) case (b)** other than the E30 chain family. Theorem 5's
  `|C| ≥ 4` and the cycle both assume infinitesimal rigidity; E30's own cluster is a 6-circle
  *path*, which the rhombus search cannot see. This is the widest remaining gap.
* **Sites outside the window.** The site masks are `UInt64`, so a window holds at most 64 sites;
  radius 8 is the largest disc that fits. The run bound confines a 25-site body to
  `Δa, Δb, Δ(a+b) ≤ 11`, which is a much larger hexagon than the radius-8 disc, so a body that
  makes a long excursion and returns is not formally excluded. A core has minimum degree 3 (a
  degree-2 circle is either removable or collinear, hence infinitesimally flexible), so an
  excursion cannot be a one-site-wide tentacle and must pay about twice its length in sites; the
  excursion also pays its length in the run bound. That makes an excursion look hopeless but is
  not a proof.
* **`k ≥ 12` chains** are excluded only by hand, from `m ≥ Δa + Δb + Δ(a+b)`: `k = 12` needs
  `Q − P` of norm 169 off the lattice directions, e.g. `(7,8)`, giving `m ≥ 30` and `n ≥ 42`;
  `k = 13` needs norm 196, e.g. `(−6,16)`, giving `m ≥ 32` and `n ≥ 45`; and `k ≥ 14` gives
  `n ≥ 2k + 2 ≥ 30` from the span alone. Only `k = 6` was searched by machine.

## Running

```bash
bash explore/caseb/build.sh [outdir]      # default outdir: explore/caseb/out
explore/caseb/out/caseb count             # the 237 anchor classes
explore/caseb/out/caseb h30               # reproduce H30 from docs/offlattice.md §8
explore/caseb/out/caseb scan 32000        # the whole |C| = 4 search, with the flat audit
explore/caseb/out/caseb ring 1 2 3 0 2 -2 40000 8 30 400 400000000   # H30's ring: min body = 26
explore/caseb/out/caseb corner 1 2 3 0 2 -2 40000 8 30 2000000000 0  # min corners, all 15 anchor subsets
explore/caseb/out/caseb chain 2100 21 30 400 300000000               # E30-type taut chains: min body = 24
explore/caseb/out/caseb verify 40000 8 2000000000                    # soundness check of the bounds
```

`build.sh` concatenates the files (`Lattice.lean` first, since it holds the imports) and runs
`lake env lean --root=<outdir> -c` then `lake env leanc -O3`, as
`explore/offlattice/catalogue/build.sh` does. It never calls `lake build`. To typecheck without
compiling, run `lake env lean --root=<outdir> <outdir>/caseb.lean` on the concatenated file.

Timings on one core: `count` and `corner` seconds, `h30` under a second, `scan 32000` about
2 min, `ring … 8 …` about 3½ min, `verify` about 3½ min, `chain` about 2 min.
