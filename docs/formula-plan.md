# Toward a general formula for the number of rigid arrangements: plan

> **Status (2026-10-15).** This is a plan; none of the work has started. It draws on four investigations (literature, an exploratory census to n = 25, structure, exactly countable sub-families) and three competing plans. The judge checked these against each other and redid some of the computations (Appendix A). The plan contains no new Lean theorem.

**Notation.**

- **a(n):** rigid arrangements of n unit circles, counted up to relabeling plus isometry, reflections allowed.
- **a_L(n):** the same, restricted to centres on the triangular lattice. By definition this is OEIS A171604.
- **f_L(n):** lattice sets counted up to translation only (the "fixed" count, about 12·a_L(n)).
- **Removable circle:** exactly two contacts, less than 4 apart.
- **Core:** has no removable circle.
- **Henneberg step:** add a circle touching at least two circles.
- **Irreducible core:** no single deletion leaves a rigid set.
- **Singular:** rigid but not infinitesimally rigid.
- **SAT ("saturated"; proposed new name "triangle-closed"):** the lattice triangles spanned by the set are edge-connected and cover every circle.
- **Exceptions:** rigid lattice sets that are not SAT.

**Status tags.**

| tag | meaning |
|---|---|
| [Lean] | theorem in the repository, kernel-checked |
| [paper] | complete argument on paper, not formalized |
| [computed] | exploratory Lean computation (`#eval` or compiled Lean), not kernel-checked |
| [cited] | taken from the literature |
| [conj] | conjecture with evidence |
| [spec] | speculation |

---

## 1. Where we stand

### 1.1 The counts

| n | a(n), all arrangements | a_L(n), lattice | status of a_L(n) | f_L(n) [computed] |
|---|---|---|---|---|
| 1, 2 | 1, 1 [Lean] | 1, 1 | [Lean] | – |
| 3 | 1 [Lean] | 1 | [Lean] | 2 |
| 4 | 1 [Lean] | 1 | [Lean] | 3 |
| 5 | 1 [Lean] | 1 | [Lean] | 6 |
| 6 | 3 [Lean] | 3 | [Lean] | 14 |
| 7 | 4 [Lean] | 4 | [Lean] | 31 |
| 8 | 9 [Lean] | 9 | [Lean] | 69 |
| 9 | ≥ 16 [Lean]; = 16 [conj] | 16 | [computed]; ≥ 16 [Lean] | 151 |
| 10 | ≥ 35 [Lean]; = 35 [conj] | 35 | [computed]; ≥ 35 [Lean] | 335 |
| 11 | ≥ 70 [Lean] (69 lattice + O11); = 70 [conj] | 69 | [computed]; ≥ 69 [Lean] | 747 |
| 12 | ≥ 155 [Lean]; ≥ 160 [computed, floating point]; = 160 [conj] | 155 | [computed]; ≥ 155 [Lean] | 1671 |
| 13 | ≥ 357 [computed, floating point] | 328 | [computed] by several independent programs, incl. brute force over all 3,274,826 connected 13-site sets | 3749 |
| 14 | ≥ 874 [same] | 740 | [computed] by 3 programs, incl. unpruned brute force (rank test) | 8487 |
| 15 | ≥ 2209 [same] | 1655 | [computed], as for 14 | 19432 |
| 16 | ≥ 5916 [same] | 3816 | [computed] by 2 pipelines that share one core-search code; SAT part confirmed independently | 44882 |
| 17 | ≥ 16290 [same] | 8761 | [computed], as for 16 | 104220 |
| 18 | ≥ a_L(18) | 20411 | [computed] by 2 pipelines with a shared core search | 242810 |
| 19 | ≥ a_L(19) | 47461 | [computed], as for 18 | 567395 |
| 20 | ≥ a_L(20) | 111219 | [computed] by orderly + hash pipelines (shared core search) | not computed |
| 21 | | 260968 | [computed], as for 20 | |
| 22 | | 615428 | [computed], as for 20 | |
| 23 | | 1454493 | [computed] by a single pipeline | |
| 24 | | 3449768 | [computed] by a single pipeline | |
| 25 | | 8198486 | [computed] by a single pipeline; 4 candidates decided by higher-order analysis, one of them rigid only at third order | |

**Caveats.**

- **Independence.** All counts for n ≥ 16 rest on one pruned core-search code lineage. The judge's re-run to n = 19 used the same code: it reproduced every free and fixed count above, but it is a reproduction, not an independent check.
  - Independent confirmation exists only for n ≤ 15 (unpruned brute force) and for the SAT part through n = 17 (a separate polyiamond enumerator).
  - The pruning rule has not been machine-checked beyond n = 13.
- **Cited theorems.** From n = 15, some flexible/rigid verdicts use cited theorems: Asimow–Roth for regular points, and Connelly–Whiteley for second-order and prestress rigidity.
- **Off-lattice lower bounds.** The bounds for n = 11..17 come from floating-point searches over restricted families:
  - two lattice bodies with a hinge and a bar;
  - three-body rings;
  - their Henneberg closures.

  The off-lattice counts are 1, 5, 29, 134, 554, 2100, 7529.
- **Exact sequence.** The exact sequence is the Lean theorem 1, 1, 1, 1, 1, 3, 4, 9 for n ≤ 8.
- **n = 9.** A research-phase hand argument that every rigid arrangement with at most 9 circles lies on the lattice is mentioned in the journal (2026-10-14). It has not been refereed or formalized.

### 1.2 Anatomy of the lattice counts [computed]

For n ≤ 12 every rigid lattice set is SAT.

| n | a_L | SAT | exceptions (gap circle / triangle-covered but not one polyiamond) | exception share | exactly 2n−3 contacts | cores | irreducible cores | singular |
|---|---|---|---|---|---|---|---|---|
| 13 | 328 | 327 | 1 (1/0) | 0.3% | 177 | 2 | 0 | 0 |
| 14 | 740 | 734 | 6 (4/2) | 0.8% | 376 | 3 | 1 | 0 |
| 15 | 1655 | 1615 | 40 (21/19) | 2.4% | 774 | 5 | 1 | 0 |
| 16 | 3816 | 3657 | 159 (68/91) | 4.2% | 1674 | 10 | 0 | 0 |
| 17 | 8761 | 8206 | 555 (212/343) | 6.3% | 3550 | 19 | 0 | 0 |
| 18 | 20411 | 18703 | 1708 (588/1120) | 8.4% | 7627 | 32 | 3 | 1 |
| 19 | 47461 | 42488 | 4973 (1614/3359) | 10.5% | 16207 | 58 | 5 | 7 |
| 20 | 111219 | 97258 | 13961 (4298/9663) | 12.6% | 34932 | 128 | 5 | 48 |
| 21 | 260968 | 222604 | 38364 (11388/26976) | 14.7% | 75564 | 236 | 19 | 223 |
| 22 | 615428 | 511589 | 103839 (29928/73911) | 16.9% | 165101 | 501 | 29 | 901 |
| 23 | 1454493 | 1176621 | 277872 (78392/199480) | 19.1% | 361465 | 999 | 49 | 3179 |
| 24 | 3449768 | 2713236 | 736532 (204103/532429) | 21.3% | 794402 | 2078 | 87 | 10467 |
| 25 | 8198486 | 6263047 | 1935439 (528726/1406713) | 23.6% | 1746607 | 4284 | 196 | 32620 |

**Cores** occur at n = 7 (the flower), 10 and 12 (two of them). Below n = 14 every rigid lattice set is in the Henneberg closure of a triangle.

**Landmarks.**

| n | name | what it is |
|---|---|---|
| 13 | R13 | a circle in no triangle |
| 14 | R14 | first irreducible core: two triangle-bodies, a hinge and a bar |
| 15 | I15 | three-body ring |
| 18 | sing18 | first singular set |
| 20 | S20 | first irreducible singular core; second-order rigid |
| 21 | S21a | rigid with fewer than 2n−3 contacts: a taut straight chain |
| 24 | F24 | flexible, by a new "parallel-rotation" flex |
| 25 | U1 | rigid only at third order |

### 1.3 Growth rates

| quantity | value | status |
|---|---|---|
| r_n = a_L(n)/a_L(n−1) | 2.3434 (n=20), 2.3718 (24), 2.3765 (25); still rising | [computed] |
| r_n·n/(n−1) (the θ = 1 correction) | 2.467 (n=20) → 2.476 (n=25); rising slowly | [computed] |
| two-step (even/odd) extrapolants | 2.50–2.53 for n = 20..25 | [computed] |
| least-squares fits of log a = c + n log μ + θ log n | μ = 2.53–2.60 with θ = −1.5 to −2; μ and θ are not separable on this range | [computed] |
| **μ_L = lim a_L(n)^{1/n}** | **probably 2.45–2.65** | [conj]; existence [paper], see WS1 |
| SAT subclass | r_n·n/(n−1) flat at 2.404–2.410 for n = 18..25, so μ_s ≈ 2.40 if θ = 1 | [computed] numbers, [conj] limit |
| exceptions | local ratio 2.81 (n=20) → 2.63 (n=25), falling | [computed] |
| core-free class (Henneberg closure of one contact) | ≈ 2.1 | [conj] |
| polyiamonds, per cell | ≈ 3.036 (Lean ratio analysis of 75 terms of A001420), 3.04 ± 0.02 (Sykes–Glen); proved 2.8578 ≤ λ ≤ 3.6108 | [cited] + [computed] |
| polyhexes (connected lattice site sets) | 5.1831; proved 4.8049 ≤ μ ≤ 5.9047 | [cited] |
| rigorous bounds for μ_L | 1.75 ≤ μ_L (from 1671 fixed sets at n = 12) and μ_L ≤ 5.9047 (polyhex bound) | lower: [paper] (WS1 makes it [Lean]); upper: [cited] |
| all arrangements | a(n) ≤ 15552^n (Milnor's bound on components of real varieties, times planar-map counting); a(n) ≥ a_L(n) | upper: [paper sketch]; lower: [Lean] for n ≤ 12, otherwise [computed] |

### 1.4 Corrections to statements in the docs or the brief

1. **"Polyiamond growth constant ≈ 2.84" is wrong as a growth constant.**
   - 2.8424 was the old rigorous lower bound (Barequet–Shalah–Zheng), since improved to 2.8578 (Bui 2023). The raw ratio of A000577 is also near 2.84 at 15–16 cells (73983/26166 = 2.83, 211297/73983 = 2.86).
   - The best estimate is ≈ 3.04 per cell [cited, computed].
   - Rigid lattice arrangements grow much more slowly: about 2.5 per circle [conj].
2. **The literature report's "match" with OEIS A284373 is not a match.**
   - The judge counted max-contact (Harborth-extremal) rigid lattice sets for n = 3..19: 1,1,1,3,1,1,4,1,2,1,**4**,1,**4**,1,**9**,3,1 [computed].
   - A284373 (fetched 2026-10-15) has **2**, **3**, **6** at n = 13, 15, 17.
   - Do not cite it as matching. The discrepancy is unexplained; probably A284373 counts a narrower class.
3. **The first non-saturated polyiamond corner set has exactly 26 circles** (judge, [computed]). This is a polyiamond whose corners span an extra triangle sharing no edge with the others.
   - The census found none for n ≤ 25.
   - The judge built one with 26 corners: a 24-cell edge-connected polyiamond (two 13-cell arcs) whose corner set spans 25 triangles. These split into a 24-triangle component covering all 26 circles, plus the isolated triangle {(0,0),(1,0),(0,1)}.
   - It is rigid by `IsPolyiamond.isRigid` [Lean theorem; this instance not yet stated in Lean].
   - Sites: (2,−1),(1,0),(2,0),(3,−1),(3,0),(2,1),(3,1),(2,2),(1,2),(1,3),(0,3),(0,2),(−1,3),(−1,2),(0,1),(−2,3),(−2,2),(−3,3),(−3,2),(−2,1),(−3,1),(−2,0),(−1,0),(−1,−1),(0,−1),(0,0).
   - File: `explore/NonSaturated26.lean`.
   - Plan 1's estimate "26 ≤ n ≤ 33, probably near 33" is superseded.
4. **The structure report's μ_L ≈ 2.46 is superseded.** It came from n ≤ 19, and the θ = 1-corrected ratio is already 2.476 at n = 25 and still rising.
5. **Naming.** "Saturated polyform" already means fully leafed tree-like polyforms (Blondin Massé–de Carufel–Goupil). Proposed rename: "triangle-closed polyiamond".
6. **Where the polyiamond/hexomino analogy breaks, by first n.**
   - n = 8: the count mismatch (9 vs 12 hexiamonds), from shared corner sets [Lean].
   - n = 11: off the lattice (O11) [Lean].
   - n = 13: a circle in no triangle (R13) [Lean].
   - n = 14: triangle-covered but not one polyiamond (R14) [computed].
   - n = 18: singular [Lean example; first occurrence computed].
   - n = 20: a two-body three-bar core is rigid but not built by merging clusters; a Laman-rigid set that shears [computed].
   - n = 21: rigid with fewer than 2n−3 contacts [computed].
   - n = 26: a polyiamond corner set whose triangles are not edge-connected [computed].

   Quantitatively, the SAT share is 76% at n = 25 and falls about 2.3 points per n. a_L(n) divided by the number of polyiamonds with n−2 cells decays roughly like 0.82^n [conj].

---

## 2. What kind of answer to expect

**A closed formula, or even an algebraic or D-finite generating function, is very unlikely** [spec, well supported].

1. **The lattice part is a subclass of lattice animals.** a_L(n) counts certain polyhexes (connected sets of triangular-lattice sites).
   - No closed formula is known for any nontrivial two-dimensional animal class [cited]. The solved classes (directed, convex, column-convex, fixed-width strips, tree-like) are all "thin".
   - Our series shows the animal signature: slowly creeping ratios, consistent with C·μ^n·n^(−1) [computed].
2. **Rigidity is not a local property.**
   - Exceptions such as R14 (two bodies, a hinge and a bar) depend on global geometry.
   - Singular sets need second- and even third-order analysis (U1 at n = 25) [computed].
   - Deciding local rigidity of a given penny configuration is ∀ℝ-complete in general (Lubiw–Schaefer) [cited].
3. **Off-lattice arrangements involve continuous angles** from n = 11 (O11, angle arccos(5/6)) [Lean]. Counting them exactly means solving a polynomial system for every body graph.
   - Floating-point lower bounds make them a large share by n ≈ 17 [computed, restricted families].
   - That they eventually dominate is [spec].
4. **The subclasses that do have formulas are exponentially rare.**
   - All exactly solved sub-families have growth ≤ φ ≈ 1.618 (§5).
   - Even SAT (≈ 2.40) seems to grow strictly slower than the total (≳ 2.48) [conj].

**What can realistically be delivered, from most to least certain:**

- **(A) Exact values.**
  - [Lean] for all arrangements through n = 8.
  - Lattice-exact [computed] through n = 25, realistically 28.
  - Certified lattice lower bounds [Lean] through n ≈ 17.
  - All-arrangement exact values at n = 9, 10 only if a new core-exclusion idea works (WS9).
- **(B) Exact structure.**
  - The canonical-core partition a(n) = f(n) + Σ_K E_K(n): every rigid arrangement peels uniquely to its core K, and f counts the core-free ones [paper].
  - The line-sum criterion for infinitesimal rigidity on the lattice [paper].
  - The cluster-merge rules R1/R2 [paper]. These turn rigidity into graph combinatorics for every lattice set with n ≤ 19 [computed].
- **(C) Exactly solvable sub-families** with rational generating functions. These give certified exponential lower bounds valid for all n (§5).
- **(D) A theorem that the lattice growth constant μ_L exists**, with a(n) ≤ 2μ_L^n and a certified lower bound on μ_L (WS1). This is the most valuable provable "formula-like" statement, and it is within reach.
- **(E) An asymptotic conjecture with an error bar:** a_L(n) ~ C·μ_L^n·n^(−1), μ_L ≈ 2.5 ± 0.1. It becomes falsifiable by pre-registered predictions for n = 26–28.
- **(F) A quantitative statement of where the polyiamond analogy fails.** Each failure mode has full growth rate μ_L [provable, WS5]. Polyiamond-like sets are an exponentially small share [conj].

---

## 3. Workstreams (in priority order)

Effort is measured in "sessions": one focused working session of an agent. Lean statements are targets, not existing code.

### WS1. The lattice growth constant as a theorem (priority 1)

- **Goal.** Prove in Lean:
  - μ_L = lim f_L(n)^{1/n} exists;
  - f_L(n) ≤ 2·μ_L^n for all n ≥ 3;
  - μ_L ≥ (f_L(N)/2)^{1/N} for every N, giving explicit certified bounds;
  - transfers to free classes and to all arrangements: (f_L(n)/12) ≤ #RigidClasses n.
- **Method: concatenation.** This is Plan 3's lemma; the judge re-derived its case analysis.
  - **Setup.** Order sites by row, then column. Let t be the last site of A. Translate B so that its first site lands on t. The two pieces share exactly t, and A lies before t, B after.
  - **Hinge case.** If any contact joins A∖t to B∖t, the union is rigid by the hinge-and-bar lemma (`IsRigid.of_hinge_of_union`, Lean).
  - **Connector case.** Otherwise, since t has at least 2 neighbours on each side, only two local pictures are possible. In the lattice coordinates (a, b) of the site at 2a + b(1+i√3), t's neighbours are L=(−1,0), D=(0,−1), DR=(1,−1) (earlier in the order) and R=(1,0), U=(0,1), UL=(−1,1) (later).
    1. A has {L, D} and B has {R, U}: add one connector circle at DR.
    2. A has {D, DR} and B has {U, UL}: add one connector circle at L.

    The connector is a Henneberg step on A followed by hinge + bar, so the union is rigid.
  - **Decoding.** t is the m-th (or (m+1)-th) site of the union. In the connector case, the connector is DR iff R is occupied. *(Plan 3's sketch omitted this detail: both L and DR are present in both pictures.)*
  - **Result.** f_L(m)·f_L(n) ≤ f_L(m+n−1) + f_L(m+n).
  - **Monotonicity.** f_L(n) ≤ f_L(n+1): add UL if L is occupied, else R.
  - **Conclusion.** Apply Fekete's lemma, which Mathlib has as `Submultiplicative.tendsto_lim`, `lim_le_rpow`, `apply_mul_add_le`, to u(n) = 2/f_L(n), padded to 1 for n < 3. This is valid because f_L(3) = 2.
- **Numbers this gives** (the judge recomputed each):

  | N | f_L(N) | μ_L ≥ | status |
  |---|---|---|---|
  | 12 | 1671 | 1.7518 | kernel-feasible |
  | 13 | 3749 | 1.785 | |
  | 14 | 8487 | 1.816 | |
  | 16 | 44882 | 1.870 | |
  | 19 | 567395 | 1.9365 | needs a sound generator |
  | 23 | ≈ 1.74·10⁷ | 2.003 | needs `native_decide` |
  | 25 | ≈ 9.8·10⁷ | ≈ 2.03 | needs `native_decide` |

  Honest note: these rigorous bounds are far below the estimate (≈ 2.5).
- **Deliverables.** New file `RigidArrangements/Growth.lean`:
  ```lean
  def fixedRigid (n : ℕ) : Set (Finset (ℤ × ℤ))   -- card n, lex-least site (0,0), (ofSites S).IsRigid
  theorem fixedRigid_finite (n : ℕ) : (fixedRigid n).Finite        -- via IsRigid.connected
  noncomputable def fixedCount (n : ℕ) : ℕ := Nat.card (fixedRigid n)
  theorem fixedCount_le_succ (hn : 3 ≤ n) : fixedCount n ≤ fixedCount (n + 1)
  theorem fixedCount_mul_le (hm : 3 ≤ m) (hn : 3 ≤ n) :
      fixedCount m * fixedCount n ≤ fixedCount (m + n - 1) + fixedCount (m + n)
  theorem fixedCount_le_pow (n : ℕ) : fixedCount n ≤ 36 ^ n      -- closed DFS walk of a spanning tree
  theorem exists_latticeGrowth : ∃ μ : ℝ, 1 < μ ∧ μ ≤ 36 ∧
      Tendsto (fun n => (fixedCount n : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 μ) ∧
      (∀ n ≥ 3, (fixedCount n : ℝ) ≤ 2 * μ ^ n) ∧
      ∀ n ≥ 3, ((fixedCount n : ℝ) / 2) ^ (n : ℝ)⁻¹ ≤ μ
  theorem fixedCount_twelve_ge : 1671 ≤ fixedCount 12            -- latticeCatalogue12 × 12 latSym, decide
  theorem sitesCongr_of_iso {S T : Finset (ℤ × ℤ)} (hS : ∃ v ∈ S, ∃ w ∈ S, eNorm (v - w) = 1)
      (h : (Arrangement.ofSites S).Iso (Arrangement.ofSites T)) : SitesCongr S T
  theorem fixedCount_le_twelve_mul (n : ℕ) :
      (fixedCount n : ℕ∞) ≤ 12 * ENat.card (RigidClasses n)
  ```
  Also a journal entry: "rigid lattice arrangements have a growth constant".
- **Effort.** 4–6 sessions, about 1,200–1,800 lines.
- **Risk.** Low on the mathematics. Medium on engineering:
  - Finset reindexing with `comap`;
  - `sitesCongr_of_iso` is the one new geometric lemma: an isometry carrying a lattice set with a unit contact onto another lattice set is a lattice symmetry plus a translation.
- **First step.** Create `Growth.lean` with `fixedRigid` and prove `fixedCount_le_succ`, using `IsRigid.touchesTwo` at the last site and `IsRigid.addCircle`. In parallel, state the neighbour-pattern case split as a Boolean function over the subsets of {L, D, DR} × {R, U, UL} and close it by `decide`.

### WS2. Lattice data to n = 28 and series analysis with pre-registered predictions (priority 1)

- **Goal.**
  - Exploratory-exact a_L(n) and f_L(n) for n ≤ 28, with the full statistics of §1.2.
  - A defensible estimate μ_L = 2.5x ± 0.0y.
  - A test of θ = 1.
- **Method.** Start from `explore/RigidEnum.lean`.
  1. **Depth-first orderly generation** (Plan 1). The roots are a single contact plus every rigid core. A child is kept iff the added circle is the child's canonical removable circle. Memory becomes O(n); storing level 28 would otherwise take about 10 GB on a 15 GB machine [spec].
  2. **Henneberg test for cores by peel-and-lookup.** C∖v is rigid iff its peeling ends at a contact or at an entry of the table of rigid cores. The judge checked this: deleting a circle with exactly two non-opposite contacts preserves both rigidity and flexibility.
  3. **Core search.** Run it on canonical representatives only (a 12-fold saving). Run the second-order test only at non-regular points.
  4. **Per-node stabilizers,** giving fixed, one-sided and achiral counts.
  5. **Analysis in Lean.** Ratio, Neville and two-step extrapolants and first-order differential approximants (Float plus exact ℚ), on the fixed series and on every subclass.
  6. **A crossover model:** total = SAT + Σ_k defects. This uses the apparently converged SAT growth to pin down μ_L.
- **Pre-registered predictions** (judge, from the even/odd trend):

  | quantity | prediction |
  |---|---|
  | a_L(26) | 1.954·10⁷ ± 0.3% |
  | a_L(27) | 4.67·10⁷ ± 0.5% |
  | SAT(26) | ≈ 1.449·10⁷ |
  | exception share at 26 | 25.8 ± 0.3% (so Plan 3's "passes 26%" is expected to fail narrowly) |
  | cores(26) | ≈ 8,900 ± 600 |
  | singular(26) | ≈ 96,000 ± 8,000 |
  | non-saturated polyiamond corner sets at 26 | at least 1, probably at most 5 |
- **Deliverables.**
  - A b-file for a_L and f_L up to n ≤ 28.
  - The tables of §1.2 extended.
  - The complete list of rigid cores up to n ≈ 27, each with its certificate type.
  - An estimates table with error bars.
  - Prediction outcomes recorded in the journal.
- **Effort.** 2 sessions to develop. About 1–1.5 days of compute for n = 26–28 on 4 threads (the core search grows ×3.3 per level; 949 s at n = 25).
- **Risk.**
  - Memory, until the depth-first mode works.
  - New undecided singular types at n ≥ 26: report them as intervals.
  - Completeness of the pruned core search for n > 13 is argued but not machine-checked. Mitigation: an unpruned spot check on random subtrees.
- **First step.** Add an `orderlyDFS N` mode, seeded with the core list from `explore/orderly25.txt`. Acceptance test: identical a(n), singular and core counts for n ≤ 22, and fixed counts equal to 3749 … 567395 for n ≤ 19.

### WS3. Structure theorems: canonical core, cluster calculus, line-sum criterion (priority 2)

- **Goal.** Turn the exact structural facts into Lean.

**(i) Canonical core** (`Peel.lean`).
- Peeling removable circles is confluent. Every rigid arrangement A has a well-defined core K(A): a single contact, or the largest rigid core inside A.
- Peeling leaves the excess (contacts − (2n−3)) unchanged.
- A lies on the lattice iff K(A) is a contact or lies on the lattice.
- So **off-lattice arrangements are exactly the Henneberg closures of off-lattice cores** [paper; two investigations agree].

**(ii) Cluster calculus** (`Cluster.lean`).
- A set S is *rigid inside A* when every small contact-keeping motion keeps all distances within S. The rules:
  - **R1:** two clusters sharing ≥ 2 circles merge.
  - **R2:** three clusters pairwise sharing three distinct circles merge.
- Both are sound in every realization, collinear hinges included: a degenerate triangle is still determined by its side lengths (judge checked the argument).
- R2 contains Henneberg steps (including straight ones), hinge + bar, and three-body rings.
- For n ≤ 19 every rigid lattice set reduces to a single cluster by R1/R2 [computed]. At n = 20 exactly 3 classes do not [computed].

**(iii) Line-sum criterion** (`Lines.lean`).
- A *line* is a maximal straight run of contacts in one of the three directions, singletons included. There are L = 3n − |E| lines.
- Infinitesimal motions correspond to line values x with x_{ℓ0} − x_{ℓ1} + x_{ℓ2} = 0 at every site. The judge re-derived this from d₀ − d₁ + d₂ = 0.
- Hence rank R = |E| − n + rank M, and the set is infinitesimally rigid iff rank M = L − 3.

**Deliverables.**
```lean
-- Peel.lean
def Arrangement.RemovableIn (A : Arrangement ι) (S : Finset ι) (w : ι) : Prop
theorem IsRigid.peels_terminal_unique (h : A.IsRigid) (h₁ : A.Peels univ K₁) (h₂ : A.Peels univ K₂)
    (t₁ : A.IsCoreSet K₁) (t₂ : A.IsCoreSet K₂) (hK : 3 ≤ K₁.card) : K₁ = K₂
theorem IsRigid.isLattice_of_core_isLattice : …
-- Cluster.lean
def Arrangement.RigidIn (A : Arrangement ι) (S : Set ι) : Prop
theorem RigidIn.union_of_two (h₁ : A.RigidIn S) (h₂ : A.RigidIn T) (ha : a ∈ S ∩ T)
    (hb : b ∈ S ∩ T) (hab : a ≠ b) : A.RigidIn (S ∪ T)
theorem RigidIn.union_of_ring … : A.RigidIn (S₁ ∪ S₂ ∪ S₃)
def checkMerge (n : ℕ) (E : List (ℕ × ℕ)) (s : List MergeStep) : Bool
theorem Arrangement.isRigid_of_checkMerge (hE : ∀ e ∈ E, Tangent A.center e.1 e.2)
    (h : checkMerge n E s = true) : A.IsRigid
theorem Arrangement.isRigid_r14 : …    theorem Arrangement.isRigid_i15 : …
-- Lines.lean
theorem isInfRigid_iff_lineRank (S : Finset (ℤ × ℤ)) (h : 2 ≤ S.card) :
    (Arrangement.ofSites S).IsInfRigid ↔ (lineMatrix S).rank + 3 = numLines S
```

- **Effort.** 5–8 sessions in total: (i) 1–2, (ii) 2, (iii) 2–3.
- **Risk.** Low to medium:
  - reindexing between Finset subtypes and `Fin n`;
  - in (iii), matrix rank over ℝ in Mathlib.
- **First step.** In `Peel.lean`, prove the persistence lemma. If w is removable in S, and T ⊆ S is rigid with w ∈ T and |T| ≥ 3, then w is removable in T (from `IsRigid.touchesTwo`). Also prove that two removable circles of a rigid set with ≥ 4 circles never touch.

### WS4. Exactly solvable families as theorems: certified exponential lower bounds for all n (priority 2)

- **Goal.** Lean theorems for the width-3 family, and explicit exponential lower bounds valid for every n:
  - width 3: ≈ 1.429^n;
  - combs: φ^n;
  - directed snakes: ≈ 1.513^n, if their validity for all n can be proved.

  These complement WS1, whose bound is larger but only asymptotic.
- **Method.**
  - **Width-3 characterization** [paper]: a spine of m ≥ 2 consecutive middle-row circles plus slot rules (C) and (E), §5.
    - Sufficiency by `IsPolyiamond.isRigid`.
    - Necessity by the rotation and shear flexes of `Flex.lean`.
    - Counting by a slot automaton and Burnside over the Klein group.
  - **Combs:** explicit build orders.
  - **Saturated snakes for n ≤ 17:** a `decide` over 2^13 words.
- **Deliverables.**
  ```lean
  structure ThreeRowWord where (m : ℕ) (slots : List (Bool × Bool))
  def ThreeRowWord.valid : ThreeRowWord → Bool
  def ThreeRowWord.sites : ThreeRowWord → Finset (ℤ × ℤ)
  theorem rigid_iff_threeRow (hS : ∀ p ∈ S, p.2 ∈ ({0,1,2} : Finset ℤ)) (h3 : usesAllRows S) :
      (Arrangement.ofSites S).IsRigid ↔ ∃ w t, w.valid ∧ S = (w.sites).image (· + (t, 0))
  theorem card_threeRow_fixed (n : ℕ) : threeRowFixed n = T3coeff n
  theorem card_rigidClasses_ge_comb (n : ℕ) (hn : 6 ≤ n) : (combClasses n : ℕ∞) ≤ ENat.card (RigidClasses n)
  ```
- **Effort.** 3–5 sessions.
- **Risk.** Medium:
  - the Burnside bookkeeping;
  - non-isomorphism needs `sitesCongr_of_iso` from WS1.
- **First step.** Write `ThreeRowWord.valid` and `sites`. Check by `#eval` that they reproduce T3's coefficients 1, 4, 10, 17, 25, 36, 53, 79, 114 for n = 4..12 (the judge re-expanded T3 by hand to n = 12).

### WS5. The polyiamond analogy, quantified (priority 2–3, after WS1)

- **Goal.** Theorems that each failure mode of the analogy has the full growth rate μ_L. The families concerned:
  - (i) gap-circle sets (R13 type);
  - (ii) triangle-covered sets that are not one polyiamond (R14 type);
  - (iii) singular sets (sing18 type);
  - (iv) off-lattice sets (O11 gadget).

  Also the n = 26 example as a Lean theorem.
- **Method.** Run the WS1 gluing with a fixed gadget G as the second factor. Orient G so that its special feature lies at least two rows above G's first site; the feature then survives gluing.
  - A gap circle stays in no triangle.
  - A taut circle keeps exactly two opposite contacts, so `not_isInfRigid_of_taut` applies.
  - For O11, exact non-overlap inequalities in ℚ(√3, √11) are needed.
- **Deliverables.**
  - `liminf (excCount n)^(1/n) ≥ μ_L`, and similarly for the other families.
  - `fixedCount n ≤ singCount (n + 17) + singCount (n + 18)`. *Plan 3's form `≤ 2·singCount (n+17)` needs a monotonicity of singCount that has not been shown.*
  - `nonsat26`: the 26-site set of §1.4 is the corner set of an edge-connected polyiamond, and its spanned triangles are not edge-connected (by `decide`).
  - For O11: an injection of lattice classes into off-lattice classes of size n + 10.
- **Effort.** 2–3 sessions for the lattice gadgets; 1–2 more for O11.
- **Risk.** Low for the lattice gadgets. Medium for O11: one O11 circle is only 0.577 above the hinge row, so some orientation or a connector is needed.
- **First step.** Extend the prototype `explore/Glue.lean`. For each of R13, R14 and sing18, find the orientations that preserve the feature against every fixed rigid A with |A| ≤ 9.

### WS6. Certified lattice lower bounds for n = 13..17 (priority 3)

- **Goal.** `328 ≤ ENat.card (RigidClasses 13)`, and so on up to `8761 ≤ … 17`, plus fixed-count versions for WS1.
- **Facts.**
  - The judge found **no profileKey collisions** among rigid lattice classes for n ≤ 19 [computed]. So the existing invariant (strictly increasing profile keys) suffices for distinctness.
  - For n ≤ 13, `checkBuild` covers every set.
  - For 14–17, sets descending from R14 and I15 need a base certificate: WS3's merge certificates, or the hinge lemma plus a three-ring lemma.
- **Deliverables.**
  - `latticeCatalogue13` … `latticeCatalogue17`;
  - `isLocallyRigid_of_checkBuildFrom`;
  - `card_rigidClasses_ge_thirteen` … `_seventeen`;
  - an extension of OEIS A171604 ready to submit.
- **Effort.** 2–3 sessions.
- **Risk.** Kernel time and memory. Extrapolating from 10 s at n = 12 (size × n²) gives about 20 min at n = 17 [spec]. Shard into files of about 500 entries if needed.
- **First step.** Export the 328 sets at n = 13 in build order, sorted by profile key, into a scratch copy of `LatticeCert.lean`, and time `decide +kernel`.

### WS7. Transfer matrices: long series for subclasses and rational GFs per strip width (priority 3)

- **Goal.**
  - SAT counts (a lower bound for a_L, and equal to it for n ≤ 12) to n ≈ 40, giving μ_s to 3–4 digits and a test of θ = 1.
  - Rational GFs for infinitesimally rigid sets of strip width 4, 5, 6.
- **Method.**
  - **SAT** is local (every site in a spanned triangle) plus triangle-connectivity, so a Jensen-type finite-lattice method applies. The state is boundary occupancy plus non-crossing connectivity labels.
  - **Strips** use the line-sum criterion. The state is the column occupancy plus the subspace of admissible open-line values modulo trivial motions (row-reduced over ℚ). Reject as soon as a closed line leaves a hidden motion.
  - The key empirical question is whether the reachable state set is finite.
- **Deliverables.**
  - SAT_fixed(n) to n ≈ 40;
  - state counts per width;
  - GFs fitted by Berlekamp–Massey (computed);
  - a check that width 3 reproduces T3 exactly.
- **Effort.** 3–6 sessions.
- **Risk.** Medium–high:
  - subspace states may be infinite, since rational coefficients can grow;
  - strip growth rates converge slowly to μ_L.
- **First step.** A fixed-width SAT strip counter for W = 2, 3, 4, validated against T3 (n ≤ 40) and a width filter of the WS2 census (n ≤ 20).

### WS8. Off-lattice: exact census to n ≈ 14 (priority 4)

- **Goal.** Exploratory-exact a(n) for all arrangements, n ≤ 14. Confirm or refute a(9..12) = 16, 35, 70, 160. Exact algebraic certificates for the 13-circle off-lattice core and a few 14-circle cores.
- **Method.**
  - By WS3(i), enumerate off-lattice cores only.
  - Build cores from lattice bodies with hinges and bars, under a body-level degree-of-freedom budget.
  - Solve exactly over ℚ(√3): hinge + bar is a quadratic; three bars give a resultant.
  - Check non-overlap with interval arithmetic and contacts exactly.
  - **Frame-compatibility test.** Plan 2's formula "2a + b = N₁ − N₂ − 1" is wrong as written. The correct, decidable test: the union of two lattice bodies sharing hinge h, joined by a bar x–y, is a lattice set iff some lattice symmetry g has eNorm(u − g·v) = 1, where u = x − h and v = y − h in the bodies' own frames. This depends on the orbit of v, not only on its norm, from norm 49 on.
- **Deliverables.**
  - A table of off-lattice cores with minimal polynomials;
  - all-arrangement counts to n = 14 (computed; exhaustive relative to a body-graph completeness lemma);
  - `OffLattice.lean`-style certificates, giving new [Lean] lower bounds such as a(13) ≥ 329.
- **Effort.** 4–6 sessions.
- **Risk.** High:
  - completeness of the body-graph enumeration is unproved;
  - the number fields get large.
- **First step.** An exhaustive two-body hinge + bar assembler. Acceptance: O11 is the unique off-lattice two-body core at n = 11; none exists at n ≤ 10; the lattice twins (R14 type) appear at lattice angles.

### WS9. Exact a(9) and a(10) for all arrangements (priority 4)

- **Goal.** `card_rigidClasses_nine = 16`, `card_rigidClasses_ten = 35`, and `IsRigid.isLattice_of_card_le_ten`. Stretch goal: a(11) = 70.
- **Method.** Extend the corner method (`Cores78`/`SixCorners`/`LemmaE`) from at most 2 to at most 4 non-corner circles, then use `LatticeCover.succ_of_cores`. Remark 2 of `docs/cores.md` says the method stops exactly at 10 circles, where the 10-circle core appears; n = 10 needs a new idea.
- **Effort.** 5–10 sessions; for comparison, n = 7–8 took about 2,500 lines.
- **Risk.** High.
- **First step** (feasibility only). A Lean `#eval` listing the leaves of the six-corner frame with 3 and 4 non-corners, with side lengths in {2, 4} ∪ [6, ∞), flagging the leaves not killed by degree counts. Decide whether to continue from the size of that list.

### WS10. Longer term (priority 5)

- **Second-order rigidity theorem** (Connelly–Whiteley, one-dimensional flex space).
  - Needed to certify singular sets from n = 20 (S20). Up to n = 19, all singular sets are Henneberg-certified.
  - Elementary proof route (Plan 2 W4): pairing with a stress kills the linear term.
- **Pattern theorem** (Madras style): SAT, core-free and infinitesimally rigid classes are exponentially rare. This is research level, and the strict inequalities are the hard part.
- **Upper bound on the Maxwell-class growth.** This is the growth of polyhexes with at least 2n−3 contacts, κ(2), for which there is only weak data from n ≤ 13. A rigorous κ(2) < 2.8578 would prove that infinitesimally rigid sets grow more slowly than polyiamonds.
- **Existence of μ for all arrangements.**
  - Open: gluing off the lattice has no decoding argument yet (Appendix A).
  - Finiteness of `RigidClasses n` for general n needs real algebraic geometry that Mathlib lacks. Keep it a clearly marked gap and state Lean results about all arrangements as lower bounds.

---

## 4. Conjectures to test

| # | conjecture | status and evidence | test |
|---|---|---|---|
| C1 | a_L(n) ~ C·μ_L^n·n^(−1) with μ_L ∈ [2.45, 2.65] | [conj]. Corrected ratio 2.476 at 25 and rising; two-step extrapolants 2.50–2.53 | WS2 to n = 28; differential approximants; θ fixed versus free |
| C2 | SAT is exponentially rare: μ_s ≈ 2.40 < μ_L, so the exception share → 1 | [conj]. Share 23.6% at 25; logit step 0.20 → 0.13 per n | WS2 shares; WS7 SAT series to 40; WS10 pattern theorem |
| C3 | Core-free, exactly-isostatic and infinitesimally rigid classes are exponentially rare | [conj]. Core-free share 60% → 31% over n = 12..19 | WS2 shares; WS10 |
| C4 | Singular share does not tend to 0 | [spec]. 0.40% at 25; ratio falling 7.0 → 3.1 | WS2 to 28 |
| C5 | a(9..12) = 16, 35, 70, 160 (no off-lattice arrangement below 11; O11 unique at 11; 5 off-lattice at 12) | [conj]. Floating-point searches of restricted families | WS8 exact assembler; WS9 proofs |
| C6 | μ_all > μ_L (lattice share → 0) | [spec]. Floating-point off-lattice share ≥ 46% at n = 17 | WS8 off-lattice growth to n ≈ 15–20 |
| C7 | For each strip width, infinitesimally rigid sets have a rational GF | [conj]; proved for width 3 | WS7 state counts |
| C8 | Rigid = cluster-merge (R1/R2) on the lattice for n ≤ 19, failing first at 20 (3 classes); Laman = lattice rigidity for n ≤ 19 | [computed] | WS3 Lean certificates for the n = 20 examples |
| C9 | Directed snakes (headings within a 120° cone) give valid saturated snakes for all n, so a_L(n) ≥ D(n) ~ c·1.5129^n | [conj]. Checked for words of length ≤ 21; gluing scheme | finite `decide` plus a window lemma |
| C10 | Exactly one interior circle ⇔ the canonical core is the flower | [conj]. Checked set by set for n ≤ 15 | WS3(i) plus a degree argument |
| C11 | The first non-saturated polyiamond corner set has exactly 26 circles | [computed] upper bound 26 (judge); census says none ≤ 25 | count them at 26 in WS2 |
| C12 | Every Harborth-extremal (max-contact) lattice set is rigid | [spec]. All counted ones are | `#eval` over max-contact polyhexes to n ≈ 15 |
| C13 | No closed form, and no algebraic or D-finite GF, for a_L or a | [spec] | not testable directly; the guess-and-check of a GF on 28+ terms should fail |

---

## 5. Exactly countable sub-families

| family | count / generating function | range | growth | status |
|---|---|---|---|---|
| Fans of triangles around one circle | 1 for each n = 3..7, else 0 (the 6-fan has the same 7 corners as the 5-fan) | all n | – | [paper]; corner coincidence [Lean] |
| Two adjacent rows | only the straight strip: 1 for each n ≥ 3 | all n | 1 | [paper] |
| Width exactly 3, fixed: T3(x) | x³(1+x)²(2+x+2x²+2x³+2x⁴−x⁵)/(1−x²−x³−x⁵) − 2x³ − 4x⁴/(1−x) | all n | 1.429108 (root of 1−x²−x³−x⁵; judge checked) | characterization [paper]; GF derived and checked to n = 40 [computed]; judge re-expanded to n = 12 |
| Width exactly 3, classes: C3(x) | ¼(T3+V+R+H) − x⁴ − x⁵ − 2x⁶ − 2x⁷, terms below | Burnside valid n ≥ 10 [paper]; checked n ≥ 8 | 1.429108 | [computed]; matches brute force to n = 20 |
| Saturated snakes (dual graph a path, triangle-closed) | S(n) = (F_{n−3} + F_{n/2})/2 for even n, (F_{n−3} + F_{(n−3)/2})/2 for odd n | **4 ≤ n ≤ 17 only**; falls short from 18 (319 vs 322) | φ (local) | [computed]; judge checked the formula against the listed values for n = 4..18 |
| Directed snakes (headings in a 120° cone) | word GF W(x) = 2/(1−x) + 2x²(1−2x²+x³−x⁵)/((1−x)(1−2x²)(1−x−x²+x³−x⁴)); D(n) = [W(m)+Pal(m)+W(m/2)·[m even]]/4 with m = n−4 | formula all n; validity all n [conj] | 1.512876 (judge checked the root) | [computed] |
| Combs (straight two-row spine, single circles on the outer rows) | rational, denominator (1−x)(1−x−x²)(1−x²−x³) | all n | φ | rigidity [paper]; GF [computed] |
| Hexagonal-convex sets (L; x, y, z) | N = C(L+2,2) − C(x+1,2) − C(y+1,2) − C(z+1,2); classes = D6-orbits of side sequences | all N | ~linear | [paper]; counts to N = 60 [computed] |
| Convex hexagon **cores** (all six sides ≥ 1) | sub-sum of the above: infinitely many rigid lattice cores | all N | ~linear | [paper] |
| Core-free class f(n) | 1,1,1,3,3,8,12,25,43,93,177,375,764,1628,3382,7130,14863 (n = 3..19); no formula | n ≤ 19 | ≈ 2.1 | [computed] |
| Max-contact (Harborth-extremal) rigid lattice sets | 1,1,1,3,1,1,4,1,2,1,4,1,4,1,9,3,1 (n = 3..19) | n ≤ 19 | – | [computed] by the judge; **differs from A284373 at 13, 15, 17** |
| Non-saturated polyiamond corner sets | 0 for n ≤ 25; ≥ 1 at n = 26 | | | [computed] |

Terms and definitions behind the table:

- **C3 terms**, n = 6..30: 2, 3, 8, 11, 15, 23, 31, 46, 63, 92, 127, 185, 258, 373, 522, 755, 1061, 1529, 2161, 3104, 4401, 6314, 8973, 12857, 18300.
- **C3 pieces:**
  - V = (x⁴+x⁶+x⁷+3x⁹−2x¹⁰+4x¹¹−x¹²+2x¹³+x¹⁴−x¹⁵−x¹⁷)/((1−x²)(1−x⁴−x⁶−x¹⁰));
  - R = (x⁴+2x⁶+x⁷+2x⁸+2x⁹+2x¹¹−x¹²−x¹⁵)/(1−x⁴−x⁶−x¹⁰);
  - H = x⁴(1+x²)²/(1−x³).
- **Width-3 rule.** A set in rows 0–2 that uses all three rows is rigid iff, after translation:
  - row 1 is m ≥ 2 consecutive circles;
  - every interior slot of rows 0 and 2 is used, and consecutive interior slots share a row;
  - an end slot is used only next to a used interior slot in the same row.

  All such sets are SAT and infinitesimally rigid.
- **Width ≤ 3** = C3 + 1. It contains every rigid arrangement for n ≤ 8, and 12 of the 16 at n = 9.

All exactly solved families grow at most like φ ≈ 1.618, far below μ_L ≈ 2.5. They give certified lower bounds, not the asymptotics.

---

## 6. Questions for the user

1. **Is this answer acceptable in place of a formula?** The proposed substitute:
   - exact values;
   - the exact core partition;
   - rational GFs for bounded-width families;
   - a theorem that the growth constant exists, with certified bounds;
   - a pre-registered asymptotic conjecture a_L(n) ~ C·μ^n/n with μ ≈ 2.5.

   Or should effort go mainly to exact values for as many n as possible?
2. **Main target:** all arrangements a(n), where exact data beyond n ≈ 12–14 looks out of reach, or the lattice count a_L(n) (= OEIS A171604), where data to n ≈ 28 and sharp asymptotics are realistic?
3. **May `native_decide` be used for large certificates?**
   - Kernel-only certification probably stops around n ≈ 16–17.
   - Getting μ_L ≥ 2 rigorously needs a certified count of about 1.7·10⁷ sets at n = 23.
4. **May compiled Lean be used?** That is, results from `lean -c` + `leanc` (the same Lean source, not kernel-checked), recorded in the journal as [computed]. And may multi-day background runs be used for n = 26–28?
5. **OEIS.** Should a(8..25) be submitted as an extension of A171604, with new entries for fixed counts and for all arrangements? If so, under whose name?
6. **Naming.** May "saturated polyiamond" be renamed (e.g. "triangle-closed polyiamond") to avoid the clash with the existing term?
7. **Fixed counts.** May fixed counts (up to translation) be the primary objects in the asymptotic theorems, with free counts as corollaries?
8. **API changes.** WS3/WS10 add a relative-rigidity notion (`RigidIn`) and generalize infinitesimal rigidity to bars of arbitrary length. May existing definitions in `InfRigid.lean` be generalized, keeping the old names as special cases?

---

## 7. Sources

**OEIS** (fetched by the judge on 2026-10-15): A171604 (data 1,1,1,1,1,3,4, keyword "more"), A000577, A284373. Cited via the literature investigation: A001420, A000228, A001207, A047932, A227117, A273468, A085632.

**Literature** (cited via the literature investigation; not re-read by the judge):

- **Rigidity:**
  - Asimow & Roth, Trans. AMS 245 (1978);
  - Connelly & Whiteley, SIAM J. Discrete Math. 9 (1996) (second order / prestress stability);
  - Tay–Whiteley body–bar–hinge theory;
  - Connelly–Gortler–Theran, Proc. R. Soc. A 475 (2019);
  - Lubiw & Schaefer, arXiv:2508.10136;
  - Dewar et al., Examples & Counterexamples 7 (2025).
- **Animals and asymptotics:**
  - Klarner, Canad. J. Math. 19 (1967);
  - Madras, Ann. Comb. 3 (1999);
  - Parisi & Sourlas, PRL 46 (1981);
  - Jensen & Guttmann, J. Phys. A 33 (2000) L257;
  - Brydges & Imbrie, Ann. Math. 158 (2003).
- **Polyiamonds:**
  - Sykes & Glen, J. Phys. A 9 (1976);
  - Barequet–Shalah–Zheng, J. Comb. Optim. 37 (2019);
  - Bui, Electron. J. Combin. 30(4) (2023) P4.38 and arXiv:2510.06806;
  - Barequet–Rote–Shalah (upper bound 3.6108, EuroComb 2019).
- **Polyhexes:** Vöge & Guttmann, Theor. Comput. Sci. 307 (2003).
- **Algorithms:**
  - Redelmeier, Discrete Math. 36 (1981);
  - Jensen, J. Stat. Phys. 102 (2001);
  - Aleksandrowicz & Barequet, IJCGA 19 (2009).
- **Solved subclasses:**
  - Dhar, PRL 49 (1982);
  - Bousquet-Mélou & Rechnitzer, Discrete Math. 258 (2002);
  - Harary & Read (1970);
  - Rastegar & Mansour, arXiv:2011.05318.
- **Clusters:**
  - Holmes-Cerfon, SIAM Rev. 58 (2016);
  - Perry, Holmes-Cerfon, Brenner & Manoharan, PRL 114 (2015);
  - Heitmann & Radin, J. Stat. Phys. 22 (1980);
  - Harborth, Elem. Math. 29 (1974);
  - De Luca & Friesecke, J. Stat. Phys. 167 (2017).
- **Bounds:**
  - Milnor, Proc. AMS 15 (1964);
  - Tutte (1963), planar maps;
  - Bonichon et al. (2006), 2^{4.91n} planar graphs (quoted from memory; verify).
- **Naming:** Blondin Massé, de Carufel & Goupil, arXiv:1803.09181.

**Internal (exploratory files),** kept in `explore/` (see `explore/README.md`):

- Census: `explore/RigidEnum.lean`, `explore/orderly25.txt`, `explore/decide25.txt`.
- Judge checks: `explore/NonSaturated26.lean` (the 26-circle example), `explore/JudgeEnum.lean`
  and `explore/judge19.txt` (fixed counts, profile-key collisions, max-contact counts for n ≤ 19).
- Gluing prototype: `explore/Glue.lean`.

---

## Appendix A. How the three plans were checked

**Confirmed.**

- **Plan 3's concatenation lemma.** The judge re-derived the case analysis: with no cross contact, exactly the two neighbour patterns remain. The decoding needs one more bit (is R occupied?), which is available.
- **Mathlib support for Fekete.** `Submultiplicative.tendsto_lim`, `lim_le_rpow` and `apply_mul_add_le` are in `Mathlib/Analysis/Subadditive.lean`. Padding u(n) to 1 for n < 3 is valid because f_L(3) = 2.
- **Repository lemmas cited by the plans all exist:**
  - `IsRigid.of_hinge_of_union` (needs only bar endpoints different from the hinge; no non-collinearity), `IsLocallyRigid.of_hinge`;
  - `IsRigid.touchesTwo`, `IsRigid.connected`, `Removable.isRigid_comap_succAbove`;
  - `exists_mem_latticeApexes`, `LatticeCover.succ_of_cores`;
  - `IsPolyiamond.isRigid`, `not_isInfRigid_of_taut`;
  - `checkBuild`, `profileKey`, `SitesCongr.iso`.

  The converse `sitesCongr_of_iso` does **not** exist; it is needed for WS1 and WS4.
- **Numbers recomputed.** The bounds 1.7518, 1.785, 1.816, 1.870, 1.9365 and ≈ 2.03 were recomputed, as were all ratios, shares and logit increments quoted from the census.
- **Arguments checked.**
  - R1/R2 soundness, including collinear hinges.
  - At most two bodies per circle.
  - Plan 1's peel-and-lookup Henneberg test.
  - The line-sum identity.
- **Counts reproduced.** Free and fixed counts for n ≤ 19 were reproduced by the judge. This is not independent: it used the same core-search code.
- **profileKey distinctness.** No collisions among rigid lattice classes for n ≤ 19, so WS6 is not blocked by the invariant.

**Corrected or downgraded.**

1. **Plan 1:** "β ≈ 2.0 from the certified N = 13" and "≈ 2.2 from N = 25" are wrong. They are 1.785 and ≈ 2.03 (at most 1.88 at N = 13 even without the factor 2). So "β ≈ 2.1–2.2 by gluing" is overstated.
2. **Plan 1:** "μ_s has already converged" is an overclaim. The flat corrected ratio shows consistency with θ = 1, not convergence.
3. **Plan 1:** "first non-saturated polyiamond corner set has 26–33 circles, probably near 33" is superseded: the judge's example has 26.
4. **Plan 1:** listing a(9) and a(10) as "realistic certified targets" is optimistic; by the method's own Remark 2, n = 10 needs a new idea.
5. **Plan 2:** the Eisenstein compatibility formula is wrong as written. For example, with N₁ = N₂ = 1 it accepts w = (−1, 1), but eNorm((1,0) − (−1,1)) = 3 ≠ 1. Compatibility also depends on the orbit of the port vector from norm 49 on. The corrected test is in WS8.
6. **Plan 2:** "supermultiplicativity for all arrangements" (W8) lacks a decoding/injectivity argument. After the rotation the pieces are no longer separated by a line. Unproved.
7. **Plan 2:** its thesis presents rational GFs per strip width as a consequence of the calculus. This is a conjecture (C7).
8. **Plan 2:** "CMR certificates make lattice counts theorems up to 16–19" is only true for lower bounds. Exact counts also need completeness of the core list.
9. **Plan 3:** `fixedCount n ≤ 2 * singCount (n + 17)` does not follow as stated. The gluing lands in sizes n+17 and n+18; use the two-term form.
10. **Plan 3:** "about 15 h to n = 28" is too low. The core search grows ×3.3 per level, giving about 1–1.5 days for n = 26–28. Storing whole levels needs about 10 GB at n = 28, so Plan 1's depth-first mode is needed.
11. **Plan 3:** the prediction "exception share passes 26% at n = 26" is expected to fail narrowly (trend: 25.8 ± 0.3%).
12. **Plan 3:** κ(2) ≈ 2.7 for the Maxwell class rests on n ≤ 13, where the rigid ratio (2.24) was still far below its later values. This is weak evidence.
13. **Literature report:** the "match" with A284373 fails at n = 13, 15, 17.
14. **Literature report vs structure report on "2.84":** both explanations are partly right. Either way, it is not the growth constant.
15. **Structure report and Plan 1:** "off-lattice arrangements outnumber lattice ones from n ≈ 18" rests on floating-point counts over restricted families. It is [spec].
16. **All plans: independence.** The lattice counts for n ≥ 16 come from one core-search code lineage (the structure agent adapted it, and the judge reused it). Only n ≤ 15 (unpruned brute force) and the SAT part through n = 17 are independently confirmed.

**Where the plans agree** (and this plan follows them):

- no closed formula;
- push the lattice data with pre-registered predictions;
- prove the growth constant exists by gluing;
- formalize the structure and the exactly solvable families;
- treat exact all-arrangement values beyond n = 8 as high-risk.

The main difference between the plans was priority. This plan puts Plan 3's Fekete theorem and Plan 1's data push first, Plan 2's structure calculus second, and the off-lattice and small-n exactness work last.