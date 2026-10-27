import RigidArrangements.Cluster

/-!
# Bars, the non-degeneracy determinant, and the fourth merging rule

`RigidArrangements.Cluster` proves three merging rules. R1, R2 and R3 all share a remarkable
feature: **they have no non-degeneracy condition at all**. Two clusters sharing two circles
merge, a ring of three clusters merges, a taut chain merges, and in each case the proof goes
through the pinning engine `Arrangement.rigidIn_of_dist_two`, which only ever talks about
distances. A flat triangle is pinned by its side lengths exactly as a fat one is.

The fourth rule is different. Two clusters `S` and `T` joined by **three contacts** merge — but
only if the three bars are in *general position*, and this file is mostly about saying what that
means and why it is unavoidable. Three bars joining two rigid pieces leave the relative motion
`z ↦ ρ z + τ` (three real parameters: one angle, two translations) three equations to satisfy.
Generically that pins the motion. It fails exactly when the three equations are dependent, and
the first-order content of each equation is a *line*: the line of the bar. Three lines fail to
be independent precisely when they are concurrent or all parallel.

## The determinant

For a bar from `P` to `Q`, `barRow P Q` is the triple of homogeneous line coordinates
`(A, B, C)` of the line through `P` and `Q`, meaning the line is `{z | A z.re + B z.im + C = 0}`
(`onLine_iff`). `barMatrix` stacks three such rows and `barDet` is the determinant, *over `ℝ`*:
the content is the real-linear independence of three real functionals of the three real unknowns
`(θ, τ.re, τ.im)`, so `ℝ` and not `ℂ` is the right home.

* `barDet_eq_zero_iff` is the honest companion statement, proved in both directions: for three
  genuine bars, `barDet = 0` exactly when some point of the plane lies on all three bar lines
  (`BarsConcurrent`) or the three bar directions are pairwise parallel (`BarsParallel`).
  "All parallel" is concurrency at infinity, which the projective reading of the determinant
  allows, so it must appear.
* What would be *wrong* is a hypothesis phrased through pairwise intersection points: with two
  coincident bar lines there is no pairwise intersection point to speak of, and with three there
  is no unique common point, yet the matrix is singular in both cases.
  `barDet_eq_zero_of_sameLine` records the coincident case separately.
* `eq_zero_of_barDet_ne_zero` is the first-order output in raw arithmetic: no nonzero
  infinitesimal rigid motion of the plane preserves all three bar lengths to first order. This
  is the infinitesimal rigidity of the two-body-and-three-bars framework.
* `det_barVelRow` records a correction. The row one writes down when differentiating the bar
  length in Euclidean coordinates is the line row with its first two columns swapped and one
  negated, so the velocity form and the line form have *equal* determinants. An earlier guess
  that they differ, or that the velocity form has no lattice transformation law, is false. The
  real reason to prefer the line form is that its affine transformation law is visible:
  concurrency and parallelism are affine notions, an affine change of coordinates acts on line
  coordinates by the contragredient matrix, and the determinant picks up a fixed nonzero factor.

## The lattice form, and why the smallest emergent arrangement has twenty circles

On the triangular lattice the determinant becomes integer arithmetic. `barRowZ` and `barDetZ`
are the line coordinates and the determinant in lattice coordinates, and

`barDet_latticePoint : barDet (latticePoint ∘ p) (latticePoint ∘ q) = 12 * barDetZ p q`.

**The constant is `12`**, not the `± 6` an earlier reconnaissance guessed: column by column the
change of coordinates is `A = √3 Az`, `B = 2 Bz - Az`, `C = 2 √3 Cz`, of determinant
`√3 · 2 · 2√3 = 12`. So `barDetZ ≠ 0` is a decidable certificate for R4's side condition
(`barDet_ne_zero_of_barDetZ_ne_zero`), checked by `decide`.

One such integer is the reason the exploratory census finds no emergent rigid arrangement below
`n = 20`. The arrangement `S20` — the `5 × 5` lattice block minus
`{(4,4), (4,0), (2,3), (1,2), (0,0)}` — is rigid, has no degree-`2` circle, and its R1–R4
fixpoint is a `16`-circle body, a `4`-circle rhombus body and three unmerged joining contacts.
Those three contacts are `(2,4)-(1,4)`, `(2,2)-(1,3)` and `(0,3)-(0,2)`, whose lattice lines
`b = 4`, `a + b = 4` and `a = 0` all pass through `(0, 4)`. So `barDetZ_s20_cross_bars`: the
determinant is `0`, R4 cannot fire, and `S20` is emergent. That single vanishing is why the
smallest emergent arrangement has twenty circles and not thirty.

## The analytic core

`eventually_eq_of_barDet_ne_zero` is the one genuinely hard statement, and it mentions no
clusters: three bars of length `2` whose determinant is nonzero admit no rigid motion
`z ↦ ρ z + τ` of the plane other than the identity, among motions close enough to the identity,
that keeps all three bar lengths.

No inverse function theorem and no exponential are needed. The motion is parametrised by `ρ`
itself with `‖ρ‖ = 1`, which pins `ρ.re` to `ρ.im` to second order all by itself: from
`ρ.re² + ρ.im² = 1` and `ρ.re > 0`,

`0 ≤ 1 - ρ.re = ρ.im² / (1 + ρ.re) ≤ ρ.im²`.

So `v = (-τ.im, τ.re, ρ.im)` is the infinitesimal motion and the `ρ.re` direction contributes
only to the quadratic remainder. (Writing `ρ = 1 + z` and forgetting that `z.re` is determined
by `z.im` to second order is the easy way to go wrong.) `bar_expand` is the *exact*
second-order identity for one bar, `bar_row_bound` turns it into `|barRow · v| ≤ 4 B² ‖v‖²`, and
`barMatrix_ker_eq_bot` plus `LinearMap.exists_antilipschitzWith` give `‖v‖ ≤ 4 K B² ‖v‖²`, so a
small enough neighbourhood forces `v = 0`.

## The rigid-motion normal form

`Arrangement.rigidIn_iff_exists_rigid_motion`: for a set with at least two circles, being a
cluster is the same as moving, along every small contact-keeping motion, by a single rotation
and translation of the plane. The direction R4 needs is `RigidIn.exists_rigid_motion_mem`,
which also places `(ρ, τ)` in a prescribed neighbourhood of `(1, 0)` — the bare existential is
not enough, because the analytic core is a statement about motions *near* the identity.

**The orientation-reversing case really is excluded**, and nearness is what excludes it: see the
discussion on `RigidIn.exists_rigid_motion_mem`. R4 does not need `‖ρ‖ = 1` weakened to "`ρ` or
its conjugate".

## R4

`Arrangement.RigidIn.union_of_three_bars` is the rule. Note what is **not** a hypothesis: `S`
and `T` are not assumed to have two circles each. Nontriviality is *free*, because if all three
bars started at the same circle their three lines would be concurrent there and the determinant
would vanish (`exists_ne_left_of_barDet_ne_zero`). The determinant hypothesis does that work.

`Arrangement.RigidIn.union_of_three_bars_lattice` is the lattice form, whose side condition is
integer arithmetic.
-/

open Filter Topology Matrix

namespace RigidArrangements

/-! ### Lines through two points -/

/-- The scalar cross product of two plane vectors. It vanishes exactly when they are parallel
(one is a real multiple of the other, if either is nonzero). -/
def crossR (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- `z` lies on the line through `P` and `Q`: it is an affine combination of them. For `P ≠ Q`
this is the line in the usual sense. -/
def OnLine (P Q z : ℂ) : Prop := ∃ t : ℝ, z = P + (t : ℂ) * (Q - P)

/-! ### The bar row and the bar determinant -/

/-- **Homogeneous line coordinates of a bar.** For a bar from `P` to `Q`, `barRow P Q` is the
triple `(A, B, C)` with

* `A = P.im - Q.im`,
* `B = Q.re - P.re`,
* `C = P.re * Q.im - P.im * Q.re`,

which are the coefficients of the line through `P` and `Q`, in the sense that the line is
`{z | A * z.re + B * z.im + C = 0}` (`onLine_iff`). Note that `(A, B)` is the normal direction
and `(B, -A) = Q - P` is the direction of the bar, so `(A, B) ≠ (0, 0)` as soon as `P ≠ Q`
(`barRow_ne_zero`), which holds for a bar since `‖P - Q‖ = 2`. -/
def barRow (P Q : ℂ) : Fin 3 → ℝ :=
  ![P.im - Q.im, Q.re - P.re, P.re * Q.im - P.im * Q.re]

@[simp] theorem barRow_zero (P Q : ℂ) : barRow P Q 0 = P.im - Q.im := rfl

@[simp] theorem barRow_one (P Q : ℂ) : barRow P Q 1 = Q.re - P.re := rfl

@[simp] theorem barRow_two (P Q : ℂ) : barRow P Q 2 = P.re * Q.im - P.im * Q.re := rfl

/-- The `3 × 3` matrix whose rows are the line coordinates of the three bars `xᵢ yᵢ`. -/
def barMatrix (x y : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i => barRow (x i) (y i)

@[simp] theorem barMatrix_apply (x y : Fin 3 → ℂ) (i j : Fin 3) :
    barMatrix x y i j = barRow (x i) (y i) j := rfl

/-- **The non-degeneracy determinant of three bars.** `barDet x y ≠ 0` is R4's side condition:
the three bars `xᵢ yᵢ` are neither concurrent nor all parallel (`barDet_eq_zero_iff`), which is
exactly the condition under which the three bar-length constraints pin down a rigid motion of
the plane (`eq_zero_of_barDet_ne_zero` to first order,
`eventually_eq_of_barDet_ne_zero` exactly).

It is a determinant over `ℝ`, taken as `Matrix.det`, so that the kernel machinery of Mathlib —
`Matrix.exists_mulVec_eq_zero_iff`, `Matrix.eq_zero_of_mulVec_eq_zero` — applies directly. -/
def barDet (x y : Fin 3 → ℂ) : ℝ := (barMatrix x y).det

/-- Applying the bar matrix to a triple, row by row. -/
theorem barMatrix_mulVec_apply (x y : Fin 3 → ℂ) (v : Fin 3 → ℝ) (i : Fin 3) :
    (barMatrix x y *ᵥ v) i =
      ((x i).im - (y i).im) * v 0 + ((y i).re - (x i).re) * v 1
        + ((x i).re * (y i).im - (x i).im * (y i).re) * v 2 := by
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three]
  simp only [barMatrix_apply, barRow_zero, barRow_one, barRow_two]

/-! ### Three algebraic facts about `3 × 3` determinants -/

/-- The determinant of a `3 × 3` matrix, expanded along the third column. -/
private theorem det_of_rows {R : Type*} [CommRing R] (r : Fin 3 → Fin 3 → R) :
    (Matrix.of r).det =
      r 0 2 * (r 1 0 * r 2 1 - r 1 1 * r 2 0) - r 1 2 * (r 0 0 * r 2 1 - r 0 1 * r 2 0)
        + r 2 2 * (r 0 0 * r 1 1 - r 0 1 * r 1 0) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  ring

/-- If the three rows, read as line coordinates, all vanish at the point `(u, v)`, the
determinant vanishes: the column vector `(u, v, 1)` is in the kernel. -/
private theorem det_eq_zero_of_sol {r : Fin 3 → Fin 3 → ℝ} {u v : ℝ}
    (h : ∀ i, r i 0 * u + r i 1 * v + r i 2 = 0) : (Matrix.of r).det = 0 := by
  rw [det_of_rows]
  linear_combination (r 1 0 * r 2 1 - r 1 1 * r 2 0) * h 0
    - (r 0 0 * r 2 1 - r 0 1 * r 2 0) * h 1 + (r 0 0 * r 1 1 - r 0 1 * r 1 0) * h 2

/-- If all three `2 × 2` minors in the first two columns vanish, the determinant vanishes. -/
private theorem det_eq_zero_of_minors {r : Fin 3 → Fin 3 → ℝ}
    (h : ∀ i j, r i 0 * r j 1 - r j 0 * r i 1 = 0) : (Matrix.of r).det = 0 := by
  rw [det_of_rows]
  linear_combination r 0 2 * h 1 2 - r 1 2 * h 0 2 + r 2 2 * h 0 1

/-- A singular `3 × 3` real matrix has a nonzero kernel vector. -/
private theorem exists_sol_of_det_eq_zero {r : Fin 3 → Fin 3 → ℝ} (h : (Matrix.of r).det = 0) :
    ∃ v : Fin 3 → ℝ, (v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0) ∧
      ∀ i, r i 0 * v 0 + r i 1 * v 1 + r i 2 * v 2 = 0 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of r)).mpr h
  refine ⟨v, ?_, fun i => ?_⟩
  · by_contra hc
    push Not at hc
    exact hv0 (funext fun i => by fin_cases i <;> simp_all)
  · have h1 := congrFun hv i
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Matrix.of_apply,
      Pi.zero_apply] at h1
    linear_combination h1

/-! ### The line equation -/

/-- A bar row is never zero in its first two entries: `(A, B)` is the normal of the bar line. -/
theorem barRow_ne_zero {P Q : ℂ} (hPQ : P ≠ Q) :
    barRow P Q 0 ≠ 0 ∨ barRow P Q 1 ≠ 0 := by
  simp only [barRow_zero, barRow_one]
  by_contra hc
  push Not at hc
  exact hPQ (Complex.ext (by linarith [hc.2]) (by linarith [hc.1]))

/-- **`barRow` really is the line through the bar.** For `P ≠ Q`, a point `z` lies on the line
through `P` and `Q` exactly when `A z.re + B z.im + C = 0`, where `(A, B, C) = barRow P Q`. -/
theorem onLine_iff {P Q : ℂ} (hPQ : P ≠ Q) (z : ℂ) :
    OnLine P Q z ↔ barRow P Q 0 * z.re + barRow P Q 1 * z.im + barRow P Q 2 = 0 := by
  simp only [barRow_zero, barRow_one, barRow_two]
  constructor
  · rintro ⟨t, rfl⟩
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · intro h
    -- the line equation is (minus) the vanishing of the cross product of `z - P` and `Q - P`
    have hcross : (z.re - P.re) * (Q.im - P.im) = (z.im - P.im) * (Q.re - P.re) := by
      linear_combination -h
    have hD : (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 ≠ 0 := by
      intro h0
      refine hPQ (Complex.ext ?_ ?_) <;> nlinarith [sq_nonneg (Q.re - P.re),
        sq_nonneg (Q.im - P.im)]
    refine ⟨((z.re - P.re) * (Q.re - P.re) + (z.im - P.im) * (Q.im - P.im)) /
      ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2), ?_⟩
    have h1 : ((z.re - P.re) * (Q.re - P.re) + (z.im - P.im) * (Q.im - P.im)) /
        ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) * (Q.re - P.re) = z.re - P.re := by
      rw [div_mul_eq_mul_div, div_eq_iff hD]
      linear_combination (-(Q.im - P.im)) * hcross
    have h2 : ((z.re - P.re) * (Q.re - P.re) + (z.im - P.im) * (Q.im - P.im)) /
        ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) * (Q.im - P.im) = z.im - P.im := by
      rw [div_mul_eq_mul_div, div_eq_iff hD]
      linear_combination (Q.re - P.re) * hcross
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    · linear_combination -h1
    · linear_combination -h2

/-- A bar line passes through its own first endpoint: the basic sanity of the line coordinates,
as a ring identity. -/
theorem barRow_self_left (P Q : ℂ) :
    barRow P Q 0 * P.re + barRow P Q 1 * P.im + barRow P Q 2 = 0 := by
  simp only [barRow_zero, barRow_one, barRow_two]; ring

/-- A bar line passes through its own second endpoint. -/
theorem barRow_self_right (P Q : ℂ) :
    barRow P Q 0 * Q.re + barRow P Q 1 * Q.im + barRow P Q 2 = 0 := by
  simp only [barRow_zero, barRow_one, barRow_two]; ring

/-! ### `barDet = 0` iff concurrent or all parallel -/

/-- Some point of the plane lies on all three bar lines. -/
def BarsConcurrent (x y : Fin 3 → ℂ) : Prop := ∃ z : ℂ, ∀ i, OnLine (x i) (y i) z

/-- The three bar directions are pairwise parallel. -/
def BarsParallel (x y : Fin 3 → ℂ) : Prop := ∀ i j, crossR (y i - x i) (y j - x j) = 0

/-- **The companion theorem.** For three genuine bars (nondegenerate endpoints), the bar
determinant vanishes exactly when the three bar lines have a common point or the three bar
directions are pairwise parallel. "All parallel" is the concurrency at infinity that the
projective reading of the determinant allows, which is why it must appear.

So `barDet x y ≠ 0` is the faithful Lean form of "the three bars are not all concurrent and not
all parallel"; see the module docstring for the readings that are *not* faithful. -/
theorem barDet_eq_zero_iff {x y : Fin 3 → ℂ} (hne : ∀ i, x i ≠ y i) :
    barDet x y = 0 ↔ BarsConcurrent x y ∨ BarsParallel x y := by
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := exists_sol_of_det_eq_zero (r := fun i => barRow (x i) (y i)) hdet
    by_cases h2 : v 2 = 0
    · -- the kernel vector is at infinity: the three bars are parallel
      right
      have hv01 : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        rcases hv0 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h2 h
      have hrow : ∀ k, ((x k).im - (y k).im) * v 0 + ((y k).re - (x k).re) * v 1 = 0 := by
        intro k
        have h1 := hv k
        simp only [barRow_zero, barRow_one, barRow_two] at h1
        rw [h2] at h1
        linear_combination h1
      intro i j
      simp only [crossR, Complex.sub_re, Complex.sub_im]
      rcases hv01 with h0 | h1
      · have key : (((x i).im - (y i).im) * ((y j).re - (x j).re)
            - ((x j).im - (y j).im) * ((y i).re - (x i).re)) * v 0 = 0 := by
          linear_combination ((y j).re - (x j).re) * hrow i - ((y i).re - (x i).re) * hrow j
        rcases mul_eq_zero.mp key with hk | hk
        · linear_combination hk
        · exact absurd hk h0
      · have key : (((x i).im - (y i).im) * ((y j).re - (x j).re)
            - ((x j).im - (y j).im) * ((y i).re - (x i).re)) * v 1 = 0 := by
          linear_combination ((x i).im - (y i).im) * hrow j - ((x j).im - (y j).im) * hrow i
        rcases mul_eq_zero.mp key with hk | hk
        · linear_combination hk
        · exact absurd hk h1
    · -- the kernel vector is a finite point: the three bars are concurrent there
      left
      refine ⟨⟨v 0 / v 2, v 1 / v 2⟩, fun i =>
        (onLine_iff (hne i) (⟨v 0 / v 2, v 1 / v 2⟩ : ℂ)).mpr ?_⟩
      have hre : (⟨v 0 / v 2, v 1 / v 2⟩ : ℂ).re = v 0 / v 2 := rfl
      have him : (⟨v 0 / v 2, v 1 / v 2⟩ : ℂ).im = v 1 / v 2 := rfl
      rw [hre, him]
      have h1 := hv i
      simp only [barRow_zero, barRow_one, barRow_two] at h1 ⊢
      field_simp [h2]
      linear_combination h1
  · rintro (⟨z, hz⟩ | hpar)
    · rw [barDet, barMatrix]
      exact det_eq_zero_of_sol (u := z.re) (v := z.im) fun i => (onLine_iff (hne i) z).mp (hz i)
    · rw [barDet, barMatrix]
      refine det_eq_zero_of_minors fun i j => ?_
      have h1 := hpar i j
      simp only [crossR, Complex.sub_re, Complex.sub_im] at h1
      simp only [barRow_zero, barRow_one]
      linear_combination h1

/-- **Reordering the bars does not change whether the determinant vanishes.** Proved from
`barDet_eq_zero_iff`, since "concurrent or all parallel" plainly does not depend on the order
of the three bars. (The determinant itself only changes by the sign of the permutation.) This
is what makes the "say, the first two bars" in `barDet_eq_zero_of_sameLine` harmless. -/
theorem barDet_comp_perm_eq_zero_iff (σ : Equiv.Perm (Fin 3)) {x y : Fin 3 → ℂ}
    (hne : ∀ i, x i ≠ y i) : barDet (x ∘ σ) (y ∘ σ) = 0 ↔ barDet x y = 0 := by
  simp only [Function.comp_def]
  rw [barDet_eq_zero_iff (fun i => hne (σ i)), barDet_eq_zero_iff hne]
  constructor
  · rintro (⟨z, hz⟩ | hpar)
    · exact Or.inl ⟨z, fun i => by simpa using hz (σ.symm i)⟩
    · exact Or.inr fun i j => by simpa using hpar (σ.symm i) (σ.symm j)
  · rintro (⟨z, hz⟩ | hpar)
    · exact Or.inl ⟨z, fun i => hz (σ i)⟩
    · exact Or.inr fun i j => hpar (σ i) (σ j)

/-- **The coincident case, explicitly.** If both endpoints of the second bar lie on the line of
the first, so that two of the three bar lines are the same line, then `barDet = 0` — whatever
the third bar does. (By `barDet_comp_perm_eq_zero_iff` the choice of the first two bars is no
restriction.) Combined with `barDet_eq_zero_iff` this says the disjunction "concurrent or all
parallel" is true in that case too, which is why that disjunction, and not a reading through
pairwise intersection points, is the correct thing to negate in R4.

The proof is the classical identity

`det = E₂(x₁) * E₀(y₁) - E₂(y₁) * E₀(x₁)`,

where `Eₖ(z) = Aₖ z.re + Bₖ z.im + Cₖ` evaluates the `k`-th bar line at `z`: both factors
`E₀(x₁)` and `E₀(y₁)` vanish exactly when the endpoints of bar `1` are on line `0`. -/
theorem barDet_eq_zero_of_sameLine {x y : Fin 3 → ℂ} (hne : x 0 ≠ y 0)
    (h1 : OnLine (x 0) (y 0) (x 1)) (h2 : OnLine (x 0) (y 0) (y 1)) :
    barDet x y = 0 := by
  rw [onLine_iff hne] at h1 h2
  rw [barDet, barMatrix, det_of_rows]
  simp only [barRow_zero, barRow_one, barRow_two] at h1 h2 ⊢
  linear_combination
    (((x 2).im - (y 2).im) * (x 1).re + ((y 2).re - (x 2).re) * (x 1).im
      + ((x 2).re * (y 2).im - (x 2).im * (y 2).re)) * h2
    - (((x 2).im - (y 2).im) * (y 1).re + ((y 2).re - (x 2).re) * (y 1).im
      + ((x 2).re * (y 2).im - (x 2).im * (y 2).re)) * h1

/-! ### Degenerate bars are excluded by the determinant

Two small consequences of `barDet_eq_zero_iff` that R4 uses to avoid hypotheses. If all three
bars start at the same point, their lines are concurrent there; if they all end at the same
point, likewise. So `barDet ≠ 0` already forces each of the two bodies to contain two distinct
circles, and R4 needs no nontriviality hypothesis. -/

/-- **The first endpoints are not all equal.** If `barDet x y ≠ 0` then two of the three bars
start at different points — otherwise the three lines would be concurrent at the common start. -/
theorem exists_ne_left_of_barDet_ne_zero {x y : Fin 3 → ℂ} (hne : ∀ i, x i ≠ y i)
    (hdet : barDet x y ≠ 0) : ∃ i j, x i ≠ x j := by
  by_contra hc
  push Not at hc
  exact hdet ((barDet_eq_zero_iff hne).mpr
    (Or.inl ⟨x 0, fun i => ⟨0, by rw [hc 0 i]; push_cast; ring⟩⟩))

/-- **The second endpoints are not all equal.** The mirror image of
`exists_ne_left_of_barDet_ne_zero`. -/
theorem exists_ne_right_of_barDet_ne_zero {x y : Fin 3 → ℂ} (hne : ∀ i, x i ≠ y i)
    (hdet : barDet x y ≠ 0) : ∃ i j, y i ≠ y j := by
  by_contra hc
  push Not at hc
  exact hdet ((barDet_eq_zero_iff hne).mpr
    (Or.inl ⟨y 0, fun i => ⟨1, by rw [hc 0 i]; push_cast; ring⟩⟩))

/-! ### The first-order output, and the velocity form of the row -/

/-- **Infinitesimal rigidity of two bodies joined by three bars.** If `barDet x y ≠ 0`, the only
infinitesimal rigid motion `(θ, s, t)` of the plane that preserves all three bar lengths to
first order is the trivial one. The three hypotheses are the differentiated bar-length
constraints with the factor `2` dropped: `θ` is the rotation speed and `(s, t)` the translation
velocity.

This is the first-order reading of the determinant hypothesis, in raw real arithmetic, and it is
what the analytic core uses, through `barMatrix_ker_eq_bot`. -/
theorem eq_zero_of_barDet_ne_zero {x y : Fin 3 → ℂ} (hdet : barDet x y ≠ 0) {θ s t : ℝ}
    (h : ∀ i, ((x i).re * (y i).im - (x i).im * (y i).re) * θ
      + ((y i).re - (x i).re) * s + ((y i).im - (x i).im) * t = 0) :
    θ = 0 ∧ s = 0 ∧ t = 0 := by
  have hv : barMatrix x y *ᵥ ![-t, s, θ] = 0 := by
    funext i
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, barMatrix_apply, barRow_zero,
      barRow_one, barRow_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply]
    linear_combination h i
  have hz : ![-t, s, θ] = (0 : Fin 3 → ℝ) := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Pi.zero_apply] at h0 h1 h2
  exact ⟨h2, h1, by linarith⟩

/-- The bar matrix is injective when its determinant is nonzero. The kernel form of
`eq_zero_of_barDet_ne_zero`, which is what feeds `LinearMap.exists_antilipschitzWith` in the
analytic core. -/
theorem barMatrix_ker_eq_bot {x y : Fin 3 → ℂ} (hdet : barDet x y ≠ 0) :
    LinearMap.ker (barMatrix x y).mulVecLin = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  replace hv : barMatrix x y *ᵥ v = 0 := hv
  obtain ⟨h2, h1, h0⟩ := eq_zero_of_barDet_ne_zero hdet (θ := v 2) (s := v 1) (t := -v 0)
    (fun i => by
      have h := congrFun hv i
      rw [barMatrix_mulVec_apply, Pi.zero_apply] at h
      linear_combination h)
  have e0 : v 0 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using e0
  · simpa using h1
  · simpa using h2

/-- The velocity row of a bar: `(dₓ, d_y, dₓ Q_y - d_y Qₓ)` with `d = P - Q`. This is what one
writes down when differentiating the bar length in Euclidean coordinates. -/
def barVelRow (P Q : ℂ) : Fin 3 → ℝ :=
  ![P.re - Q.re, P.im - Q.im, (P.re - Q.re) * Q.im - (P.im - Q.im) * Q.re]

/-- **The velocity form has the same determinant as the line form.** Since `dₓ = -B`, `d_y = A`
and `dₓ Q_y - d_y Qₓ = C`, the velocity row is the line row with its first two columns swapped
and one of them negated — a signed column permutation, of determinant `1`. So nothing is lost by
working with the line form, and an earlier guess that the velocity form "would not survive the
change to lattice coordinates" is false: it transforms exactly as well, by the same factor `12`
(`det_barVelRowZ`, `barDet_latticePoint`).

What *is* true, and is the real reason to prefer the line form, is that the line form makes the
transformation law visible: concurrency and parallelism are affine-invariant notions and an
affine change of coordinates acts on homogeneous line coordinates by the contragredient of its
matrix. Read as a *velocity*, i.e. as a Euclidean object, the velocity row has no affine
transformation law of its own, since the generator of rotations is not preserved by a shear. -/
theorem det_barVelRow (x y : Fin 3 → ℂ) :
    (Matrix.of fun i => barVelRow (x i) (y i)).det = barDet x y := by
  simp only [barDet, barMatrix, Matrix.det_fin_three, Matrix.of_apply, barVelRow, barRow,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ### The analytic core -/

/-- Cauchy–Schwarz in `ℝ²`, in coordinates. -/
theorem abs_dot_le (z w : ℂ) : |z.re * w.re + z.im * w.im| ≤ ‖z‖ * ‖w‖ := by
  have h : z.re * w.re + z.im * w.im = ((starRingEnd ℂ) z * w).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h]
  calc |((starRingEnd ℂ) z * w).re| ≤ ‖(starRingEnd ℂ) z * w‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]

/-- **The exact second-order expansion of one bar constraint.**

Write `d = X - Y` and `w = (1 - ρ) Y - τ`, so that `X - (ρ Y + τ) = d + w`. If both `d` and
`d + w` have length `2` then `2⟪d, w⟫ = -‖w‖²`, and `⟪d, w⟫` splits as the bar row of `X Y`
applied to the infinitesimal motion `(-τ.im, τ.re, ρ.im)`, plus `(1 - ρ.re) ⟪Y, d⟫`. Both of
the terms on the right are quadratically small when `ρ` is near `1` and `τ` near `0`. -/
theorem bar_expand (X Y ρ τ : ℂ) (hA : Complex.normSq (X - Y) = 4)
    (hB : Complex.normSq (X - (ρ * Y + τ)) = 4) :
    2 * ((X.im - Y.im) * (-τ.im) + (Y.re - X.re) * τ.re
          + (X.re * Y.im - X.im * Y.re) * ρ.im)
      = -Complex.normSq ((1 - ρ) * Y - τ)
        - 2 * (1 - ρ.re) * (Y.re * (X.re - Y.re) + Y.im * (X.im - Y.im)) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im] at hA hB ⊢
  linear_combination hB - hA

/-- **The quadratic estimate for one bar.** If the bar `X Y` of length `2` is still of length
`2` after the second end is moved by `z ↦ ρ z + τ`, and the infinitesimal motion
`(-τ.im, τ.re, ρ.im)` has size at most `t`, then the bar row applied to it is `O(t²)`.

The hypotheses `h1a` and `h1a2`, namely `0 ≤ 1 - ρ.re ≤ t²`, are what `‖ρ‖ = 1` provides near
`ρ = 1`; `B` is any bound for `‖Y‖ + 1`. -/
theorem bar_row_bound {X Y ρ τ : ℂ} {t B : ℝ}
    (hd : ‖X - Y‖ = 2) (hz : ‖X - (ρ * Y + τ)‖ = 2) (ht0 : 0 ≤ t)
    (h1a : 0 ≤ 1 - ρ.re) (h1a2 : 1 - ρ.re ≤ t ^ 2)
    (hrho : ‖1 - ρ‖ ≤ 2 * t) (htau : ‖τ‖ ≤ 2 * t)
    (hB1 : 1 ≤ B) (hBy : ‖Y‖ + 1 ≤ B) :
    |(X.im - Y.im) * (-τ.im) + (Y.re - X.re) * τ.re
        + (X.re * Y.im - X.im * Y.re) * ρ.im| ≤ 4 * B ^ 2 * t ^ 2 := by
  have hnsA : Complex.normSq (X - Y) = 4 := by rw [← Complex.sq_norm, hd]; norm_num
  have hnsB : Complex.normSq (X - (ρ * Y + τ)) = 4 := by rw [← Complex.sq_norm, hz]; norm_num
  have hid := bar_expand X Y ρ τ hnsA hnsB
  have hW0 : 0 ≤ Complex.normSq ((1 - ρ) * Y - τ) := Complex.normSq_nonneg _
  have hynn : (0 : ℝ) ≤ ‖Y‖ := norm_nonneg _
  -- the displacement of the second end is `O(t)`
  have hwnorm : ‖(1 - ρ) * Y - τ‖ ≤ 2 * t * B := by
    have h1 : ‖(1 - ρ) * Y - τ‖ ≤ ‖(1 - ρ) * Y‖ + ‖τ‖ := norm_sub_le _ _
    rw [norm_mul] at h1
    have h2 : ‖1 - ρ‖ * ‖Y‖ ≤ 2 * t * ‖Y‖ := mul_le_mul_of_nonneg_right hrho hynn
    have h4 : 0 ≤ t * (B - ‖Y‖ - 1) := mul_nonneg ht0 (by linarith)
    nlinarith
  have hWub : Complex.normSq ((1 - ρ) * Y - τ) ≤ 4 * t ^ 2 * B ^ 2 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg ((1 - ρ) * Y - τ)]
  -- the coefficient of the `ρ.re` direction is bounded
  have hGub : |Y.re * (X.re - Y.re) + Y.im * (X.im - Y.im)| ≤ 2 * B := by
    have h := abs_dot_le Y (X - Y)
    rw [Complex.sub_re, Complex.sub_im, hd] at h
    linarith
  have habs :
      |(1 - ρ.re) * (Y.re * (X.re - Y.re) + Y.im * (X.im - Y.im))| ≤ t ^ 2 * (2 * B) := by
    rw [abs_mul, abs_of_nonneg h1a]
    exact mul_le_mul h1a2 hGub (abs_nonneg _) (by positivity)
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hBsq : B * t ^ 2 ≤ B ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg t)
  have hBt : (0 : ℝ) ≤ B ^ 2 * t ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith [hid, hW0, hWub, hlo, hhi, hBsq, hBt]

/-- **The analytic core of R4.** Three bars `xᵢ yᵢ` of length `2` whose lines are not concurrent
and not all parallel (`barDet x y ≠ 0`) leave no room: for every rigid motion `z ↦ ρ z + τ` of
the plane close enough to the identity (`‖ρ‖ = 1`, and `(ρ, τ)` near `(1, 0)`) that keeps all
three bar lengths, `ρ = 1` and `τ = 0`.

The proof is the explicit quadratic estimate described in the module docstring: `bar_expand`
gives the exact identity, `bar_row_bound` the bound `|barRow · v| ≤ 4 B² ‖v‖²`, and
`barMatrix_ker_eq_bot` with `LinearMap.exists_antilipschitzWith` the reverse bound
`‖v‖ ≤ K ‖M v‖`. Either `v = 0` or `‖v‖ ≥ 1 / (4 K B²)`, and a small enough neighbourhood
excludes the second. No inverse function theorem and no exponential are used. -/
theorem eventually_eq_of_barDet_ne_zero {x y : Fin 3 → ℂ}
    (hbar : ∀ i, ‖x i - y i‖ = 2) (hdet : barDet x y ≠ 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (1, 0), ‖p.1‖ = 1 →
      (∀ i, ‖x i - (p.1 * y i + p.2)‖ = 2) → p.1 = 1 ∧ p.2 = 0 := by
  classical
  obtain ⟨K, hK0, hK⟩ :=
    LinearMap.exists_antilipschitzWith (barMatrix x y).mulVecLin (barMatrix_ker_eq_bot hdet)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
  -- a size bound for the moving piece
  obtain ⟨B, hB1, hBy⟩ : ∃ B : ℝ, 1 ≤ B ∧ ∀ i, ‖y i‖ + 1 ≤ B := by
    refine ⟨1 + ∑ i, ‖y i‖, ?_, fun i => ?_⟩
    · have : (0 : ℝ) ≤ ∑ i, ‖y i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
    · have := Finset.single_le_sum (f := fun j => ‖y j‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      linarith
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  have hden : (0 : ℝ) < 4 * K * B ^ 2 := mul_pos (by linarith) (pow_pos hBpos 2)
  set δ : ℝ := min 1 (1 / (4 * K * B ^ 2)) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (div_pos one_pos hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (4 * K * B ^ 2) := min_le_right _ _
  refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ0, ?_⟩
  rintro ⟨ρ, τ⟩ hdist
  change ‖ρ‖ = 1 → (∀ i, ‖x i - (ρ * y i + τ)‖ = 2) → ρ = 1 ∧ τ = 0
  intro hρ1 hkeep
  obtain ⟨hρd, hτd⟩ : ‖ρ - 1‖ < δ ∧ ‖τ‖ < δ := by
    rw [Prod.dist_eq, max_lt_iff] at hdist
    exact ⟨by simpa [Complex.dist_eq] using hdist.1, by simpa using hdist.2⟩
  -- coordinates of the motion
  have himρ : |ρ.im| < δ := by
    have h := Complex.abs_im_le_norm (ρ - 1)
    have e : (ρ - 1).im = ρ.im := by simp
    rw [e] at h
    linarith
  have hreρ : |ρ.re - 1| < δ := by
    have h := Complex.abs_re_le_norm (ρ - 1)
    have e : (ρ - 1).re = ρ.re - 1 := by simp
    rw [e] at h
    linarith
  have hreτ : |τ.re| < δ := lt_of_le_of_lt (Complex.abs_re_le_norm τ) hτd
  have himτ : |τ.im| < δ := lt_of_le_of_lt (Complex.abs_im_le_norm τ) hτd
  have ha0 : 0 < ρ.re := by
    have h := abs_lt.mp hreρ
    linarith
  have hnormρ : ρ.re * ρ.re + ρ.im * ρ.im = 1 := by
    have h : Complex.normSq ρ = 1 := by rw [← Complex.sq_norm, hρ1]; norm_num
    rwa [Complex.normSq_apply] at h
  have h1a : 0 ≤ 1 - ρ.re := by nlinarith [mul_self_nonneg ρ.im]
  -- the infinitesimal motion as a triple
  obtain ⟨v, hv0, hv1, hv2, hvlt⟩ :
      ∃ v : Fin 3 → ℝ, v 0 = -τ.im ∧ v 1 = τ.re ∧ v 2 = ρ.im ∧ ‖v‖ < δ := by
    refine ⟨![-τ.im, τ.re, ρ.im], by simp, by simp, by simp, ?_⟩
    rw [pi_norm_lt_iff hδ0]
    intro i
    fin_cases i
    · simpa using himτ
    · simpa using hreτ
    · simpa using himρ
  have hm0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hm1 : ‖v‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hvlt hδ1)
  have hbb : |ρ.im| ≤ ‖v‖ := by
    have h := norm_le_pi_norm v 2
    rwa [Real.norm_eq_abs, hv2] at h
  have hcc : |τ.re| ≤ ‖v‖ := by
    have h := norm_le_pi_norm v 1
    rwa [Real.norm_eq_abs, hv1] at h
  have hee : |τ.im| ≤ ‖v‖ := by
    have h := norm_le_pi_norm v 0
    rwa [Real.norm_eq_abs, hv0, abs_neg] at h
  -- the two quadratic hypotheses of `bar_row_bound`
  have h1a2 : 1 - ρ.re ≤ ‖v‖ ^ 2 := by
    have h := abs_le.mp hbb
    nlinarith
  have hrho : ‖1 - ρ‖ ≤ 2 * ‖v‖ := by
    have h := Complex.norm_le_abs_re_add_abs_im (1 - ρ)
    have e1 : (1 - ρ).re = 1 - ρ.re := by simp
    have e2 : (1 - ρ).im = -ρ.im := by simp
    rw [e1, e2, abs_of_nonneg h1a, abs_neg] at h
    have hsq : ‖v‖ ^ 2 ≤ ‖v‖ := by nlinarith
    linarith
  have htau : ‖τ‖ ≤ 2 * ‖v‖ := by
    have h := Complex.norm_le_abs_re_add_abs_im τ
    linarith
  -- the rows are quadratically small
  have hrow : ∀ i, |(barMatrix x y *ᵥ v) i| ≤ 4 * B ^ 2 * ‖v‖ ^ 2 := by
    intro i
    rw [barMatrix_mulVec_apply, hv0, hv1, hv2]
    exact bar_row_bound (hbar i) (hkeep i) hm0 h1a h1a2 hrho htau hB1 (hBy i)
  have hMv : ‖barMatrix x y *ᵥ v‖ ≤ 4 * B ^ 2 * ‖v‖ ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact hrow i
  -- so the motion is zero
  have hanti : ‖v‖ ≤ K * ‖barMatrix x y *ᵥ v‖ := by
    have h := hK.le_mul_dist v 0
    simpa [Matrix.mulVecLin_apply] using h
  have hfinal : ‖v‖ ≤ K * (4 * B ^ 2 * ‖v‖ ^ 2) :=
    hanti.trans (mul_le_mul_of_nonneg_left hMv hKR.le)
  have hvzero : ‖v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖v‖ := lt_of_le_of_ne hm0 (Ne.symm hne)
    have h2 : 1 ≤ 4 * K * B ^ 2 * ‖v‖ := by nlinarith
    have h3 : ‖v‖ < 1 / (4 * K * B ^ 2) := lt_of_lt_of_le hvlt hδ2
    rw [lt_div_iff₀ hden] at h3
    linarith
  have e0 : τ.im = 0 := by
    have h := norm_le_pi_norm v 0
    rw [Real.norm_eq_abs, hv0, abs_neg, hvzero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have e1 : τ.re = 0 := by
    have h := norm_le_pi_norm v 1
    rw [Real.norm_eq_abs, hv1, hvzero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have e2 : ρ.im = 0 := by
    have h := norm_le_pi_norm v 2
    rw [Real.norm_eq_abs, hv2, hvzero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  refine ⟨?_, ?_⟩
  · have hsq : ρ.re * ρ.re = 1 := by rw [e2] at hnormρ; linarith
    have hfac : (ρ.re - 1) * (ρ.re + 1) = 0 := by linarith [hsq]
    have ha1 : ρ.re = 1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith
    rw [Complex.ext_iff]
    exact ⟨by rw [Complex.one_re]; exact ha1, by rw [Complex.one_im]; exact e2⟩
  · rw [Complex.ext_iff]
    exact ⟨by rw [Complex.zero_re]; exact e1, by rw [Complex.zero_im]; exact e0⟩

/-! ### The lattice form: R4's side condition as integer arithmetic -/

/-- **Line coordinates of a lattice bar**, in lattice coordinates `(a, b)`: the line through
`p` and `q` is `{(a, b) | Az a + Bz b + Cz = 0}` with `barRowZ p q = (Az, Bz, Cz)`. -/
def barRowZ (p q : ℤ × ℤ) : ℤ × ℤ × ℤ := (p.2 - q.2, q.1 - p.1, p.1 * q.2 - p.2 * q.1)

/-- **R4's side condition as integer arithmetic.** The determinant of the three lattice bar
rows. It is `1 / 12` of the Euclidean `barDet` of the same three bars
(`barDet_latticePoint`), so `barDetZ ≠ 0` certifies `barDet ≠ 0` and is decidable. -/
def barDetZ (p q : Fin 3 → ℤ × ℤ) : ℤ :=
  (barRowZ (p 0) (q 0)).2.2 *
      ((barRowZ (p 1) (q 1)).1 * (barRowZ (p 2) (q 2)).2.1
        - (barRowZ (p 1) (q 1)).2.1 * (barRowZ (p 2) (q 2)).1)
    - (barRowZ (p 1) (q 1)).2.2 *
      ((barRowZ (p 0) (q 0)).1 * (barRowZ (p 2) (q 2)).2.1
        - (barRowZ (p 0) (q 0)).2.1 * (barRowZ (p 2) (q 2)).1)
    + (barRowZ (p 2) (q 2)).2.2 *
      ((barRowZ (p 0) (q 0)).1 * (barRowZ (p 1) (q 1)).2.1
        - (barRowZ (p 0) (q 0)).2.1 * (barRowZ (p 1) (q 1)).1)

/-- The velocity row of a lattice bar, in lattice coordinates. -/
def barVelRowZ (p q : ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (p.1 - q.1, p.2 - q.2, (p.1 - q.1) * q.2 - (p.2 - q.2) * q.1)

/-- Over `ℤ` too, the velocity form has the same determinant as the line form: it is the same
signed permutation of the same triple. See `det_barVelRow`. -/
theorem det_barVelRowZ (p q : Fin 3 → ℤ × ℤ) :
    (Matrix.of fun i => ![(barVelRowZ (p i) (q i)).1, (barVelRowZ (p i) (q i)).2.1,
      (barVelRowZ (p i) (q i)).2.2]).det = barDetZ p q := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, barVelRowZ, barRowZ, barDetZ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- Scaling the three columns of a `3 × 3` matrix by `s`, by `2` (after a shear by the first
column), and by `2 s` multiplies the determinant by `4 s ^ 2`. This is the change of
coordinates from lattice line coordinates to Euclidean line coordinates, column by column. -/
private theorem det_rows_scaled {R : Type*} [CommRing R] (s : R) (a b c : Fin 3 → R) :
    (Matrix.of fun i => ![s * a i, 2 * b i - a i, 2 * s * c i]).det
      = 4 * s ^ 2 * (Matrix.of fun i => ![a i, b i, c i]).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **How Euclidean line coordinates are built from lattice ones.** With
`latticePoint (a, b) = (2a + b, √3 b)`, the line coordinates of a lattice bar transform by

`A = √3 Az`,  `B = 2 Bz - Az`,  `C = 2 √3 Cz`.

No relation `√3 ^ 2 = 3` is used here; it enters only in the determinant. -/
theorem barRow_latticePoint (v w : ℤ × ℤ) :
    barRow (latticePoint v) (latticePoint w)
      = ![Real.sqrt 3 * ((barRowZ v w).1 : ℝ),
          2 * ((barRowZ v w).2.1 : ℝ) - ((barRowZ v w).1 : ℝ),
          2 * Real.sqrt 3 * ((barRowZ v w).2.2 : ℝ)] := by
  funext k
  fin_cases k <;>
    simp only [barRow, barRowZ, latticePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one] <;>
    push_cast <;> ring

/-- The bar matrix of a lattice placement, in terms of the integer rows. -/
theorem barMatrix_latticePoint (p q : Fin 3 → ℤ × ℤ) :
    barMatrix (latticePoint ∘ p) (latticePoint ∘ q)
      = Matrix.of fun i => ![Real.sqrt 3 * ((barRowZ (p i) (q i)).1 : ℝ),
          2 * ((barRowZ (p i) (q i)).2.1 : ℝ) - ((barRowZ (p i) (q i)).1 : ℝ),
          2 * Real.sqrt 3 * ((barRowZ (p i) (q i)).2.2 : ℝ)] := by
  ext i j
  simp only [barMatrix_apply, Matrix.of_apply, Function.comp_apply, barRow_latticePoint]

/-- The determinant of the integer rows, cast to `ℝ`, is `barDetZ`. -/
theorem det_barRowZ_cast (p q : Fin 3 → ℤ × ℤ) :
    (Matrix.of fun i => ![((barRowZ (p i) (q i)).1 : ℝ), ((barRowZ (p i) (q i)).2.1 : ℝ),
      ((barRowZ (p i) (q i)).2.2 : ℝ)]).det = (barDetZ p q : ℝ) := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, barDetZ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  push_cast
  ring

/-- **The constant is `12`.** For three bars with lattice endpoints,

`barDet (latticePoint ∘ p) (latticePoint ∘ q) = 12 * barDetZ p q`.

The factor is honest bookkeeping, not a guess: column by column the change of coordinates from
lattice line coordinates to Euclidean line coordinates is `A = √3 Az`, `B = 2 Bz - Az`,
`C = 2 √3 Cz` (`barRow_latticePoint`), whose matrix is lower triangular up to the shear and has
determinant `√3 * 2 * 2 √3 = 4 * 3 = 12`. (An earlier reconnaissance guessed `± 6`; that is
wrong. The `2` from the second column and the `2 √3` from the third contribute a factor `4`, and
the two `√3`s contribute the `3`.) -/
theorem barDet_latticePoint (p q : Fin 3 → ℤ × ℤ) :
    barDet (latticePoint ∘ p) (latticePoint ∘ q) = 12 * barDetZ p q := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc barDet (latticePoint ∘ p) (latticePoint ∘ q)
      = (Matrix.of fun i => ![Real.sqrt 3 * ((barRowZ (p i) (q i)).1 : ℝ),
          2 * ((barRowZ (p i) (q i)).2.1 : ℝ) - ((barRowZ (p i) (q i)).1 : ℝ),
          2 * Real.sqrt 3 * ((barRowZ (p i) (q i)).2.2 : ℝ)]).det := by
        rw [barDet, barMatrix_latticePoint]
    _ = 4 * Real.sqrt 3 ^ 2 * (Matrix.of fun i => ![((barRowZ (p i) (q i)).1 : ℝ),
          ((barRowZ (p i) (q i)).2.1 : ℝ), ((barRowZ (p i) (q i)).2.2 : ℝ)]).det :=
        det_rows_scaled _ _ _ _
    _ = 12 * (barDetZ p q : ℝ) := by rw [hs, det_barRowZ_cast]; ring

/-- **The decidable certificate.** A nonzero integer determinant certifies R4's side condition
for a lattice arrangement. -/
theorem barDet_ne_zero_of_barDetZ_ne_zero {p q : Fin 3 → ℤ × ℤ} (h : barDetZ p q ≠ 0) :
    barDet (latticePoint ∘ p) (latticePoint ∘ q) ≠ 0 := by
  rw [barDet_latticePoint]
  simpa using h

/-! ### Sanity checks on `barDetZ`, and the number behind `S20` -/

/-- Three parallel bars have vanishing determinant. -/
theorem barDetZ_parallel_example :
    barDetZ ![(0, 0), (0, 1), (0, 2)] ![(1, 0), (1, 1), (1, 2)] = 0 := by
  decide

/-- Three bars through one lattice point have vanishing determinant. -/
theorem barDetZ_concurrent_example :
    barDetZ ![(0, 0), (0, 0), (0, 0)] ![(1, 0), (0, 1), (1, -1)] = 0 := by
  decide

/-- A generic triple of contacts has nonvanishing determinant, so R4's side condition is not
vacuous. -/
theorem barDetZ_generic_example :
    barDetZ ![(0, 0), (0, 0), (0, 1)] ![(1, 0), (0, 1), (1, 1)] ≠ 0 := by
  decide

/-- **The number behind the smallest emergent arrangement.** `S20`, the `5 × 5` lattice block
minus `{(4,4), (4,0), (2,3), (1,2), (0,0)}`, splits into a `16`-circle triangle body and a
`4`-circle rhombus body joined by exactly the three contacts `(2,4)-(1,4)`, `(2,2)-(1,3)` and
`(0,3)-(0,2)`, whose lines in lattice coordinates are `b = 4`, `a + b = 4` and `a = 0`. Those
three lines meet at `(0, 4)` — itself a circle of the small body — so the determinant is `0`,
R4 cannot fire on that join, and no merging rule R1–R4 assembles `S20`. -/
theorem barDetZ_s20_cross_bars :
    barDetZ ![(2, 4), (2, 2), (0, 3)] ![(1, 4), (1, 3), (0, 2)] = 0 := by
  decide

/-- …and hence the Euclidean determinant of `S20`'s three cross bars vanishes too. -/
theorem barDet_s20_cross_bars :
    barDet (latticePoint ∘ ![(2, 4), (2, 2), (0, 3)])
      (latticePoint ∘ ![(1, 4), (1, 3), (0, 2)]) = 0 := by
  rw [barDet_latticePoint, barDetZ_s20_cross_bars]
  norm_num

/-- **The lattice certificate in the form a merge certificate needs.** If the centers of `A` are
the lattice points of the coordinates `f`, a nonzero integer determinant of the three bars'
lattice coordinates certifies R4's side condition for `A`. -/
theorem barDet_center_ne_zero_of_barDetZ {ι : Type*} {A : Arrangement ι} {f : ι → ℤ × ℤ}
    (hf : ∀ i, A.center i = latticePoint (f i)) {x y : Fin 3 → ι}
    (h : barDetZ (f ∘ x) (f ∘ y) ≠ 0) : barDet (A.center ∘ x) (A.center ∘ y) ≠ 0 := by
  have hcx : A.center ∘ x = latticePoint ∘ (f ∘ x) := funext fun k => hf (x k)
  have hcy : A.center ∘ y = latticePoint ∘ (f ∘ y) := funext fun k => hf (y k)
  rw [hcx, hcy]
  exact barDet_ne_zero_of_barDetZ_ne_zero h

namespace Arrangement

variable {ι : Type*}

/-! ### A cluster moves by one rigid motion -/

/-- **Step one of R4: a cluster moves by a single rigid motion of the plane.** If `S` is a
cluster containing two distinct circles `a` and `b`, then every contact-keeping placement close
enough to `A` acts on `S` as one map `z ↦ ρ z + τ` of the plane with `‖ρ‖ = 1` — and `(ρ, τ)`
may be required to lie in any prescribed neighbourhood `V` of `(1, 0)`.

R4 needs the neighbourhood: the analytic core `eventually_eq_of_barDet_ne_zero` is a statement
about motions *near* the identity, and a bare existential throws away the fact that the motion a
cluster undergoes is itself close to the identity when `q` is close to `A.center`.

**The orientation-reversing case really is excluded**, and nearness to the identity is what
excludes it. The normalising map `Φ q` used here is by construction a rotation and translation
(multiplication by a unit complex number, then a shift), so it is orientation-preserving; the
worry is that `q` restricted to `S` might be `A.center` followed by a *reflection*. If it were,
`Φ q` would be the identity map of the plane on the nose, and the pinning lemma
`eventually_forall_eq_of_dist_eq_of_dist_eq` then forces `q k = A.center k` for every `k ∈ S`
once `q` is close enough — because the mirror image of `A.center k` in the line through
`A.center a` and `A.center b` is either `A.center k` itself (when `k` lies on that line) or a
*fixed positive distance* away. So the reflected placement is either equal to the original on
`S`, in which case the conclusion holds with `ρ = 1`, `τ = 0`, or excluded by nearness. In
particular R4 does **not** need `‖ρ‖ = 1` weakened to "`ρ` or its conjugate".

The proof is the normalisation of `Arrangement.rigidIn_of_dist_two` read backwards: pin `S` with
`Φ q`, then invert `Φ q`, whose inverse is `z ↦ ρ z + τ` with
`ρ = (q b - q a) / (A.center b - A.center a)`. -/
theorem RigidIn.exists_rigid_motion_mem [Finite ι] {A : Arrangement ι} {S : Set ι}
    (h : A.RigidIn S) {a b : ι} (haS : a ∈ S) (hbS : b ∈ S) (hab : a ≠ b)
    {V : Set (ℂ × ℂ)} (hV : V ∈ 𝓝 ((1 : ℂ), (0 : ℂ))) :
    ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q →
      ∃ ρ τ : ℂ, (ρ, τ) ∈ V ∧ ‖ρ‖ = 1 ∧ ∀ i ∈ S, q i = ρ * A.center i + τ := by
  have := Fintype.ofFinite ι
  have h' : ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q →
      ∀ i ∈ S, ∀ j ∈ S, dist (q i) (q j) = dist (A.center i) (A.center j) := h
  set p := A.center with hp
  have hne : p a ≠ p b := A.center_injective.ne hab
  have hd : p b - p a ≠ 0 := sub_ne_zero.mpr hne.symm
  let Φ : (ι → Plane) → (ι → Plane) := fun q k =>
    p a + (p b - p a) / (q b - q a) * (q k - q a)
  have hΦp : Φ p = p := by
    funext k
    simp only [Φ]
    field_simp
    ring
  have hΦc : ContinuousAt Φ p := by
    refine continuousAt_pi.2 fun k => ?_
    have hden : (fun q : ι → Plane => q b - q a) p ≠ 0 := hd
    have c1 : ContinuousAt (fun q : ι → Plane => q b - q a) p := by fun_prop
    have c2 : ContinuousAt (fun q : ι → Plane => q k - q a) p := by fun_prop
    exact continuousAt_const.add ((continuousAt_const.div c1 hden).mul c2)
  have hTend : Tendsto Φ (𝓝 p) (𝓝 p) := by
    have := hΦc.tendsto
    rwa [hΦp] at this
  have hpin := hTend.eventually (eventually_forall_eq_of_dist_eq_of_dist_eq (p := p) hne)
  -- the rigid motion that `q` induces on `S` depends continuously on `q` and is the identity
  -- at `q = p`, so it stays in any prescribed neighbourhood `V` of `(1, 0)`
  have ca : ContinuousAt (fun q : ι → Plane => q a) p := (continuous_apply a).continuousAt
  have cb : ContinuousAt (fun q : ι → Plane => q b) p := (continuous_apply b).continuousAt
  have c1 : ContinuousAt (fun q : ι → Plane => (q b - q a) / (p b - p a)) p :=
    (cb.sub ca).div continuousAt_const hd
  have hR : ContinuousAt (fun q : ι → Plane => ((q b - q a) / (p b - p a),
      q a - (q b - q a) / (p b - p a) * p a)) p :=
    c1.prodMk (ca.sub (c1.mul continuousAt_const))
  have hRmem : (fun q : ι → Plane => ((q b - q a) / (p b - p a),
      q a - (q b - q a) / (p b - p a) * p a)) ⁻¹' V ∈ 𝓝 p := by
    refine hR.preimage_mem_nhds ?_
    simp only [div_self hd, one_mul, sub_self]
    exact hV
  filter_upwards [hpin, h', hRmem] with q hq hr hmem hk
  have hc := hr hk
  have hqab : dist (q b) (q a) = dist (p b) (p a) := hc b hbS a haS
  have hq0 : q b - q a ≠ 0 := by
    intro h0
    rw [dist_eq_norm, h0, norm_zero, eq_comm, dist_eq_zero] at hqab
    exact hne hqab.symm
  have hΦdist : ∀ k l, dist (Φ q k) (Φ q l) = dist (q k) (q l) := by
    have hρn : ‖(p b - p a) / (q b - q a)‖ = 1 := by
      rw [norm_div, ← dist_eq_norm, ← dist_eq_norm, hqab, div_self]
      exact dist_ne_zero.mpr hne.symm
    intro k l
    simp only [Φ, dist_eq_norm]
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hρn, one_mul, sub_sub_sub_cancel_right]
  have hΦa : Φ q a = p a := by simp [Φ]
  have hΦb : Φ q b = p b := by
    simp only [Φ]
    field_simp
    ring
  have hfix : ∀ k l, Φ q l = p l → dist (Φ q k) (p l) = dist (q k) (q l) := fun k l hl => by
    rw [← hl, hΦdist]
  have pin : ∀ k ∈ S, Φ q k = p k := fun k hkS =>
    hq k (by rw [hfix _ _ hΦa]; exact hc k hkS a haS)
      (by rw [hfix _ _ hΦb]; exact hc k hkS b hbS)
  refine ⟨(q b - q a) / (p b - p a), q a - (q b - q a) / (p b - p a) * p a, hmem, ?_,
    fun i hi => ?_⟩
  · rw [norm_div, ← dist_eq_norm, ← dist_eq_norm, hqab, div_self]
    exact dist_ne_zero.mpr hne.symm
  · have hpi : p a + (p b - p a) / (q b - q a) * (q i - q a) = p i := pin i hi
    have hρα : (q b - q a) / (p b - p a) * ((p b - p a) / (q b - q a)) = 1 := by
      field_simp
    linear_combination ((q b - q a) / (p b - p a)) * hpi - (q i - q a) * hρα

/-- **A cluster moves by a single rigid motion**, in plain existential form: the `V = Set.univ`
case of `RigidIn.exists_rigid_motion_mem`. -/
theorem RigidIn.exists_rigid_motion [Finite ι] {A : Arrangement ι} {S : Set ι}
    (h : A.RigidIn S) {a b : ι} (haS : a ∈ S) (hbS : b ∈ S) (hab : a ≠ b) :
    ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q →
      ∃ ρ τ : ℂ, ‖ρ‖ = 1 ∧ ∀ i ∈ S, q i = ρ * A.center i + τ := by
  filter_upwards [h.exists_rigid_motion_mem haS hbS hab (V := Set.univ) univ_mem] with q hq hk
  obtain ⟨ρ, τ, -, hρ, hmap⟩ := hq hk
  exact ⟨ρ, τ, hρ, hmap⟩

/-- The converse: a set that moves by one rigid motion along every small contact-keeping motion
is a cluster. (No finiteness and no two distinct circles needed.) -/
theorem rigidIn_of_exists_rigid_motion {A : Arrangement ι} {S : Set ι}
    (h : ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q →
      ∃ ρ τ : ℂ, ‖ρ‖ = 1 ∧ ∀ i ∈ S, q i = ρ * A.center i + τ) : A.RigidIn S := by
  filter_upwards [h] with q hq hk i hi j hj
  obtain ⟨ρ, τ, hρ, hmap⟩ := hq hk
  rw [dist_eq_norm, dist_eq_norm, hmap i hi, hmap j hj,
    show ρ * A.center i + τ - (ρ * A.center j + τ) = ρ * (A.center i - A.center j) from by ring,
    norm_mul, hρ, one_mul]

/-- **Relative rigidity is exactly the rigid-motion normal form.** For a set with at least two
circles, being a cluster is the same as moving by a single rotation-and-translation of the plane
along every small contact-keeping motion. This is the form in which R4 uses a cluster. -/
theorem rigidIn_iff_exists_rigid_motion [Finite ι] {A : Arrangement ι} {S : Set ι}
    (hS : S.Nontrivial) :
    A.RigidIn S ↔ ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q →
      ∃ ρ τ : ℂ, ‖ρ‖ = 1 ∧ ∀ i ∈ S, q i = ρ * A.center i + τ := by
  obtain ⟨a, haS, b, hbS, hab⟩ := hS
  exact ⟨fun h => h.exists_rigid_motion haS hbS hab, rigidIn_of_exists_rigid_motion⟩

/-! ### R4: two clusters joined by three bars in general position -/

/-- **Rule R4.** Two clusters `S` and `T` joined by three contacts `xᵢ yᵢ`, with `xᵢ ∈ S` and
`yᵢ ∈ T`, merge into one — provided the three bars are in general position, meaning
`barDet ≠ 0`: not all concurrent and not all parallel (`barDet_eq_zero_iff`).

Unlike R1, R2 and R3 this rule *has* a non-degeneracy condition, and it cannot be dispensed
with: the whole point of `S20` (`barDetZ_s20_cross_bars`) is that three concurrent cross bars
leave a genuine first-order motion, so there is nothing to prove in that case. The condition is
exactly the invertibility of the three-by-three system that the three bar lengths impose on the
three-parameter group of rigid motions of the plane.

**No nontriviality hypothesis on `S` or `T` is needed.** One might expect to have to assume that
each of the two clusters contains two distinct circles, since the rigid-motion normal form
`RigidIn.exists_rigid_motion_mem` needs two circles to normalise against. It comes for free: if
all three bars started at the same circle, their three lines would be concurrent there and the
determinant would vanish (`exists_ne_left_of_barDet_ne_zero`, and symmetrically
`exists_ne_right_of_barDet_ne_zero`). So the determinant hypothesis does that work too.

The assembly. Each of `S` and `T` moves by one rigid motion, `z ↦ ρ_S z + τ_S` and
`z ↦ ρ_T z + τ_T`, both close to the identity; the *relative* motion is `ρ = ρ_T / ρ_S`,
`τ = (τ_T - τ_S) / ρ_S`, obtained by dividing the contact equation
`‖(ρ_S xᵢ + τ_S) - (ρ_T yᵢ + τ_T)‖ = 2` by `ρ_S`, which is harmless because `‖ρ_S‖ = 1`. The
analytic core then forces `ρ = 1` and `τ = 0`, that is `ρ_T = ρ_S` and `τ_T = τ_S`: one motion
serves all of `S ∪ T`, and `rigidIn_of_exists_rigid_motion` turns that back into a cluster. The
one subtlety is choosing the neighbourhoods: the relative motion depends continuously on the two
motions and is the identity when both are, so the core's neighbourhood of `(1, 0)` pulls back to
a product of neighbourhoods, one for each cluster. -/
theorem RigidIn.union_of_three_bars [Finite ι] {A : Arrangement ι} {S T : Set ι}
    (hS : A.RigidIn S) (hT : A.RigidIn T) (x y : Fin 3 → ι)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ T)
    (hbar : ∀ i, Tangent A.center (x i) (y i))
    (hdet : barDet (A.center ∘ x) (A.center ∘ y) ≠ 0) :
    A.RigidIn (S ∪ T) := by
  -- the three bars, as bars of the plane
  have hbar' : ∀ i, ‖(A.center ∘ x) i - (A.center ∘ y) i‖ = 2 := by
    intro i
    rw [Function.comp_apply, Function.comp_apply, ← dist_eq_norm]
    exact hbar i
  have hbne : ∀ i, (A.center ∘ x) i ≠ (A.center ∘ y) i := fun i he => by
    have h := hbar' i
    rw [he, sub_self, norm_zero] at h
    norm_num at h
  -- nontriviality of the two clusters, for free from the determinant
  obtain ⟨i₁, i₂, hix⟩ := exists_ne_left_of_barDet_ne_zero hbne hdet
  obtain ⟨j₁, j₂, hjy⟩ := exists_ne_right_of_barDet_ne_zero hbne hdet
  have hxne : x i₁ ≠ x i₂ := fun he => hix (by
    simp only [Function.comp_apply]; rw [he])
  have hyne : y j₁ ≠ y j₂ := fun he => hjy (by
    simp only [Function.comp_apply]; rw [he])
  -- the relative motion depends continuously on the two motions, and is the identity when
  -- both of them are
  have htend : Tendsto (fun z : (ℂ × ℂ) × (ℂ × ℂ) => (z.2.1 / z.1.1, (z.2.2 - z.1.2) / z.1.1))
      (𝓝 ((((1 : ℂ), (0 : ℂ)), ((1 : ℂ), (0 : ℂ))) : (ℂ × ℂ) × (ℂ × ℂ)))
      (𝓝 ((1 : ℂ), (0 : ℂ))) := by
    have hid : ContinuousAt (fun z : (ℂ × ℂ) × (ℂ × ℂ) => z)
        ((((1 : ℂ), (0 : ℂ)), ((1 : ℂ), (0 : ℂ))) : (ℂ × ℂ) × (ℂ × ℂ)) := continuousAt_id
    have hden : ((((1 : ℂ), (0 : ℂ)), ((1 : ℂ), (0 : ℂ))) : (ℂ × ℂ) × (ℂ × ℂ)).1.1 ≠ 0 :=
      one_ne_zero
    have hc := ((hid.snd.fst.div hid.fst.fst hden).prodMk
      ((hid.snd.snd.sub hid.fst.snd).div hid.fst.fst hden)).tendsto
    simpa using hc
  -- so the core's neighbourhood of the identity pulls back to a product of neighbourhoods
  have hev := htend.eventually (eventually_eq_of_barDet_ne_zero hbar' hdet)
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hsub⟩ := hev
  -- each cluster moves by one rigid motion, inside its own neighbourhood
  refine rigidIn_of_exists_rigid_motion ?_
  filter_upwards [hS.exists_rigid_motion_mem (hx i₁) (hx i₂) hxne (V := {z | pa z}) hpa,
    hT.exists_rigid_motion_mem (hy j₁) (hy j₂) hyne (V := {z | pb z}) hpb] with q hqS hqT hk
  obtain ⟨ρS, τS, hmemS, hρS, hmapS⟩ := hqS hk
  obtain ⟨ρT, τT, hmemT, hρT, hmapT⟩ := hqT hk
  have hρS0 : ρS ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hρS
    exact zero_ne_one hρS
  have hinv : ρS * ρS⁻¹ = 1 := mul_inv_cancel₀ hρS0
  -- the relative motion keeps all three bar lengths: divide the contact equation by `ρS`
  have hkeep : ∀ i, ‖(A.center ∘ x) i
      - (ρT / ρS * (A.center ∘ y) i + (τT - τS) / ρS)‖ = 2 := by
    intro i
    have hcon : dist (q (x i)) (q (y i)) = 2 := hk _ _ (hbar i)
    rw [hmapS _ (hx i), hmapT _ (hy i), dist_eq_norm] at hcon
    have he : ρS * A.center (x i) + τS - (ρT * A.center (y i) + τT)
        = ρS * ((A.center ∘ x) i - (ρT / ρS * (A.center ∘ y) i + (τT - τS) / ρS)) := by
      simp only [Function.comp_apply, div_eq_mul_inv]
      linear_combination (ρT * A.center (y i) + τT - τS) * hinv
    rw [he, norm_mul, hρS, one_mul] at hcon
    exact hcon
  -- so it is the identity, by the analytic core
  obtain ⟨hρ1, hτ0⟩ := hsub hmemS hmemT (by rw [norm_div, hρT, hρS, div_one]) hkeep
  have hρeq : ρT = ρS := by
    rw [div_eq_iff hρS0, one_mul] at hρ1
    exact hρ1
  have hτeq : τT = τS := by
    rcases div_eq_zero_iff.mp hτ0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hρS0
  refine ⟨ρS, τS, hρS, ?_⟩
  rintro i (hiS | hiT)
  · exact hmapS i hiS
  · rw [hmapT i hiT, hρeq, hτeq]

/-- **Rule R4 on the lattice.** If the centers of `A` are the lattice points of the coordinates
`f`, the side condition of `Arrangement.RigidIn.union_of_three_bars` becomes the integer
inequality `barDetZ (f ∘ x) (f ∘ y) ≠ 0`, which `decide` settles. -/
theorem RigidIn.union_of_three_bars_lattice [Finite ι] {A : Arrangement ι} {S T : Set ι}
    (hS : A.RigidIn S) (hT : A.RigidIn T) {f : ι → ℤ × ℤ}
    (hf : ∀ i, A.center i = latticePoint (f i)) (x y : Fin 3 → ι)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ T)
    (hbar : ∀ i, Tangent A.center (x i) (y i))
    (hdet : barDetZ (f ∘ x) (f ∘ y) ≠ 0) :
    A.RigidIn (S ∪ T) :=
  hS.union_of_three_bars hT x y hx hy hbar (barDet_center_ne_zero_of_barDetZ hf hdet)

end Arrangement

end RigidArrangements
