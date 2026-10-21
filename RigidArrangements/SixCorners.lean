import RigidArrangements.CornerBasics

/-!
# Six corners: the equiangular hexagon and its hub

This file formalizes Section 3 of `docs/cores.md` ("Exactly six corners"): Lemma S and
Proposition H.

## Setting S6

Let `A` be a finite arrangement in which every circle touches at least two others
(`Arrangement.TouchesTwo`) and no circle is removable (`Arrangement.IsCore`). By the hull lemma
(`Arrangement.exists_injective_isExtreme`) there are six different circles `e₀, …, e₅` with
`eₖ` extreme in direction `k · 60°`. Setting S6 is the case where these six circles are all the
corners (circles extreme in some direction, `Arrangement.IsCorner`). Indices are taken modulo
`6` (`Fin 6`), and `ρ = e^{iπ/3}` (`RigidArrangements.rho`).

## Lemma S: an equiangular hexagon

In setting S6 there are a unit complex number `ω` and side lengths `L₀, …, L₅ ≥ 2` such that,
writing `ωₖ = ω ρᵏ` (`Arrangement.IsSixCornerFrame`, `Arrangement.exists_isSixCornerFrame`):

* (S-a) `eₖ₊₁ - eₖ = Lₖ ωₖ`: the corners form a convex hexagon that turns by exactly `60°` at
  each corner;
* (S-b) `cross ωₖ (p - eₖ) ≥ 0` for every center `p`: each side lies on a supporting line, with
  all centers on its left;
* (S-c) the three neighbours of `eₖ` are centered at `eₖ + 2ωₖ`, `eₖ + 2ρωₖ` and `eₖ + 2ρ²ωₖ`.

The proof follows the extreme circle `E(θ)` as the direction `θ` turns.

* **Step 1.** On the arc `[k · 60°, (k + 1) · 60°]` only `eₖ` and `eₖ₊₁` can be extreme: a
  circle is extreme only in directions less than `60°` apart (modulo `360°`).
* **Step 2.** The switch from `eₖ` to `eₖ₊₁` happens at the angle `τₖ ∈ (k · 60°, (k + 1) · 60°]`
  perpendicular to the side `eₖ₊₁ - eₖ`, which therefore has direction `τₖ + 90°`.
* **Step 3.** The corner `eₖ` is extreme from `τₖ₋₁` to `τₖ`, a range narrower than `60°` beyond
  its start, so `τₖ - τₖ₋₁ ≤ 60°`. The six differences add up to `360°` (a telescoping sum), so
  each one is exactly `60°`.
* **Step 4.** `eₖ₊₁` is extreme in direction `τₖ`: every center lies on the left of side `k`.
* **Step 5.** Seen from `eₖ`, the neighbours lie on the left of both sides at `eₖ`, an arc of
  `120°`; three of them, pairwise at least `60°` apart, sit at its ends and its middle.

## Proposition H: the hub

If moreover at most two circles are not corners, then all six sides have length `2`, and the
arrangement contains the flower: a seventh circle `o`, not a corner, touches all six corners,
these touch nothing else but their two neighbours on the hexagon, and `eₖ = o + 2 ζ ρᵏ` with
`ζ = ω ρ⁴`. The steps are:

* (H1) `Arrangement.IsSixCornerFrame.closure`: the hexagon closes up, so
  `L₀ - L₃ = L₂ - L₅ = L₄ - L₁`;
* (H2) `Arrangement.IsSixCornerFrame.exists_mid`, `Arrangement.IsSixCornerFrame.exists_mid'`,
  `Arrangement.IsSixCornerFrame.eq_four_or_six_le`: on a side longer than `2`, the neighbours
  `eₖ + 2ωₖ` and `eₖ₊₁ - 2ωₖ` of its two ends lie inside the side, so they are not corners, and
  the side has length `4` or at least `6`;
* (H3) `Arrangement.IsSixCornerFrame.eq_of_mem_openSegment`: two different open sides do not
  meet;
* (H4) `Arrangement.IsSixCornerFrame.sides_eq_two`: with at most two non-corners, every side has
  length `2`. Otherwise three non-corners appear: on three long sides, or on two opposite sides
  one of which has length other than `4`, or, for the hexagon with sides `4, 2, 2, 4, 2, 2`,
  the neighbour `eₖ + 2ρωₖ` of the corner between the sides `4` and `2`;
* (H5) `Arrangement.IsSixCornerFrame.exists_hub`: when all sides have length `2`, the points
  `eₖ + 2ρωₖ` all coincide, at the center of a common neighbour `o` of the six corners.

## Main results

* `Arrangement.IsSixCornerFrame`, `Arrangement.exists_isSixCornerFrame`: Lemma S.
* `Arrangement.IsSixCornerFrame.sides_eq_two`, `Arrangement.IsSixCornerFrame.exists_hub` and
  their combination `Arrangement.IsSixCornerFrame.exists_hub_of_few`: Proposition H.
-/

open Complex

namespace RigidArrangements

/-! ### Powers of `ρ` indexed by `Fin 6` -/

/-- Powers of `ρ` with exponents in `Fin 6` multiply like powers with natural exponents. -/
theorem rho_pow_val_add (k m : Fin 6) :
    rho ^ ((k + m : Fin 6) : ℕ) = rho ^ (k : ℕ) * rho ^ (m : ℕ) := by
  rw [Fin.val_add, rho_pow_mod_six, pow_add]

private theorem rho_pow_val_add_one (k : Fin 6) :
    rho ^ ((k + 1 : Fin 6) : ℕ) = rho ^ (k : ℕ) * rho := by
  rw [rho_pow_val_add, Fin.val_one, pow_one]

private theorem rho_pow_val_add_three (k : Fin 6) :
    rho ^ ((k + 3 : Fin 6) : ℕ) = -rho ^ (k : ℕ) := by
  rw [rho_pow_val_add, show ((3 : Fin 6) : ℕ) = 3 from rfl, rho_pow_three, mul_neg_one]

private theorem rho_pow_val_sub_one (k : Fin 6) :
    rho ^ (k : ℕ) = rho ^ ((k - 1 : Fin 6) : ℕ) * rho := by
  rw [← rho_pow_val_add_one, sub_add_cancel]

private theorem norm_mul_rho_pow {ω : ℂ} (hω : ‖ω‖ = 1) (n : ℕ) : ‖ω * rho ^ n‖ = 1 := by
  rw [norm_mul, norm_pow, norm_rho, one_pow, hω, one_mul]

private theorem rho_ne_one : rho ≠ 1 := fun h => by
  have := congrArg Complex.re h
  norm_num at this

/-- In `Fin 6`, adding a nonzero element changes every element. -/
private theorem fin_add_ne {k m : Fin 6} (hm : m ≠ 0) : k + m ≠ k :=
  fun h => hm (by simpa using h)

/-! ### Plane geometry -/

/-- If `p₁ = p₀ + L w`, then `cross w (x - p₀) = cross w (x - p₁)`: the signed distance to a
line does not depend on the base point on the line. -/
private theorem cross_sub_eq_of_eq_add {w p₀ p₁ x : ℂ} {L : ℝ} (h : p₁ = p₀ + L * w) :
    cross w (x - p₀) = cross w (x - p₁) := by
  rw [show x - p₀ = (x - p₁) + L * w by rw [h]; ring, cross_add_right, cross_ofReal_mul_right,
    cross_self, mul_zero, add_zero]

/-- Three points on the line through `c` with direction `w ≠ 0` are collinear. -/
private theorem cross_eq_zero_of_cross_eq_zero {w c x y z : ℂ} (hw : w ≠ 0)
    (hx : cross w (x - c) = 0) (hy : cross w (y - c) = 0) (hz : cross w (z - c) = 0) :
    cross (y - x) (z - x) = 0 := by
  obtain ⟨s, hs⟩ := (cross_eq_zero_iff hw).mp hx
  obtain ⟨t, ht⟩ := (cross_eq_zero_iff hw).mp hy
  obtain ⟨u, hu⟩ := (cross_eq_zero_iff hw).mp hz
  rw [show y - x = ((t - s : ℝ) : ℂ) * w by push_cast; linear_combination ht - hs,
    show z - x = ((u - s : ℝ) : ℂ) * w by push_cast; linear_combination hu - hs,
    cross_ofReal_mul_left, cross_ofReal_mul_right, cross_self, mul_zero, mul_zero]

/-- For `-90° < α < 270°`, the unit vector of angle `α` is lexicographically positive exactly
when `α ≤ 90°`. -/
private theorem lexPos_cond_iff {α : ℝ} (h1 : -(Real.pi / 2) < α) (h2 : α < 3 * (Real.pi / 2)) :
    (0 < Real.cos α ∨ (Real.cos α = 0 ∧ 0 < Real.sin α)) ↔ α ≤ Real.pi / 2 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have := Real.cos_neg_of_pi_div_two_lt_of_lt hlt (by linarith)
    rcases h with h | ⟨h, -⟩ <;> linarith
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact Or.inl (Real.cos_pos_of_mem_Ioo ⟨h1, h⟩)
    · exact Or.inr ⟨Real.cos_pi_div_two, by rw [Real.sin_pi_div_two]; norm_num⟩

/-- A vector of length `L > 0` and direction `β`, rotated by `-θ`, is lexicographically positive
exactly when `β - θ ≤ 90°`, provided `-90° < β - θ < 270°`. -/
private theorem lexPos_mul_exp_mul_exp_iff {L β θ : ℝ} (hL : 0 < L)
    (h1 : -(Real.pi / 2) < β - θ) (h2 : β - θ < 3 * (Real.pi / 2)) :
    LexPos (↑L * exp (↑β * I) * exp (↑(-θ) * I)) ↔ β - θ ≤ Real.pi / 2 := by
  have e : (↑L * exp (↑β * I) * exp (↑(-θ) * I) : ℂ) = ↑L * exp (↑(β - θ) * I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, ← lexPos_cond_iff h1 h2, LexPos, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (pos_of_mul_pos_right h hL.le)
    · exact Or.inr ⟨(mul_eq_zero.mp h1).resolve_left hL.ne', pos_of_mul_pos_right h2 hL.le⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (mul_pos hL h)
    · exact Or.inr ⟨by rw [h1, mul_zero], mul_pos hL h2⟩

/-- Rotating by `-τ` and taking the real part measures the signed distance to a line of
direction `τ + 90°`: `cross (e^{i(τ + π/2)}) z = Re (-z e^{-iτ})`. -/
private theorem cross_exp_add_pi_div_two (τ : ℝ) (z : ℂ) :
    cross (exp (↑(τ + Real.pi / 2) * I)) z = (-z * exp (↑(-τ) * I)).re := by
  simp only [cross, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Real.cos_neg, Real.sin_neg]
  ring

/-- `Im (ρ z) = |z| sin (arg z + 60°)`. -/
private theorem im_rho_mul (z : ℂ) : (rho * z).im = ‖z‖ * Real.sin (arg z + Real.pi / 3) := by
  rw [Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three, Complex.mul_im, rho_re, rho_im,
    ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z]
  ring

/-- A direction `a ≤ 180°` with `sin (a + 60°) ≥ 0` is at most `120°`. -/
private theorem le_two_mul_pi_div_three {a : ℝ} (ha : a ≤ Real.pi)
    (h : 0 ≤ Real.sin (a + Real.pi / 3)) : a ≤ 2 * (Real.pi / 3) := by
  by_contra hlt
  push Not at hlt
  have : 0 < Real.sin (a + Real.pi / 3 - Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub_pi] at this
  linarith

/-- Three reals in `[0°, 120°]`, pairwise at least `60°` apart: the first one is `0°`, `60°` or
`120°`. -/
private theorem exists_eq_of_three_sep {a b c : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2 * (Real.pi / 3))
    (hb : 0 ≤ b) (hb' : b ≤ 2 * (Real.pi / 3)) (hc : 0 ≤ c) (hc' : c ≤ 2 * (Real.pi / 3))
    (hab : Real.pi / 3 ≤ |a - b|) (hac : Real.pi / 3 ≤ |a - c|) (hbc : Real.pi / 3 ≤ |b - c|) :
    ∃ j : Fin 3, a = (j : ℕ) * Real.pi / 3 := by
  have hπ := Real.pi_pos
  have h : a = 0 ∨ a = Real.pi / 3 ∨ a = 2 * (Real.pi / 3) := by
    rcases le_abs.mp hab with h1 | h1 <;> rcases le_abs.mp hac with h2 | h2 <;>
      rcases le_abs.mp hbc with h3 | h3 <;>
      first
      | (exfalso; linarith)
      | exact Or.inl (by linarith)
      | exact Or.inr (Or.inl (by linarith))
      | exact Or.inr (Or.inr (by linarith))
  rcases h with h | h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · exact ⟨2, by simp [h]; ring⟩

/-- Three reals in `[0°, 120°]`, pairwise at least `60°` apart: each of `0°`, `60°` and `120°`
is one of them. -/
private theorem hit_of_three_sep {a b c : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2 * (Real.pi / 3))
    (hb : 0 ≤ b) (hb' : b ≤ 2 * (Real.pi / 3)) (hc : 0 ≤ c) (hc' : c ≤ 2 * (Real.pi / 3))
    (hab : Real.pi / 3 ≤ |a - b|) (hac : Real.pi / 3 ≤ |a - c|) (hbc : Real.pi / 3 ≤ |b - c|)
    (j : Fin 3) :
    a = (j : ℕ) * Real.pi / 3 ∨ b = (j : ℕ) * Real.pi / 3 ∨ c = (j : ℕ) * Real.pi / 3 := by
  have hπ := Real.pi_pos
  have hj : ((j : ℕ) : ℝ) * Real.pi / 3 = 0 ∨ ((j : ℕ) : ℝ) * Real.pi / 3 = Real.pi / 3 ∨
      ((j : ℕ) : ℝ) * Real.pi / 3 = 2 * (Real.pi / 3) := by
    fin_cases j
    · left; simp
    · right; left; simp
    · right; right; simp; ring
  rcases hj with hj | hj | hj <;> rw [hj] <;>
    rcases le_abs.mp hab with h1 | h1 <;> rcases le_abs.mp hac with h2 | h2 <;>
      rcases le_abs.mp hbc with h3 | h3 <;>
      first
      | (exfalso; linarith)
      | exact Or.inl (by linarith)
      | exact Or.inr (Or.inl (by linarith))
      | exact Or.inr (Or.inr (by linarith))

namespace Arrangement

variable {ι : Type*} {A : Arrangement ι}

/-! ### Lemma S: the statement -/

variable (A) in
/-- **Lemma S**, the conclusion: the six corners `e₀, …, e₅` of `A` form an equiangular hexagon
with unit direction `ω` (side `k` has direction `ωₖ = ω ρᵏ`) and side lengths `L₀, …, L₅`.

* `injective`, `isCorner_iff`: the `eₖ` are six different circles, and they are all the corners;
* `two_le`, `side` (S-a): `eₖ₊₁ = eₖ + Lₖ ωₖ` with `Lₖ ≥ 2`;
* `support` (S-b): every center lies on the left of each side line;
* `adj_iff`, `exists_nbr` (S-c): the neighbours of `eₖ` are exactly the circles centered at
  `eₖ + 2 ωₖ ρʲ` for `j = 0, 1, 2`, and each of these three points is a center. -/
structure IsSixCornerFrame (e : Fin 6 → ι) (ω : ℂ) (L : Fin 6 → ℝ) : Prop where
  /-- The six corners are different. -/
  injective : Function.Injective e
  /-- The `eₖ` are exactly the corners. -/
  isCorner_iff : ∀ i, A.IsCorner i ↔ i ∈ Set.range e
  /-- The direction `ω` of side `0` is a unit vector. -/
  norm_eq_one : ‖ω‖ = 1
  /-- Every side has length at least `2`. -/
  two_le : ∀ k, 2 ≤ L k
  /-- (S-a) Side `k` goes from `eₖ` to `eₖ₊₁ = eₖ + Lₖ ω ρᵏ`. -/
  side : ∀ k : Fin 6, A.center (e (k + 1)) = A.center (e k) + L k * (ω * rho ^ (k : ℕ))
  /-- (S-b) Every center lies on the left of each side line. -/
  support : ∀ (k : Fin 6) (i : ι), 0 ≤ cross (ω * rho ^ (k : ℕ)) (A.center i - A.center (e k))
  /-- (S-c) The neighbours of `eₖ` are centered at `eₖ + 2 ω ρᵏ⁺ʲ`, `j = 0, 1, 2`. -/
  adj_iff : ∀ (k : Fin 6) (i : ι), A.contactGraph.Adj (e k) i ↔
    ∃ j : Fin 3, A.center i = A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + (j : ℕ)))
  /-- (S-c) Each of the three points `eₖ + 2 ω ρᵏ⁺ʲ` is a center. -/
  exists_nbr : ∀ (k : Fin 6) (j : Fin 3), ∃ i,
    A.center i = A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + (j : ℕ)))

/-! ### Lemma S, Step 5: the neighbours of a corner -/

section Step5

variable {e : Fin 6 → ι} {ω : ℂ} {L : Fin 6 → ℝ}

/-- **Step 5**, one neighbour. Seen from the corner `eₖ` and measured from the direction `ωₖ` of
side `k`, a neighbour lies at distance `2` in a direction between `0°` and `120°`: it lies on
the left of side `k` and on the left of side `k - 1`. -/
private theorem step5_arg (hω : ‖ω‖ = 1)
    (hside : ∀ k : Fin 6, A.center (e (k + 1)) = A.center (e k) + L k * (ω * rho ^ (k : ℕ)))
    (hsupp : ∀ (k : Fin 6) (i : ι), 0 ≤ cross (ω * rho ^ (k : ℕ)) (A.center i - A.center (e k)))
    {k : Fin 6} {y : ι} (hy : A.contactGraph.Adj (e k) y) :
    ‖(A.center y - A.center (e k)) * starRingEnd ℂ (ω * rho ^ (k : ℕ))‖ = 2 ∧
      0 ≤ arg ((A.center y - A.center (e k)) * starRingEnd ℂ (ω * rho ^ (k : ℕ))) ∧
      arg ((A.center y - A.center (e k)) * starRingEnd ℂ (ω * rho ^ (k : ℕ))) ≤
        2 * (Real.pi / 3) := by
  set W' := ω * rho ^ ((k - 1 : Fin 6) : ℕ)
  have hW : ω * rho ^ (k : ℕ) = W' * rho := by rw [rho_pow_val_sub_one k]; ring
  set z := (A.center y - A.center (e k)) * starRingEnd ℂ (ω * rho ^ (k : ℕ)) with hz
  have hn : ‖z‖ = 2 := by
    rw [hz, norm_mul, Complex.norm_conj, norm_mul_rho_pow hω, mul_one, ← dist_eq_norm, dist_comm]
    exact hy.2
  have him : 0 ≤ z.im := by
    rw [hz, mul_comm, ← cross_eq_im]
    exact hsupp k y
  have hrho : 0 ≤ (rho * z).im := by
    have e1 : rho * z = starRingEnd ℂ W' * (A.center y - A.center (e k)) := by
      have hr : rho * starRingEnd ℂ rho = 1 := by
        rw [Complex.mul_conj, normSq_rho, Complex.ofReal_one]
      rw [hz, hW, map_mul]
      linear_combination (starRingEnd ℂ W' * (A.center y - A.center (e k))) * hr
    rw [e1, ← cross_eq_im]
    have h := hside (k - 1)
    rw [sub_add_cancel] at h
    rw [← cross_sub_eq_of_eq_add h]
    exact hsupp (k - 1) y
  refine ⟨hn, Complex.arg_nonneg_iff.mpr him, le_two_mul_pi_div_three (Complex.arg_le_pi z) ?_⟩
  rw [im_rho_mul, hn] at hrho
  linarith

/-- **Step 5.** If the six corners `eₖ` touch exactly three circles each and form a hexagon with
sides `eₖ₊₁ - eₖ = Lₖ ω ρᵏ` and all centers on the left of each side, then the neighbours of
`eₖ` are centered exactly at the three points `eₖ + 2 ω ρᵏ⁺ʲ`, `j = 0, 1, 2`. -/
private theorem step5 (hω : ‖ω‖ = 1)
    (hside : ∀ k : Fin 6, A.center (e (k + 1)) = A.center (e k) + L k * (ω * rho ^ (k : ℕ)))
    (hsupp : ∀ (k : Fin 6) (i : ι), 0 ≤ cross (ω * rho ^ (k : ℕ)) (A.center i - A.center (e k)))
    (h3 : ∀ k, A.TouchesExactlyThree (e k)) (k : Fin 6) :
    (∀ i, A.contactGraph.Adj (e k) i ↔
      ∃ j : Fin 3, A.center i = A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + (j : ℕ)))) ∧
    ∀ j : Fin 3, ∃ i, A.center i = A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + (j : ℕ))) := by
  obtain ⟨y₁, y₂, y₃, h12, h13, h23, hy⟩ := h3 k
  have a₁ := (hy y₁).mpr (Or.inl rfl)
  have a₂ := (hy y₂).mpr (Or.inr (Or.inl rfl))
  have a₃ := (hy y₃).mpr (Or.inr (Or.inr rfl))
  set W := ω * rho ^ (k : ℕ) with hWdef
  set z : ι → ℂ := fun y => (A.center y - A.center (e k)) * starRingEnd ℂ W with hz
  have arg_mem := fun {y : ι} (hy : A.contactGraph.Adj (e k) y) =>
    step5_arg (L := L) hω hside hsupp hy
  -- the three directions are pairwise at least `60°` apart
  have sep : ∀ {y y' : ι}, A.contactGraph.Adj (e k) y → A.contactGraph.Adj (e k) y' → y ≠ y' →
      Real.pi / 3 ≤ |arg (z y) - arg (z y')| := fun {y y'} hy hy' hne =>
    pi_div_three_le_abs_arg_sub (arg_mem hy).1 (arg_mem hy').1 (by
      rw [show z y - z y' = (A.center y - A.center y') * starRingEnd ℂ W by simp only [hz]; ring,
        norm_mul, Complex.norm_conj, norm_mul_rho_pow hω, mul_one, ← dist_eq_norm]
      exact A.nonoverlap hne)
  -- a neighbour in direction `j · 60°` is centered at `eₖ + 2 ω ρᵏ⁺ʲ`
  have pos : ∀ {y : ι}, A.contactGraph.Adj (e k) y → ∀ j : Fin 3,
      arg (z y) = (j : ℕ) * Real.pi / 3 →
      A.center y = A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + (j : ℕ))) := by
    intro y hy j hj
    have h1 : z y = 2 * rho ^ (j : ℕ) := by
      rw [← Complex.norm_mul_exp_arg_mul_I (z y), (arg_mem hy).1, hj,
        exp_nat_mul_pi_div_three_mul_I]
      push_cast
      ring
    have hWW : starRingEnd ℂ W * W = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hWdef, norm_mul_rho_pow hω]
      norm_num
    have h2 : A.center y - A.center (e k) = z y * W := by
      simp only [hz]
      linear_combination (-(A.center y - A.center (e k))) * hWW
    rw [h1, hWdef] at h2
    rw [pow_add]
    linear_combination h2
  -- the three directions, sorted, are `0°`, `60°` and `120°`
  obtain ⟨-, l₁, u₁⟩ := arg_mem a₁
  obtain ⟨-, l₂, u₂⟩ := arg_mem a₂
  obtain ⟨-, l₃, u₃⟩ := arg_mem a₃
  have s12 := sep a₁ a₂ h12
  have s13 := sep a₁ a₃ h13
  have s23 := sep a₂ a₃ h23
  have s21 : Real.pi / 3 ≤ |arg (z y₂) - arg (z y₁)| := by rwa [abs_sub_comm]
  have s31 : Real.pi / 3 ≤ |arg (z y₃) - arg (z y₁)| := by rwa [abs_sub_comm]
  have s32 : Real.pi / 3 ≤ |arg (z y₃) - arg (z y₂)| := by rwa [abs_sub_comm]
  have vals : ∀ {y : ι}, A.contactGraph.Adj (e k) y → ∃ j : Fin 3,
      arg (z y) = (j : ℕ) * Real.pi / 3 := by
    intro y hy'
    rcases (hy y).mp hy' with rfl | rfl | rfl
    · exact exists_eq_of_three_sep l₁ u₁ l₂ u₂ l₃ u₃ s12 s13 s23
    · exact exists_eq_of_three_sep l₂ u₂ l₁ u₁ l₃ u₃ s21 s23 s13
    · exact exists_eq_of_three_sep l₃ u₃ l₁ u₁ l₂ u₂ s31 s32 s12
  have hit : ∀ j : Fin 3, ∃ y, A.contactGraph.Adj (e k) y ∧ arg (z y) = (j : ℕ) * Real.pi / 3 := by
    intro j
    rcases hit_of_three_sep l₁ u₁ l₂ u₂ l₃ u₃ s12 s13 s23 j with h | h | h
    · exact ⟨y₁, a₁, h⟩
    · exact ⟨y₂, a₂, h⟩
    · exact ⟨y₃, a₃, h⟩
  refine ⟨fun i => ⟨fun hi => ?_, fun ⟨j, hj⟩ => ?_⟩, fun j => ?_⟩
  · obtain ⟨j, hj⟩ := vals hi
    exact ⟨j, pos hi j hj⟩
  · obtain ⟨y, hy', hyj⟩ := hit j
    rw [← pos hy' j hyj] at hj
    rwa [A.center_injective hj]
  · obtain ⟨y, hy', hyj⟩ := hit j
    exact ⟨y, pos hy' j hyj⟩

end Step5

/-! ### Lemma S, Steps 1–4: following the extreme circle -/

section Steps

variable {e : Fin 6 → ι}

/-- The hypotheses of setting S6: every circle touches two others, no circle is removable, and
`e₀, …, e₅` are six different circles, `eₖ` extreme in direction `k · 60°`, which are all the
corners. -/
private structure Setting (A : Arrangement ι) (e : Fin 6 → ι) : Prop where
  touchesTwo : A.TouchesTwo
  isCore : A.IsCore
  injective : Function.Injective e
  isExtreme : ∀ k : Fin 6, A.IsExtreme ((k : ℕ) * Real.pi / 3) (e k)
  mem_range : ∀ i, A.IsCorner i → i ∈ Set.range e

/-- `eₖ₊₁` is extreme in direction `(k + 1) · 60°`. For `k = 5` this is `e₀` and `360°`
(fact X2). -/
private theorem Setting.isExtreme_succ (hS : Setting A e) (k : Fin 6) :
    A.IsExtreme (((k : ℕ) + 1) * Real.pi / 3) (e (k + 1)) := by
  by_cases hk : (k : ℕ) < 5
  · have h1 : ((k + 1 : Fin 6) : ℕ) = (k : ℕ) + 1 := by rw [Fin.val_add, Fin.val_one]; omega
    have := hS.isExtreme (k + 1)
    rw [h1] at this
    exact_mod_cast this
  · obtain rfl : k = 5 := Fin.ext (show (k : ℕ) = 5 by omega)
    have := (A.isExtreme_add_two_pi).mpr (hS.isExtreme 0)
    convert this using 2
    · norm_num
      ring
    · rfl

/-- The sides of the hexagon have length at least `2`. -/
private theorem Setting.two_le_norm (hS : Setting A e) (k : Fin 6) :
    2 ≤ ‖A.center (e (k + 1)) - A.center (e k)‖ := by
  rw [← dist_eq_norm]
  exact A.nonoverlap (hS.injective.ne (fin_add_ne one_ne_zero))

/-- **Step 1.** On the arc `[k · 60°, (k + 1) · 60°]`, only `eₖ` and `eₖ₊₁` can be extreme
among the corners: a corner is extreme only in directions less than `60°` apart modulo
`360°`. -/
private theorem Setting.eq_or_eq_succ (hS : Setting A e) {k j : Fin 6} {θ : ℝ}
    (h1 : (k : ℕ) * Real.pi / 3 ≤ θ) (h2 : θ ≤ ((k : ℕ) + 1) * Real.pi / 3)
    (hj : A.IsExtreme θ (e j)) : j = k ∨ j = k + 1 := by
  obtain ⟨n, hn⟩ := hj.exists_int_abs_lt hS.touchesTwo hS.isCore (hS.isExtreme j)
  have hπ := Real.pi_pos
  rw [abs_lt] at hn
  have i1 : ((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 6 * n < 1 := by
    have : ((((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 6 * n : ℤ) : ℝ) < 1 := by
      push_cast
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  have i2 : -2 < ((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 6 * n := by
    have : (-2 : ℝ) < ((((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 6 * n : ℤ) : ℝ) := by
      push_cast
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  have hk := k.isLt
  have hj6 := j.isLt
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_add, Fin.val_one]
  omega

variable (A e) in
/-- The *switching angle* `τₖ` of side `k`: the direction in which the extreme circle switches
from `eₖ` to `eₖ₊₁`. It is perpendicular to the side `eₖ₊₁ - eₖ`, which has direction
`τₖ + 90°`. -/
private noncomputable def switchAngle (k : Fin 6) : ℝ :=
  (k : ℕ) * Real.pi / 3 + Real.pi / 2 +
    arg ((A.center (e k) - A.center (e (k + 1))) * exp (↑(-((k : ℕ) * Real.pi / 3)) * I))

/-- **Step 2.** The side `eₖ₊₁ - eₖ` has direction `τₖ + 90°`. -/
private theorem sub_eq_switchAngle (k : Fin 6) :
    A.center (e (k + 1)) - A.center (e k) =
      ↑‖A.center (e (k + 1)) - A.center (e k)‖ * exp (↑(switchAngle A e k + Real.pi / 2) * I) := by
  set v := (A.center (e k) - A.center (e (k + 1))) * exp (↑(-((k : ℕ) * Real.pi / 3)) * I)
    with hv
  have hn : ‖v‖ = ‖A.center (e (k + 1)) - A.center (e k)‖ := by
    rw [hv, norm_mul_exp_neg, norm_sub_rev]
  have e1 : exp (↑(switchAngle A e k + Real.pi / 2) * I) =
      exp (↑(arg v) * I) * exp (↑((k : ℕ) * Real.pi / 3) * I) * exp (↑Real.pi * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [switchAngle, ← hv]
    push_cast
    ring
  rw [e1, Complex.exp_pi_mul_I, ← hn, ← mul_assoc, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I,
    hv, mul_assoc (A.center (e k) - A.center (e (k + 1))), ← Complex.exp_add,
    show (↑(-((k : ℕ) * Real.pi / 3)) * I + ↑((k : ℕ) * Real.pi / 3) * I : ℂ) = 0 by
      push_cast; ring, Complex.exp_zero]
  ring

/-- **Step 2.** The switching angle `τₖ` lies in `(k · 60°, (k + 1) · 60°]`: `eₖ` is extreme in
direction `k · 60°` and `eₖ₊₁` in direction `(k + 1) · 60°`. -/
private theorem Setting.switchAngle_mem (hS : Setting A e) (k : Fin 6) :
    (k : ℕ) * Real.pi / 3 < switchAngle A e k ∧
      switchAngle A e k ≤ ((k : ℕ) + 1) * Real.pi / 3 := by
  have hne : e (k + 1) ≠ e k := hS.injective.ne (fin_add_ne one_ne_zero)
  obtain ⟨a1, a2⟩ := (hS.isExtreme k (e (k + 1)) hne).arg_mem
  have hnext := hS.isExtreme_succ k (e k) hne.symm
  have hπ := Real.pi_pos
  have hL : 0 < ‖A.center (e (k + 1)) - A.center (e k)‖ := by
    linarith [hS.two_le_norm k]
  rw [sub_eq_switchAngle, lexPos_mul_exp_mul_exp_iff hL] at hnext
  · simp only [switchAngle] at hnext ⊢
    constructor <;> linarith
  all_goals simp only [switchAngle]; linarith

/-- **Step 2.** On the arc `[k · 60°, (k + 1) · 60°]`, the side `eₖ₊₁ - eₖ`, rotated by `-θ`, is
lexicographically positive exactly from the switching angle `τₖ` on. -/
private theorem Setting.lexPos_iff (hS : Setting A e) (k : Fin 6) {θ : ℝ}
    (h1 : (k : ℕ) * Real.pi / 3 ≤ θ) (h2 : θ ≤ ((k : ℕ) + 1) * Real.pi / 3) :
    LexPos ((A.center (e (k + 1)) - A.center (e k)) * exp (↑(-θ) * I)) ↔
      switchAngle A e k ≤ θ := by
  have hL : 0 < ‖A.center (e (k + 1)) - A.center (e k)‖ := by
    linarith [hS.two_le_norm k]
  have hm := hS.switchAngle_mem k
  have hπ := Real.pi_pos
  rw [sub_eq_switchAngle, lexPos_mul_exp_mul_exp_iff hL (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-- **Step 2.** Before the switching angle, `eₖ` is extreme. -/
private theorem Setting.isExtreme_of_lt [Finite ι] (hS : Setting A e) (k : Fin 6) {θ : ℝ}
    (h1 : (k : ℕ) * Real.pi / 3 ≤ θ) (h2 : θ < switchAngle A e k) : A.IsExtreme θ (e k) := by
  have : Nonempty ι := ⟨e 0⟩
  have h2' : θ ≤ ((k : ℕ) + 1) * Real.pi / 3 := h2.le.trans (hS.switchAngle_mem k).2
  obtain ⟨i, hi⟩ := A.exists_isExtreme θ
  obtain ⟨j, rfl⟩ := hS.mem_range i hi.isCorner
  rcases hS.eq_or_eq_succ h1 h2' hi with rfl | rfl
  · exact hi
  · have hne : e k ≠ e (k + 1) := hS.injective.ne (fin_add_ne one_ne_zero).symm
    exact absurd ((hS.lexPos_iff k h1 h2').mp (hi (e k) hne)) (not_le.mpr h2)

/-- **Step 2.** From the switching angle on, `eₖ₊₁` is extreme. -/
private theorem Setting.isExtreme_succ_of_le [Finite ι] (hS : Setting A e) (k : Fin 6) {θ : ℝ}
    (h1 : switchAngle A e k ≤ θ) (h2 : θ ≤ ((k : ℕ) + 1) * Real.pi / 3) :
    A.IsExtreme θ (e (k + 1)) := by
  have : Nonempty ι := ⟨e 0⟩
  have h1' : (k : ℕ) * Real.pi / 3 ≤ θ := (hS.switchAngle_mem k).1.le.trans h1
  obtain ⟨i, hi⟩ := A.exists_isExtreme θ
  obtain ⟨j, rfl⟩ := hS.mem_range i hi.isCorner
  rcases hS.eq_or_eq_succ h1' h2 hi with rfl | rfl
  · have hne : e (j + 1) ≠ e j := hS.injective.ne (fin_add_ne one_ne_zero)
    have hpos := (hS.lexPos_iff j h1' h2).mpr h1
    refine absurd (hi (e (j + 1)) hne) ?_
    rw [show (A.center (e j) - A.center (e (j + 1))) * exp (↑(-θ) * I) =
      -((A.center (e (j + 1)) - A.center (e j)) * exp (↑(-θ) * I)) by ring]
    exact hpos.not_neg
  · exact hi

/-- **Step 3.** Consecutive switching angles are at most `60°` apart: `eₖ₊₁` is extreme from
`τₖ` to `τₖ₊₁`, and a corner is not extreme in two directions `60°` apart. -/
private theorem Setting.switchAngle_succ_le [Finite ι] (hS : Setting A e) (k : Fin 6)
    (hk : (k : ℕ) < 5) : switchAngle A e (k + 1) ≤ switchAngle A e k + Real.pi / 3 := by
  by_contra hlt
  push Not at hlt
  have hπ := Real.pi_pos
  have h1 : ((k + 1 : Fin 6) : ℕ) = (k : ℕ) + 1 := by rw [Fin.val_add, Fin.val_one]; omega
  have hm := hS.switchAngle_mem k
  have hext := hS.isExtreme_succ_of_le k le_rfl hm.2
  refine hext.not_isExtreme_add hS.touchesTwo hS.isCore le_rfl (by linarith) ?_
  refine hS.isExtreme_of_lt (k + 1) ?_ hlt
  rw [h1]
  push_cast
  linarith

/-- **Step 3**, wrapping around: `τ₀ + 360° ≤ τ₅ + 60°`. Here `e₀` is extreme from `τ₅` to
`τ₀ + 360°`. -/
private theorem Setting.switchAngle_zero_le [Finite ι] (hS : Setting A e) :
    switchAngle A e 0 + 2 * Real.pi ≤ switchAngle A e 5 + Real.pi / 3 := by
  by_contra hlt
  push Not at hlt
  have hπ := Real.pi_pos
  have hm := hS.switchAngle_mem 5
  have hext : A.IsExtreme (switchAngle A e 5) (e 0) := hS.isExtreme_succ_of_le 5 le_rfl hm.2
  refine hext.not_isExtreme_add hS.touchesTwo hS.isCore le_rfl (by linarith) ?_
  have h0 : A.IsExtreme (switchAngle A e 5 + Real.pi / 3 - 2 * Real.pi) (e 0) := by
    refine hS.isExtreme_of_lt 0 ?_ (by linarith)
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_div]
    norm_num at hm
    linarith
  rw [← A.isExtreme_add_two_pi] at h0
  rwa [sub_add_cancel] at h0

/-- **Step 3.** The switching angles are exactly `60°` apart: six steps of at most `60°` that
turn once around the circle. -/
private theorem Setting.switchAngle_eq [Finite ι] (hS : Setting A e) (k : Fin 6) :
    switchAngle A e k = switchAngle A e 0 + (k : ℕ) * Real.pi / 3 := by
  have h0 : switchAngle A e 1 ≤ switchAngle A e 0 + Real.pi / 3 :=
    hS.switchAngle_succ_le 0 (by decide)
  have h1 : switchAngle A e 2 ≤ switchAngle A e 1 + Real.pi / 3 :=
    hS.switchAngle_succ_le 1 (by decide)
  have h2 : switchAngle A e 3 ≤ switchAngle A e 2 + Real.pi / 3 :=
    hS.switchAngle_succ_le 2 (by decide)
  have h3 : switchAngle A e 4 ≤ switchAngle A e 3 + Real.pi / 3 :=
    hS.switchAngle_succ_le 3 (by decide)
  have h4 : switchAngle A e 5 ≤ switchAngle A e 4 + Real.pi / 3 :=
    hS.switchAngle_succ_le 4 (by decide)
  have h5 := hS.switchAngle_zero_le
  fin_cases k <;> simp <;> linarith

/-- The unit vector of direction `τₖ + 90°` is `ω ρᵏ`, where `ω` has direction `τ₀ + 90°`. -/
private theorem Setting.exp_switchAngle [Finite ι] (hS : Setting A e) (k : Fin 6) :
    exp (↑(switchAngle A e k + Real.pi / 2) * I) =
      exp (↑(switchAngle A e 0 + Real.pi / 2) * I) * rho ^ (k : ℕ) := by
  rw [← exp_nat_mul_pi_div_three_mul_I, ← Complex.exp_add, hS.switchAngle_eq k]
  congr 1
  push_cast
  ring

/-- **Step 4.** Every center lies on the left of side `k`: `eₖ₊₁` is extreme in direction `τₖ`,
perpendicular to the side. -/
private theorem Setting.support [Finite ι] (hS : Setting A e) (k : Fin 6) (i : ι) :
    0 ≤ cross (exp (↑(switchAngle A e k + Real.pi / 2) * I)) (A.center i - A.center (e k)) := by
  have hm := hS.switchAngle_mem k
  rw [cross_sub_eq_of_eq_add (p₁ := A.center (e (k + 1))) (L := ‖A.center (e (k + 1)) -
    A.center (e k)‖) (by rw [← sub_eq_switchAngle]; ring)]
  by_cases hi : i = e (k + 1)
  · rw [hi, sub_self, cross_zero_right]
  · have h := hS.isExtreme_succ_of_le k le_rfl hm.2 i hi
    rw [cross_exp_add_pi_div_two, neg_sub]
    rcases h with h | ⟨h, -⟩ <;> linarith

end Steps

/-! ### Lemma S -/

/-- **Lemma S.** Let `A` be a finite arrangement in which every circle touches at least two
others and no circle is removable, and let `e₀, …, e₅` be six different circles, `eₖ` extreme in
direction `k · 60°`, which are all the corners (setting S6). Then the corners form an
equiangular hexagon: there are a unit vector `ω` and side lengths `Lₖ ≥ 2` with
`eₖ₊₁ = eₖ + Lₖ ω ρᵏ`, all centers lie on the left of each side, and the neighbours of `eₖ` are
centered exactly at `eₖ + 2 ω ρᵏ`, `eₖ + 2 ω ρᵏ⁺¹` and `eₖ + 2 ω ρᵏ⁺²`. -/
theorem exists_isSixCornerFrame [Finite ι] (hT : A.TouchesTwo) (hc : A.IsCore) {e : Fin 6 → ι}
    (he : Function.Injective e) (hext : ∀ k : Fin 6, A.IsExtreme ((k : ℕ) * Real.pi / 3) (e k))
    (hcorner : ∀ i, A.IsCorner i → i ∈ Set.range e) :
    ∃ ω L, A.IsSixCornerFrame e ω L := by
  have hS : Setting A e := ⟨hT, hc, he, hext, hcorner⟩
  set ω := exp (↑(switchAngle A e 0 + Real.pi / 2) * I)
  set L : Fin 6 → ℝ := fun k => ‖A.center (e (k + 1)) - A.center (e k)‖
  have hω : ‖ω‖ = 1 := norm_exp_ofReal_mul_I _
  have hside : ∀ k : Fin 6, A.center (e (k + 1)) = A.center (e k) + L k * (ω * rho ^ (k : ℕ)) :=
    fun k => by
      rw [← hS.exp_switchAngle k]
      linear_combination sub_eq_switchAngle (A := A) (e := e) k
  have hsupp : ∀ (k : Fin 6) (i : ι),
      0 ≤ cross (ω * rho ^ (k : ℕ)) (A.center i - A.center (e k)) := fun k i => by
    rw [← hS.exp_switchAngle k]
    exact hS.support k i
  have h3 : ∀ k, A.TouchesExactlyThree (e k) := fun k => (hext k).touchesExactlyThree hT hc
  exact ⟨ω, L, he, fun i => ⟨hcorner i, fun ⟨k, hk⟩ => hk ▸ (hext k).isCorner⟩, hω,
    hS.two_le_norm, hside, hsupp, fun k => (step5 hω hside hsupp h3 k).1,
    fun k => (step5 hω hside hsupp h3 k).2⟩

/-! ### Proposition H -/

namespace IsSixCornerFrame

variable {e : Fin 6 → ι} {ω : ℂ} {L : Fin 6 → ℝ}

/-- The direction `ω ρᵏ` of side `k` is not zero. -/
theorem ne_zero (hF : A.IsSixCornerFrame e ω L) (k : Fin 6) : ω * rho ^ (k : ℕ) ≠ 0 := by
  intro h
  have := norm_mul_rho_pow hF.norm_eq_one (k : ℕ)
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- Each `eₖ` is a corner. -/
theorem isCorner (hF : A.IsSixCornerFrame e ω L) (k : Fin 6) : A.IsCorner (e k) :=
  (hF.isCorner_iff _).mpr ⟨k, rfl⟩

/-- **(H1) Closure.** The hexagon closes up: `∑ Lₖ ρᵏ = 0`, and since `ρ` is not real,
`L₀ - L₃ = L₂ - L₅ = L₄ - L₁`. -/
theorem closure (hF : A.IsSixCornerFrame e ω L) :
    L 0 - L 3 = L 2 - L 5 ∧ L 2 - L 5 = L 4 - L 1 := by
  have h0 : A.center (e 1) = A.center (e 0) + L 0 * (ω * rho ^ 0) := hF.side 0
  have h1 : A.center (e 2) = A.center (e 1) + L 1 * (ω * rho ^ 1) := hF.side 1
  have h2 : A.center (e 3) = A.center (e 2) + L 2 * (ω * rho ^ 2) := hF.side 2
  have h3 : A.center (e 4) = A.center (e 3) + L 3 * (ω * rho ^ 3) := hF.side 3
  have h4 : A.center (e 5) = A.center (e 4) + L 4 * (ω * rho ^ 4) := hF.side 4
  have h5 : A.center (e 0) = A.center (e 5) + L 5 * (ω * rho ^ 5) := hF.side 5
  have hω : ω ≠ 0 := by simpa using hF.ne_zero 0
  have hsum : ω * (((L 0 - L 2 - L 3 + L 5 : ℝ) : ℂ) + ((L 1 + L 2 - L 4 - L 5 : ℝ) : ℂ) * rho) =
      0 := by
    push_cast
    linear_combination (-1 : ℂ) * (h0 + h1 + h2 + h3 + h4 + h5) -
      ω * (L 2 - L 5) * rho_sq - ω * (L 3 + L 4 * rho + L 5 * rho ^ 2) * rho_pow_three
  obtain ⟨ha, hb⟩ := ofReal_add_ofReal_mul_rho_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hω)
  constructor <;> linarith

/-- **(H3) Open sides are disjoint.** A point inside two sides of the hexagon is inside one
side: the line of side `k` supports all centers, so a side meeting it inside lies on it, and no
three corners are collinear. -/
theorem eq_of_mem_openSegment (hF : A.IsSixCornerFrame e ω L) {k m : Fin 6} {q : ℂ}
    (hk : q ∈ openSegment ℝ (A.center (e k)) (A.center (e (k + 1))))
    (hm : q ∈ openSegment ℝ (A.center (e m)) (A.center (e (m + 1)))) : k = m := by
  by_contra hkm
  set w := ω * rho ^ (k : ℕ)
  have hw0 : w ≠ 0 := hF.ne_zero k
  have hside := hF.side k
  -- the line of side `k` passes through `q`
  have hq : cross w (q - A.center (e k)) = 0 := by
    obtain ⟨a, b, -, -, hab, rfl⟩ := hk
    rw [cross_add_smul_sub _ _ _ _ hab, sub_self, cross_zero_right, hside, add_sub_cancel_left,
      cross_ofReal_mul_right, cross_self]
    ring
  -- so it passes through both ends of side `m`
  have hm' : cross w (A.center (e m) - A.center (e k)) = 0 ∧
      cross w (A.center (e (m + 1)) - A.center (e k)) = 0 := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hm
    rw [cross_add_smul_sub _ _ _ _ hab] at hq
    have h1 := hF.support k (e m)
    have h2 := hF.support k (e (m + 1))
    exact ⟨le_antisymm (by nlinarith) h1, le_antisymm (by nlinarith) h2⟩
  have hk0 : cross w (A.center (e k) - A.center (e k)) = 0 := by
    rw [sub_self, cross_zero_right]
  have hk1 : cross w (A.center (e (k + 1)) - A.center (e k)) = 0 := by
    rw [hside, add_sub_cancel_left, cross_ofReal_mul_right, cross_self, mul_zero]
  -- three different corners among `eₖ, eₖ₊₁, eₘ, eₘ₊₁` would be collinear
  have col : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      cross w (A.center (e a) - A.center (e k)) = 0 →
      cross w (A.center (e b) - A.center (e k)) = 0 →
      cross w (A.center (e c) - A.center (e k)) = 0 → False :=
    fun a b c hab hac hbc ha hb hc =>
      (hF.isCorner a).cross_ne_zero (hF.isCorner b) (hF.isCorner c) (hF.injective.ne hab)
        (hF.injective.ne hac) (hF.injective.ne hbc) (cross_eq_zero_of_cross_eq_zero hw0 ha hb hc)
  by_cases h1 : m = k + 1
  · subst h1
    refine col k (k + 1) (k + 1 + 1) (fin_add_ne one_ne_zero).symm ?_
      (fin_add_ne one_ne_zero).symm hk0 hk1 hm'.2
    rw [add_assoc]
    exact (fin_add_ne (by decide)).symm
  · exact col k (k + 1) m (fin_add_ne one_ne_zero).symm hkm (Ne.symm h1) hk0 hk1 hm'.1

/-- **(H2)** On a side longer than `2`, the neighbour `eₖ + 2ωₖ` of `eₖ` (S-c) lies inside the
side, so it is not a corner (4a). -/
theorem exists_mid (hF : A.IsSixCornerFrame e ω L) {k : Fin 6} (hk : 2 < L k) :
    ∃ a, ¬ A.IsCorner a ∧ A.center a = A.center (e k) + 2 * (ω * rho ^ (k : ℕ)) ∧
      A.center a ∈ openSegment ℝ (A.center (e k)) (A.center (e (k + 1))) := by
  obtain ⟨a, ha⟩ := hF.exists_nbr k 0
  rw [Fin.val_zero, add_zero] at ha
  have hL : (L k : ℂ) ≠ 0 := by exact_mod_cast (by linarith : L k ≠ 0)
  have hmem : A.center a ∈ openSegment ℝ (A.center (e k)) (A.center (e (k + 1))) := by
    refine ⟨1 - 2 / L k, 2 / L k, ?_, by have := hF.two_le k; positivity, by ring, ?_⟩
    · rw [sub_pos, div_lt_one (by linarith)]
      exact hk
    · rw [ha, hF.side k, Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
      ring
  have hne : e k ≠ a := by
    rintro rfl
    exact hF.ne_zero k (by linear_combination -ha / 2)
  exact ⟨a, fun hc => hc.not_mem_openSegment hne hmem, ha, hmem⟩

/-- **(H2)** On a side longer than `2`, the neighbour `eₖ₊₁ - 2ωₖ` of `eₖ₊₁` (S-c) lies inside the
side, so it is not a corner (4a). -/
theorem exists_mid' (hF : A.IsSixCornerFrame e ω L) {k : Fin 6} (hk : 2 < L k) :
    ∃ a, ¬ A.IsCorner a ∧ A.center a = A.center (e (k + 1)) - 2 * (ω * rho ^ (k : ℕ)) ∧
      A.center a ∈ openSegment ℝ (A.center (e k)) (A.center (e (k + 1))) := by
  obtain ⟨a, ha⟩ := hF.exists_nbr (k + 1) 2
  rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_add, rho_pow_val_add_one] at ha
  have ha' : A.center a = A.center (e (k + 1)) - 2 * (ω * rho ^ (k : ℕ)) := by
    rw [ha]
    linear_combination 2 * ω * rho ^ (k : ℕ) * rho_pow_three
  have hL : (L k : ℂ) ≠ 0 := by exact_mod_cast (by linarith : L k ≠ 0)
  have hmem : A.center a ∈ openSegment ℝ (A.center (e k)) (A.center (e (k + 1))) := by
    refine ⟨2 / L k, 1 - 2 / L k, by have := hF.two_le k; positivity, ?_, by ring, ?_⟩
    · rw [sub_pos, div_lt_one (by linarith)]
      exact hk
    · rw [ha', hF.side k, Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
      ring
  have hne : e (k + 1) ≠ a := by
    rintro rfl
    exact hF.ne_zero k (by linear_combination ha' / 2)
  refine ⟨a, fun hc => hc.not_mem_openSegment (c' := e k) hne ?_, ha', hmem⟩
  rwa [openSegment_symm]

/-- The distance between the points `x + s ωₖ` and `x + t ωₖ` of a line of direction `ωₖ`
is `|s - t|`. -/
private theorem dist_add_mul (hF : A.IsSixCornerFrame e ω L) (k : Fin 6) (x : ℂ) (s t : ℝ) :
    dist (x + s * (ω * rho ^ (k : ℕ))) (x + t * (ω * rho ^ (k : ℕ))) = |s - t| := by
  rw [dist_eq_norm, show x + s * (ω * rho ^ (k : ℕ)) - (x + t * (ω * rho ^ (k : ℕ))) =
    ((s - t : ℝ) : ℂ) * (ω * rho ^ (k : ℕ)) by push_cast; ring, norm_mul,
    norm_mul_rho_pow hF.norm_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **(H2) Side lengths.** A side longer than `2` has length `4` or at least `6`. The circle at
`eₖ + 2ωₖ` does not overlap `eₖ₊₁`, so the side has length at least `4`; if the circles at
`eₖ + 2ωₖ` and `eₖ₊₁ - 2ωₖ` are different, they are at least `2` apart, so the length is not
in `(2, 6)`. -/
theorem eq_four_or_six_le (hF : A.IsSixCornerFrame e ω L) {k : Fin 6} (hk : 2 < L k) :
    L k = 4 ∨ 6 ≤ L k := by
  obtain ⟨a, ha, hpa, -⟩ := hF.exists_mid hk
  obtain ⟨b, -, hpb, -⟩ := hF.exists_mid' hk
  have h4 : 4 ≤ L k := by
    have : 2 ≤ dist (A.center a) (A.center (e (k + 1))) :=
      A.nonoverlap (show a ≠ e (k + 1) from fun h => ha (h ▸ hF.isCorner _))
    rw [hpa, hF.side k, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, dist_add_mul hF,
      abs_of_neg (by linarith)] at this
    linarith
  by_cases h : L k = 4
  · exact Or.inl h
  · right
    have hab : a ≠ b := by
      rintro rfl
      rw [hpa, hF.side k] at hpb
      have : ((4 - L k : ℝ) : ℂ) * (ω * rho ^ (k : ℕ)) = 0 := by
        push_cast
        linear_combination hpb
      rcases mul_eq_zero.mp this with h' | h'
      · exact h (by linarith [Complex.ofReal_eq_zero.mp h'])
      · exact hF.ne_zero k h'
    have : 2 ≤ dist (A.center a) (A.center b) := A.nonoverlap hab
    rw [hpa, hpb, hF.side k, show A.center (e k) + ↑(L k) * (ω * rho ^ (k : ℕ)) -
      2 * (ω * rho ^ (k : ℕ)) = A.center (e k) + ((L k - 2 : ℝ) : ℂ) * (ω * rho ^ (k : ℕ)) by
        push_cast; ring, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, dist_add_mul hF] at this
    rcases le_abs.mp this with h' | h' <;> linarith

/-- **(H4) Every side has length `2`**, provided at most two circles are not corners. Otherwise
three different non-corners appear (by (H2) and (H3)):
* if `L₀ ≠ L₃`, then by (H1) each pair of opposite sides has a side longer than `2`, which
  carries a non-corner;
* if `L₀ = L₃`, then (H1) makes opposite sides equal, and a long side `k` gives non-corners on
  sides `k` and `k + 3`. A third one is the circle at `eₖ₊₁ - 2ωₖ` if `Lₖ ≠ 4`, a non-corner on
  side `k + 1` or `k + 2` if that is long, and otherwise (the hexagon `4, 2, 2, 4, 2, 2`) the
  neighbour `eₖ + 2ρωₖ` of `eₖ`, the midpoint between `eₖ` and the non-corner on side `k + 3`. -/
theorem sides_eq_two (hF : A.IsSixCornerFrame e ω L)
    (hfew : ∀ a b c : ι, ¬ A.IsCorner a → ¬ A.IsCorner b → ¬ A.IsCorner c →
      a = b ∨ a = c ∨ b = c) :
    ∀ k, L k = 2 := by
  have three : ∀ a b c : ι, ¬ A.IsCorner a → ¬ A.IsCorner b → ¬ A.IsCorner c → a ≠ b → a ≠ c →
      b ≠ c → False := fun a b c ha hb hc hab hac hbc => by
    rcases hfew a b c ha hb hc with h | h | h <;> contradiction
  -- circles inside different sides are different
  have mid_ne : ∀ {k m : Fin 6} {a b : ι},
      A.center a ∈ openSegment ℝ (A.center (e k)) (A.center (e (k + 1))) →
      A.center b ∈ openSegment ℝ (A.center (e m)) (A.center (e (m + 1))) → k ≠ m → a ≠ b := by
    rintro k m a b ha hb hkm rfl
    exact hkm (hF.eq_of_mem_openSegment ha hb)
  -- three long sides give three non-corners
  have three_long : ∀ k₁ k₂ k₃ : Fin 6, k₁ ≠ k₂ → k₁ ≠ k₃ → k₂ ≠ k₃ → 2 < L k₁ → 2 < L k₂ →
      2 < L k₃ → False := by
    intro k₁ k₂ k₃ h12 h13 h23 l₁ l₂ l₃
    obtain ⟨a₁, n₁, -, s₁⟩ := hF.exists_mid l₁
    obtain ⟨a₂, n₂, -, s₂⟩ := hF.exists_mid l₂
    obtain ⟨a₃, n₃, -, s₃⟩ := hF.exists_mid l₃
    exact three a₁ a₂ a₃ n₁ n₂ n₃ (mid_ne s₁ s₂ h12) (mid_ne s₁ s₃ h13) (mid_ne s₂ s₃ h23)
  have long : ∀ i j : Fin 6, L i ≠ L j → 2 < L i ∨ 2 < L j := by
    intro i j h
    rcases (hF.two_le i).lt_or_eq with hi | hi
    · exact Or.inl hi
    · exact Or.inr (lt_of_le_of_ne (hF.two_le j) fun hj => h (hi.symm.trans hj))
  by_contra hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  have hk2 : 2 < L k := lt_of_le_of_ne (hF.two_le k) (Ne.symm hk)
  obtain ⟨c1, c2⟩ := hF.closure
  by_cases hD : L 0 = L 3
  · -- opposite sides are equal
    have h3 : ∀ k : Fin 6, L (k + 3) = L k := by
      intro k
      fin_cases k <;> simp only [Fin.isValue, Fin.reduceAdd, Fin.reduceFinMk] <;> linarith
    have hk3 : 2 < L (k + 3) := (h3 k).symm ▸ hk2
    have hk03 : k ≠ k + 3 := (fin_add_ne (by decide)).symm
    obtain ⟨a, ha, hpa, hsa⟩ := hF.exists_mid hk2
    obtain ⟨b, hb, hpb, hsb⟩ := hF.exists_mid hk3
    have hab : a ≠ b := mid_ne hsa hsb hk03
    by_cases h4 : L k = 4
    · by_cases h1 : 2 < L (k + 1)
      · exact three_long k (k + 3) (k + 1) hk03 (fin_add_ne one_ne_zero).symm
          (by rw [add_right_injective k |>.ne_iff]; decide) hk2 hk3 h1
      by_cases h2 : 2 < L (k + 2)
      · exact three_long k (k + 3) (k + 2) hk03 (fin_add_ne (by decide)).symm
          (by rw [add_right_injective k |>.ne_iff]; decide) hk2 hk3 h2
      have h1' : L (k + 1) = 2 := le_antisymm (not_lt.mp h1) (hF.two_le _)
      have h2' : L (k + 2) = 2 := le_antisymm (not_lt.mp h2) (hF.two_le _)
      -- the hexagon `4, 2, 2, 4, 2, 2`, in units of `ωₖ` from `eₖ`
      have s0 := hF.side k
      have s1 := hF.side (k + 1)
      have s2 := hF.side (k + 2)
      rw [add_assoc, show (1 : Fin 6) + 1 = 2 from rfl, rho_pow_val_add_one, h1'] at s1
      rw [add_assoc, show (2 : Fin 6) + 1 = 3 from rfl, rho_pow_val_add, h2',
        show ((2 : Fin 6) : ℕ) = 2 from rfl] at s2
      rw [h4] at s0
      rw [rho_pow_val_add_three] at hpb
      have hpb' : A.center b = A.center (e k) + 4 * rho * (ω * rho ^ (k : ℕ)) := by
        rw [hpb, s2, s1, s0]
        push_cast
        linear_combination (2 * ω * rho ^ (k : ℕ)) * rho_sq
      -- the neighbour `x` of `eₖ` at `eₖ + 2ρωₖ` is the midpoint of `eₖ` and `b`
      obtain ⟨x, hx⟩ := hF.exists_nbr k 1
      have hx' : A.center x = A.center (e k) + 2 * rho * (ω * rho ^ (k : ℕ)) := by
        rw [hx, show ((1 : Fin 3) : ℕ) = 1 from rfl]
        ring
      have hxmid : A.center x ∈ openSegment ℝ (A.center (e k)) (A.center b) := by
        refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        rw [hx', hpb', Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      have hW0 : ω * rho ^ (k : ℕ) ≠ 0 := hF.ne_zero k
      have hρ0 : rho - 1 ≠ 0 := sub_ne_zero.mpr rho_ne_one
      have hxk : e k ≠ x := by
        rintro rfl
        exact mul_ne_zero rho_ne_zero hW0 (by linear_combination -hx' / 2)
      have hx_nc : ¬ A.IsCorner x := fun hc => hc.not_mem_openSegment hxk hxmid
      have hxa : a ≠ x := by
        rintro rfl
        exact mul_ne_zero hρ0 hW0 (by linear_combination (hpa - hx') / 2)
      have hxb : b ≠ x := by
        rintro rfl
        exact mul_ne_zero rho_ne_zero hW0 (by linear_combination (hx' - hpb') / 2)
      exact three a b x ha hb hx_nc hab hxa hxb
    · obtain ⟨a', ha', hpa', hsa'⟩ := hF.exists_mid' hk2
      have haa' : a ≠ a' := by
        rintro rfl
        rw [hpa, hF.side k] at hpa'
        have : ((4 - L k : ℝ) : ℂ) * (ω * rho ^ (k : ℕ)) = 0 := by
          push_cast
          linear_combination hpa'
        rcases mul_eq_zero.mp this with h' | h'
        · exact h4 (by linarith [Complex.ofReal_eq_zero.mp h'])
        · exact hF.ne_zero k h'
      exact three a b a' ha hb ha' hab haa' (mid_ne hsb hsa' (Ne.symm hk03))
  · -- each pair of opposite sides has a long side
    have h25 : L 2 ≠ L 5 := fun h => hD (by linarith)
    have h41 : L 4 ≠ L 1 := fun h => hD (by linarith)
    rcases long 0 3 hD with l₁ | l₁ <;> rcases long 2 5 h25 with l₂ | l₂ <;>
      rcases long 4 1 h41 with l₃ | l₃ <;>
      exact three_long _ _ _ (by decide) (by decide) (by decide) l₁ l₂ l₃

/-- All the points `bₖ = eₖ + 2 ω ρᵏ⁺¹` agree when the six sides have length `2`. -/
private theorem hub_eq (hF : A.IsSixCornerFrame e ω L) (hL : ∀ k, L k = 2) (k : Fin 6) :
    A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + 1)) = A.center (e 0) + 2 * (ω * rho ^ 1) := by
  have step : ∀ k : Fin 6, A.center (e (k + 1)) + 2 * (ω * rho ^ (((k + 1 : Fin 6) : ℕ) + 1)) =
      A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + 1)) := by
    intro k
    rw [hF.side k, hL k, pow_succ, pow_succ, rho_pow_val_add_one]
    push_cast
    linear_combination 2 * ω * rho ^ (k : ℕ) * one_sub_rho_add_rho_sq
  have s0 := step 0
  have s1 := step 1
  have s2 := step 2
  have s3 := step 3
  have s4 := step 4
  simp only [Fin.isValue, Fin.reduceAdd, Fin.val_zero, Fin.val_one, Fin.val_two, zero_add]
    at s0 s1 s2 s3 s4
  fin_cases k
  · rfl
  · exact s0
  · exact s1.trans s0
  · exact s2.trans (s1.trans s0)
  · exact s3.trans (s2.trans (s1.trans s0))
  · exact s4.trans (s3.trans (s2.trans (s1.trans s0)))

/-- **(H5) The hub.** If all six sides have length `2`, the points `eₖ + 2ρωₖ` coincide, at the
center of a circle `o` that is not a corner. It touches every corner, each corner touches only
`o` and its two neighbours on the hexagon, and `eₖ = o + 2 ζ ρᵏ` with `ζ = ω ρ⁴`. -/
theorem exists_hub (hF : A.IsSixCornerFrame e ω L) (hL : ∀ k, L k = 2) :
    ∃ o, ¬ A.IsCorner o ∧ (∀ k, A.contactGraph.Adj (e k) o) ∧
      (∀ k i, A.contactGraph.Adj (e k) i → i = e (k + 1) ∨ i = e (k - 1) ∨ i = o) ∧
      ∀ k : Fin 6, A.center (e k) = A.center o + 2 * (ω * rho ^ 4) * rho ^ (k : ℕ) := by
  obtain ⟨o, ho⟩ := hF.exists_nbr 0 1
  rw [show ((1 : Fin 3) : ℕ) = 1 from rfl, Fin.val_zero, zero_add] at ho
  have hpo : ∀ k : Fin 6, A.center o = A.center (e k) + 2 * (ω * rho ^ ((k : ℕ) + 1)) :=
    fun k => ho.trans (hF.hub_eq hL k).symm
  have hadj : ∀ k, A.contactGraph.Adj (e k) o := fun k => (hF.adj_iff k o).mpr ⟨1, hpo k⟩
  refine ⟨o, fun hc => ?_, hadj, fun k i hi => ?_, fun k => ?_⟩
  · obtain ⟨k, rfl⟩ := (hF.isCorner_iff o).mp hc
    exact (hadj k).ne rfl
  · obtain ⟨j, hj⟩ := (hF.adj_iff k i).mp hi
    rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 by omega) with h | h | h <;>
      rw [h] at hj
    · left
      apply A.center_injective
      rw [hj, hF.side k, hL k]
      push_cast
      ring
    · right; right
      apply A.center_injective
      rw [hj, hpo k]
    · right; left
      apply A.center_injective
      have hs := hF.side (k - 1)
      rw [sub_add_cancel, hL] at hs
      rw [hj, hs, pow_add, rho_pow_val_sub_one k]
      push_cast
      linear_combination 2 * ω * rho ^ ((k - 1 : Fin 6) : ℕ) * rho_pow_three
  · rw [hpo k]
    linear_combination -2 * ω * rho ^ (k : ℕ) * rho * rho_pow_three

/-- **Proposition H.** In setting S6, if at most two circles are not corners, the arrangement
contains the flower: there is a circle `o`, not a corner, touching all six corners, each corner
touches only `o` and its two neighbours on the hexagon, and `eₖ = o + 2 ζ ρᵏ` with
`ζ = ω ρ⁴`. -/
theorem exists_hub_of_few (hF : A.IsSixCornerFrame e ω L)
    (hfew : ∀ a b c : ι, ¬ A.IsCorner a → ¬ A.IsCorner b → ¬ A.IsCorner c →
      a = b ∨ a = c ∨ b = c) :
    ∃ o, ¬ A.IsCorner o ∧ (∀ k, A.contactGraph.Adj (e k) o) ∧
      (∀ k i, A.contactGraph.Adj (e k) i → i = e (k + 1) ∨ i = e (k - 1) ∨ i = o) ∧
      ∀ k : Fin 6, A.center (e k) = A.center o + 2 * (ω * rho ^ 4) * rho ^ (k : ℕ) :=
  hF.exists_hub (hF.sides_eq_two hfew)

end IsSixCornerFrame

end Arrangement

end RigidArrangements
