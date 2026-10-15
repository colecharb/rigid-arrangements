import RigidArrangements.Core
import RigidArrangements.Flex
import RigidArrangements.Henneberg
import RigidArrangements.Isometry

/-!
# No cores with three to six circles: the hull lemma

A circle of an arrangement is *removable* (`Arrangement.Removable`) if it touches exactly two
circles and these two are less than `4` apart; a *core* (`Arrangement.IsCore`) has no
removable circle. This file proves that **every rigid arrangement of `3` to `6` circles has a
removable circle** (`noCoresBetween_three_six`, and `noCoresBetween_four_six`, the form of the
hypothesis used in `RigidArrangements.Small`). Removing a removable circle keeps rigidity
(`Arrangement.IsRigid.erase`), so every rigid arrangement of three to six circles is built
from the triangle by adding circles one at a time, each touching two earlier ones.

## The hull lemma

The first half uses only two facts: every circle touches at least two others (which holds in
every rigid arrangement of at least three circles, `Arrangement.IsRigid.touchesTwo`), and no
circle is removable. Rigidity itself is not used.

* **Extreme circles.** Fix a direction, the unit vector of angle `θ`. Pick the circle whose
  center is furthest in that direction, breaking ties by the perpendicular direction `θ + 90°`
  (`Arrangement.IsExtreme`, `Arrangement.exists_isExtreme`). Seen from this circle, every
  other center lies in the half-open half-plane of directions `(θ + 90°, θ + 270°]`.
* **At most three neighbours, and not two.** The neighbours of a circle are at distance `2`
  from it and at least `2` from each other, so seen from it any two of them are at least
  `60°` apart. A half-open half-plane (an arc of `180°`) has room for at most three of them.
  Two neighbours inside it are never diametrically opposite, so they are less than `4` apart
  (`Arrangement.IsExtreme.dist_lt_four`), and an extreme circle with only two neighbours is
  removable. So in a core every extreme circle touches exactly three others
  (`Arrangement.IsExtreme.touchesExactlyThree`).
* **Narrow range of directions.** A circle cannot be extreme in two directions `θ` and
  `θ + δ` with `60° ≤ δ ≤ 180°` (`Arrangement.IsExtreme.not_isExtreme_add`): its neighbours
  would lie in both half-open half-planes, a half-open arc of at most `120°`, and three
  neighbours `60°` apart do not fit there.
* **Six directions.** The extreme circles in the directions `0°, 60°, …, 300°` are therefore
  pairwise different. This is the **hull lemma** (`Arrangement.exists_injective_isExtreme`,
  `Arrangement.exists_injective_touchesExactlyThree`, `Arrangement.six_le_card_degree_three`):
  in an arrangement where every circle touches two others and none is removable, at least
  six circles touch exactly three others. In particular such an arrangement has at least six
  circles (`Arrangement.six_le_card_of_isCore`), so no core of three to five circles has
  every circle touching two others. Hence there is no rigid core of three to five circles.

Angles are measured with `Complex.arg`: for a neighbour `j` of a circle `i` that is extreme in
direction `θ`, the vector from `j` to `i`, rotated by `-θ`, has its argument in `(-90°, 90°]`.

## Six circles

Suppose a rigid core has exactly six circles. All six are extreme circles, so each touches
exactly three others: the contact graph is cubic.

* The three neighbours `p, q, r` of a circle `v` cannot be pairwise apart. Otherwise each of
  them would touch `v` and both of the two remaining circles, and `v` and one of those would
  have three common neighbours. But two different circles have at most two common neighbours:
  the points at distance `2` from two different centers are mirror images in the line through
  them (`Arrangement.not_three_common_neighbors`). This rules out the graph `K₃,₃`.
* So there is a triangle `a₁a₂a₃` of mutually touching circles. Let `bᵢ` be the third
  neighbour of `aᵢ`. If two of the `bᵢ` coincide, either the four circles `a₁, a₂, a₃, b`
  form a whole component (not rigid, by the translation flex), or the sixth circle has only
  two circles left that it could touch.
* So the contact graph is the triangular prism: triangles `a₁a₂a₃`, `b₁b₂b₃` and contacts
  `aᵢbᵢ`. Each quadrilateral `aᵢbᵢbⱼaⱼ` has four sides of length `2`, so it is a
  parallelogram (`sub_eq_sub_of_rhombus`; its diagonals cannot degenerate because distinct
  circles have distinct centers). Hence all vectors `bᵢ - aᵢ` are equal, and the shear flex
  (`Arrangement.not_isRigid_of_shear_of_three_le`) slides the triangle `a₁a₂a₃` along the
  triangle `b₁b₂b₃`: the arrangement is not rigid.

So no rigid core has six circles (`Arrangement.IsRigid.not_isCore_of_card_eq_six`), and with
the hull lemma, **a rigid core of at least three circles has at least seven circles**
(`Arrangement.IsRigid.seven_le_card_of_isCore`). (One circle, and two touching circles, are
rigid cores too.) The bound is sharp: the flower (a hexagon of six circles around a seventh)
is a rigid core; this is not formalized here.

## Main results

* `Arrangement.IsExtreme`, `Arrangement.exists_isExtreme`: extreme circles exist.
* `Arrangement.IsExtreme.touchesExactlyThree`, `Arrangement.IsExtreme.not_isExtreme_add`:
  in a core in which every circle touches two others, an extreme circle touches exactly three
  others and is extreme only in a range of directions narrower than `60°`.
* `Arrangement.exists_injective_touchesExactlyThree`, `Arrangement.six_le_card_degree_three`:
  the hull lemma.
* `Arrangement.not_three_common_neighbors`, `sub_eq_sub_of_rhombus`: two plane facts.
* `Arrangement.IsRigid.seven_le_card_of_isCore`: a rigid core of at least three circles has
  at least seven circles.
* `noCoresBetween_four_six`: every rigid arrangement of `4`, `5` or `6` circles has a removable
  circle (also `noCoresBetween_three_six`).
-/

open Complex

namespace RigidArrangements

/-! ### Plane geometry -/

/-- `z` is positive in the lexicographic order of the plane: `0 < re z`, or `re z = 0` and
`0 < im z`. Equivalently, `z ≠ 0` and `arg z ∈ (-π/2, π/2]`. -/
def LexPos (z : ℂ) : Prop :=
  0 < z.re ∨ (z.re = 0 ∧ 0 < z.im)

/-- A lexicographically positive complex number has its argument in `(-π/2, π/2]`. -/
theorem LexPos.arg_mem {z : ℂ} (h : LexPos z) :
    -(Real.pi / 2) < arg z ∧ arg z ≤ Real.pi / 2 := by
  constructor
  · refine lt_of_le_of_ne (neg_pi_div_two_le_arg_iff.mpr ?_) fun h' => ?_
    · rcases h with h | ⟨-, h⟩
      · exact Or.inl h.le
      · exact Or.inr h.le
    · have := arg_eq_neg_pi_div_two_iff.mp h'.symm
      rcases h with h | ⟨-, h⟩ <;> linarith [this.1, this.2]
  · apply arg_le_pi_div_two_iff.mpr
    rcases h with h | ⟨h, -⟩
    · exact Or.inl h.le
    · exact Or.inl h.ge

/-- Law of cosines for two vectors of length `2`. -/
theorem norm_sub_sq_of_norm_eq_two {z w : ℂ} (hz : ‖z‖ = 2) (hw : ‖w‖ = 2) :
    ‖z - w‖ ^ 2 = 8 - 8 * Real.cos (arg z - arg w) := by
  have h1 := norm_mul_cos_arg z
  have h2 := norm_mul_sin_arg z
  have h3 := norm_mul_cos_arg w
  have h4 := norm_mul_sin_arg w
  rw [hz] at h1 h2
  rw [hw] at h3 h4
  rw [Complex.sq_norm, Complex.normSq_apply, Real.cos_sub, Complex.sub_re, Complex.sub_im, ← h1,
    ← h2, ← h3, ← h4]
  linear_combination 4 * Real.sin_sq_add_cos_sq (arg z) + 4 * Real.sin_sq_add_cos_sq (arg w)

/-- Two vectors of length `2` whose ends are at least `2` apart make an angle of at least
`60°`. -/
theorem pi_div_three_le_abs_arg_sub {z w : ℂ} (hz : ‖z‖ = 2) (hw : ‖w‖ = 2)
    (hzw : 2 ≤ ‖z - w‖) : Real.pi / 3 ≤ |arg z - arg w| := by
  by_contra hlt
  push Not at hlt
  have hc : 1 / 2 < Real.cos (arg z - arg w) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hlt
  have := norm_sub_sq_of_norm_eq_two hz hw
  nlinarith

/-- Two vectors of length `2` making an angle of less than `180°` have ends less than `4`
apart. -/
theorem norm_sub_lt_four_of_abs_arg_sub_lt {z w : ℂ} (hz : ‖z‖ = 2) (hw : ‖w‖ = 2)
    (h : |arg z - arg w| < Real.pi) : ‖z - w‖ < 4 := by
  have hc : -1 < Real.cos (arg z - arg w) := by
    rw [← Real.cos_abs, ← Real.cos_pi]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) le_rfl h
  have := norm_sub_sq_of_norm_eq_two hz hw
  nlinarith [norm_nonneg (z - w)]

/-- If rotating a vector `z` of length `2` by `-δ` gives a lexicographically positive vector,
then the angle `arg z - δ` points into the lexicographically positive half-plane: its cosine
is positive, or zero with positive sine. (The rotated vector is `2` times the unit vector of
angle `arg z - δ`.) -/
theorem lexPos_mul_exp {z : ℂ} (hz : ‖z‖ = 2) (δ : ℝ)
    (h : LexPos (z * exp (↑(-δ) * I))) :
    0 < Real.cos (arg z - δ) ∨ (Real.cos (arg z - δ) = 0 ∧ 0 < Real.sin (arg z - δ)) := by
  have e : z * exp (↑(-δ) * I) = (2 : ℝ) * exp (↑(arg z - δ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [hz, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, LexPos, Complex.re_ofReal_mul, Complex.im_ofReal_mul, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im] at h
  rcases h with h | ⟨h1, h2⟩
  · left; linarith
  · right; constructor <;> linarith

/-- If `t > -90°` and `δ ≤ 180°`, and the angle `t - δ` points into the lexicographically
positive half-plane, then `t > δ - 90°`. -/
private theorem lt_of_cos_sub {t δ : ℝ} (ht : -(Real.pi / 2) < t) (hδ : δ ≤ Real.pi)
    (h : 0 < Real.cos (t - δ) ∨ (Real.cos (t - δ) = 0 ∧ 0 < Real.sin (t - δ))) :
    δ - Real.pi / 2 < t := by
  by_contra hle
  push Not at hle
  have hs2 : -(Real.pi / 2) < t - δ + Real.pi := by linarith
  rcases (show t - δ + Real.pi ≤ Real.pi / 2 by linarith).lt_or_eq with hlt | heq
  · have := Real.cos_pos_of_mem_Ioo ⟨hs2, hlt⟩
    rw [Real.cos_add_pi] at this
    rcases h with h | ⟨h, -⟩ <;> linarith
  · rw [show t - δ = -(Real.pi / 2) by linarith] at h
    norm_num at h

/-- Three reals in a half-open interval of length `2δ` cannot be pairwise `δ` apart. -/
private theorem false_of_three_sep {δ lo a b c : ℝ} (ha : lo < a)
    (ha' : a ≤ lo + 2 * δ) (hb : lo < b) (hb' : b ≤ lo + 2 * δ) (hc : lo < c)
    (hc' : c ≤ lo + 2 * δ) (hab : δ ≤ |a - b|) (hac : δ ≤ |a - c|) (hbc : δ ≤ |b - c|) :
    False := by
  rcases le_abs.mp hab with h1 | h1 <;> rcases le_abs.mp hac with h2 | h2 <;>
    rcases le_abs.mp hbc with h3 | h3 <;> linarith

/-- Four reals in a half-open interval of length `3δ` cannot be pairwise `δ` apart. -/
private theorem false_of_four_sep {δ lo a b c d : ℝ} (ha : lo < a)
    (ha' : a ≤ lo + 3 * δ) (hb : lo < b) (hb' : b ≤ lo + 3 * δ) (hc : lo < c)
    (hc' : c ≤ lo + 3 * δ) (hd : lo < d) (hd' : d ≤ lo + 3 * δ) (hab : δ ≤ |a - b|)
    (hac : δ ≤ |a - c|) (had : δ ≤ |a - d|) (hbc : δ ≤ |b - c|) (hbd : δ ≤ |b - d|)
    (hcd : δ ≤ |c - d|) : False := by
  rcases le_abs.mp hab with h1 | h1 <;> rcases le_abs.mp hac with h2 | h2 <;>
    rcases le_abs.mp had with h3 | h3 <;> rcases le_abs.mp hbc with h4 | h4 <;>
    rcases le_abs.mp hbd with h5 | h5 <;> rcases le_abs.mp hcd with h6 | h6 <;> linarith

/-- Four vectors of length `2` that add up to zero cancel in pairs (same identity as in
`RigidArrangements.Flex`). -/
private theorem prod_add_eq_zero_of_norm_eq_two {x y z w : ℂ} (hx : ‖x‖ = 2) (hy : ‖y‖ = 2)
    (hz : ‖z‖ = 2) (hw : ‖w‖ = 2) (hs : x + y + z + w = 0) :
    (x + y) * (x + z) * (x + w) = 0 := by
  have hc : ∀ u : ℂ, ‖u‖ = 2 → u * starRingEnd ℂ u = 4 := fun u hu => by
    rw [Complex.mul_conj', hu]
    norm_num
  have hs' : starRingEnd ℂ x + starRingEnd ℂ y + starRingEnd ℂ z + starRingEnd ℂ w = 0 := by
    simp only [← map_add, hs, map_zero]
  linear_combination x ^ 2 * hs + x * y * z * w / 4 * hs' - y * z * w / 4 * hc x hx -
    x * z * w / 4 * hc y hy - x * y * w / 4 * hc z hz - x * y * z / 4 * hc w hw

/-- **Rhombus lemma.** If `p, q, r, s` are four points of the plane with `|pq| = |qr| = |rs| =
|sp| = 2`, `p ≠ r` and `q ≠ s`, then `pqrs` is a parallelogram: `q - p = r - s`. -/
theorem sub_eq_sub_of_rhombus {p q r s : ℂ} (h₁ : ‖q - p‖ = 2) (h₂ : ‖r - q‖ = 2)
    (h₃ : ‖s - r‖ = 2) (h₄ : ‖p - s‖ = 2) (hpr : p ≠ r) (hqs : q ≠ s) : q - p = r - s := by
  have := prod_add_eq_zero_of_norm_eq_two h₁ h₂ h₃ h₄ (by ring)
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd (by linear_combination -h) hpr
    · linear_combination h
  · exact absurd (by linear_combination h) hqs

theorem norm_mul_exp_neg (z : ℂ) (θ : ℝ) : ‖z * exp (↑(-θ) * I)‖ = ‖z‖ := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]

namespace Arrangement

variable {ι : Type*} (A : Arrangement ι)

/-! ### Extreme circles -/

/-- Circle `i` is *extreme in direction `θ`*: its center is furthest in the direction of the
unit vector `exp (θ i)`, ties being broken by the perpendicular direction `exp ((θ + π/2) i)`.
Formally, for every other circle `j`, the vector from `j` to `i`, rotated by `-θ`, is
lexicographically positive. Seen from `i`, every other center then lies in the half-open
half-plane of directions `(θ + π/2, θ + 3π/2]`. -/
def IsExtreme (θ : ℝ) (i : ι) : Prop :=
  ∀ j, j ≠ i → LexPos ((A.center i - A.center j) * exp (↑(-θ) * I))

/-- Circle `i` touches exactly three other circles, `a`, `b` and `c`. -/
def TouchesExactlyThree (i : ι) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ k, A.contactGraph.Adj i k ↔ k = a ∨ k = b ∨ k = c

/-- A finite nonempty arrangement has an extreme circle in every direction: the maximum of the
lexicographic order after rotating by `-θ`. -/
theorem exists_isExtreme [Finite ι] [Nonempty ι] (θ : ℝ) : ∃ i, A.IsExtreme θ i := by
  set r := exp (↑(-θ) * I)
  have hr : r ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => toLex ((A.center i * r).re, (A.center i * r).im)
  refine ⟨i, fun j hji => ?_⟩
  have hne : toLex ((A.center j * r).re, (A.center j * r).im) ≠
      toLex ((A.center i * r).re, (A.center i * r).im) := by
    intro e
    have e' := Prod.ext_iff.mp (toLex.injective e)
    exact hji (A.center_injective (mul_right_cancel₀ hr (Complex.ext e'.1 e'.2)))
  have hlt := Prod.Lex.toLex_lt_toLex.mp (lt_of_le_of_ne (hi j) hne)
  simp only [LexPos, sub_mul, Complex.sub_re, Complex.sub_im]
  rcases hlt with h | ⟨h1, h2⟩
  · left; linarith
  · right; constructor <;> linarith

/-- Directions are angles modulo `2π`. -/
theorem isExtreme_add_two_pi {θ : ℝ} {i : ι} :
    A.IsExtreme (θ + 2 * Real.pi) i ↔ A.IsExtreme θ i := by
  have e : exp (↑(-(θ + 2 * Real.pi)) * I) = exp (↑(-θ) * I) := by
    rw [show (↑(-(θ + 2 * Real.pi)) * I : ℂ) = ↑(-θ) * I - 2 * Real.pi * I by push_cast; ring,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  simp only [IsExtreme, e]

variable {A}

theorem norm_adj {i j : ι} (h : A.contactGraph.Adj i j) :
    ‖A.center i - A.center j‖ = 2 := by
  rw [← dist_eq_norm]; exact h.2

/-- Facts about the vector from a neighbour `j` to an extreme circle `i`, rotated so that the
direction becomes the positive real axis: it has length `2` and its argument lies in
`(-π/2, π/2]`. -/
theorem IsExtreme.arg_mem {θ : ℝ} {i j : ι} (he : A.IsExtreme θ i)
    (hj : A.contactGraph.Adj i j) :
    ‖(A.center i - A.center j) * exp (↑(-θ) * I)‖ = 2 ∧
      -(Real.pi / 2) < arg ((A.center i - A.center j) * exp (↑(-θ) * I)) ∧
      arg ((A.center i - A.center j) * exp (↑(-θ) * I)) ≤ Real.pi / 2 := by
  refine ⟨by rw [norm_mul_exp_neg, norm_adj hj], (he j hj.ne.symm).arg_mem⟩

private theorem IsExtreme.norm_sub {θ : ℝ} {i j k : ι} :
    ‖(A.center i - A.center j) * exp (↑(-θ) * I) - (A.center i - A.center k) * exp (↑(-θ) * I)‖ =
      dist (A.center j) (A.center k) := by
  rw [← sub_mul, norm_mul_exp_neg, dist_comm, dist_eq_norm]
  congr 1; ring

/-- Two neighbours of an extreme circle are less than `4` apart: seen from it they lie in a
half-open half-plane, so they are not diametrically opposite. -/
theorem IsExtreme.dist_lt_four {θ : ℝ} {i j k : ι} (he : A.IsExtreme θ i)
    (hj : A.contactGraph.Adj i j) (hk : A.contactGraph.Adj i k) :
    dist (A.center j) (A.center k) < 4 := by
  obtain ⟨hj1, hj2, hj3⟩ := he.arg_mem hj
  obtain ⟨hk1, hk2, hk3⟩ := he.arg_mem hk
  rw [← IsExtreme.norm_sub (θ := θ) (i := i)]
  exact norm_sub_lt_four_of_abs_arg_sub_lt hj1 hk1 (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)

/-- Seen from any circle, two of its neighbours are at least `60°` apart (their centers are at
distance `2` from it and at least `2` from each other). -/
theorem IsExtreme.pi_div_three_le {θ : ℝ} {i j k : ι} (he : A.IsExtreme θ i)
    (hj : A.contactGraph.Adj i j) (hk : A.contactGraph.Adj i k) (hjk : j ≠ k) :
    Real.pi / 3 ≤ |arg ((A.center i - A.center j) * exp (↑(-θ) * I)) -
      arg ((A.center i - A.center k) * exp (↑(-θ) * I))| :=
  pi_div_three_le_abs_arg_sub (he.arg_mem hj).1 (he.arg_mem hk).1
    (by rw [IsExtreme.norm_sub]; exact A.nonoverlap hjk)

/-- In a core in which every circle touches two others, an extreme circle touches at least
three others: with only two contacts it would be removable. -/
theorem IsExtreme.exists_three {θ : ℝ} {i : ι} (hT : A.TouchesTwo) (hc : A.IsCore)
    (he : A.IsExtreme θ i) :
    ∃ j k l, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ A.contactGraph.Adj i j ∧ A.contactGraph.Adj i k ∧
      A.contactGraph.Adj i l := by
  obtain ⟨j, k, hjk, hij, hik, hj, hk⟩ := hT i
  have hj' : A.contactGraph.Adj i j := ⟨hij, hj⟩
  have hk' : A.contactGraph.Adj i k := ⟨hik, hk⟩
  by_contra hno
  refine hc i ⟨j, k, hjk, fun l => ⟨fun hl => ?_, ?_⟩, he.dist_lt_four hj' hk'⟩
  · by_contra hl'
    push Not at hl'
    exact hno ⟨j, k, l, hjk, Ne.symm hl'.1, Ne.symm hl'.2, hj', hk', hl⟩
  · rintro (rfl | rfl) <;> assumption

/-- In a core in which every circle touches two others, an extreme circle touches exactly
three others: a fourth neighbour would not fit in the half-plane, since four directions
pairwise at least `60°` apart span at least `180°`. -/
theorem IsExtreme.touchesExactlyThree {θ : ℝ} {i : ι} (hT : A.TouchesTwo) (hc : A.IsCore)
    (he : A.IsExtreme θ i) : A.TouchesExactlyThree i := by
  obtain ⟨j, k, l, hjk, hjl, hkl, hj, hk, hl⟩ := he.exists_three hT hc
  refine ⟨j, k, l, hjk, hjl, hkl, fun m => ⟨fun hm => ?_, ?_⟩⟩
  · by_contra hm'
    push Not at hm'
    obtain ⟨hmj, hmk, hml⟩ := hm'
    have hπ := Real.pi_pos
    obtain ⟨-, a1, a2⟩ := he.arg_mem hj
    obtain ⟨-, b1, b2⟩ := he.arg_mem hk
    obtain ⟨-, c1, c2⟩ := he.arg_mem hl
    obtain ⟨-, d1, d2⟩ := he.arg_mem hm
    exact false_of_four_sep (δ := Real.pi / 3) (lo := -(Real.pi / 2))
      a1 (by linarith) b1 (by linarith) c1 (by linarith) d1 (by linarith)
      (he.pi_div_three_le hj hk hjk) (he.pi_div_three_le hj hl hjl)
      (he.pi_div_three_le hj hm (Ne.symm hmj)) (he.pi_div_three_le hk hl hkl)
      (he.pi_div_three_le hk hm (Ne.symm hmk)) (he.pi_div_three_le hl hm (Ne.symm hml))
  · rintro (rfl | rfl | rfl) <;> assumption

/-- **An extreme circle of a core is extreme only in a narrow range of directions.** If every
circle touches two others and no circle is removable, a circle that is extreme in direction
`θ` is not extreme in any direction `θ + δ` with `60° ≤ δ ≤ 180°`. Its (at least three)
neighbours, pairwise at least `60°` apart, would have to fit in the half-open half-planes
behind both directions, which leave a half-open arc of at most `120°`. -/
theorem IsExtreme.not_isExtreme_add {θ δ : ℝ} {i : ι} (hT : A.TouchesTwo) (hc : A.IsCore)
    (he : A.IsExtreme θ i) (hδ₁ : Real.pi / 3 ≤ δ) (hδ₂ : δ ≤ Real.pi) :
    ¬ A.IsExtreme (θ + δ) i := by
  intro he'
  obtain ⟨j, k, l, hjk, hjl, hkl, hj, hk, hl⟩ := he.exists_three hT hc
  have key : ∀ m, A.contactGraph.Adj i m →
      δ - Real.pi / 2 < arg ((A.center i - A.center m) * exp (↑(-θ) * I)) := by
    intro m hm
    have h1 := he' m hm.ne.symm
    rw [show (A.center i - A.center m) * exp (↑(-(θ + δ)) * I) =
        (A.center i - A.center m) * exp (↑(-θ) * I) * exp (↑(-δ) * I) by
      rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring] at h1
    exact lt_of_cos_sub (he.arg_mem hm).2.1 hδ₂ (lexPos_mul_exp (he.arg_mem hm).1 δ h1)
  have hπ := Real.pi_pos
  exact false_of_three_sep (δ := Real.pi / 3) (lo := -(Real.pi / 6))
    (by linarith [key j hj]) (by linarith [(he.arg_mem hj).2.2])
    (by linarith [key k hk]) (by linarith [(he.arg_mem hk).2.2])
    (by linarith [key l hl]) (by linarith [(he.arg_mem hl).2.2])
    (he.pi_div_three_le hj hk hjk) (he.pi_div_three_le hj hl hjl) (he.pi_div_three_le hk hl hkl)

/-! ### The hull lemma -/

/-- A circle is not extreme in two of the six directions `0°, 60°, …, 300°`. -/
private theorem IsExtreme.false_of_lt {i : ι} (hT : A.TouchesTwo) (hc : A.IsCore) {k l : ℕ}
    (hkl : k < l) (hl6 : l < 6) (hk : A.IsExtreme (k * Real.pi / 3) i)
    (hl : A.IsExtreme (l * Real.pi / 3) i) : False := by
  have hπ := Real.pi_pos
  have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  have hl6' : (l : ℝ) + 1 ≤ 6 := by exact_mod_cast hl6
  by_cases h3 : l ≤ k + 3
  · have h3' : (l : ℝ) ≤ k + 3 := by exact_mod_cast h3
    exact hk.not_isExtreme_add hT hc (δ := ((l : ℝ) - k) * Real.pi / 3) (by nlinarith)
      (by nlinarith) (by convert hl using 2; ring)
  · have h3' : (k : ℝ) + 4 ≤ l := by exact_mod_cast (show k + 4 ≤ l by omega)
    rw [← A.isExtreme_add_two_pi] at hk
    exact hl.not_isExtreme_add hT hc (δ := (6 - ((l : ℝ) - k)) * Real.pi / 3) (by nlinarith)
      (by nlinarith) (by
        rwa [show (l : ℝ) * Real.pi / 3 + (6 - ((l : ℝ) - k)) * Real.pi / 3 =
          k * Real.pi / 3 + 2 * Real.pi by ring])

/-- **Six extreme circles.** For each of the six directions `0°, 60°, …, 300°` pick an extreme
circle. In a core in which every circle touches two others, these six circles are pairwise
different. -/
theorem exists_injective_isExtreme [Finite ι] [Nonempty ι] (hT : A.TouchesTwo) (hc : A.IsCore) :
    ∃ e : Fin 6 → ι, Function.Injective e ∧
      ∀ k : Fin 6, A.IsExtreme ((k : ℕ) * Real.pi / 3) (e k) := by
  choose e he using fun k : Fin 6 => A.exists_isExtreme ((k : ℕ) * Real.pi / 3)
  refine ⟨e, fun k l hkl => ?_, he⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact (he k).false_of_lt hT hc h l.isLt (hkl ▸ he l)
  · exact (he l).false_of_lt hT hc h k.isLt (hkl ▸ he k)

/-- **Hull lemma.** In an arrangement in which every circle touches at least two others and no
circle is removable, at least six different circles touch exactly three others. -/
theorem exists_injective_touchesExactlyThree [Finite ι] [Nonempty ι] (hT : A.TouchesTwo)
    (hc : A.IsCore) :
    ∃ e : Fin 6 → ι, Function.Injective e ∧ ∀ k, A.TouchesExactlyThree (e k) := by
  obtain ⟨e, he, hext⟩ := A.exists_injective_isExtreme hT hc
  exact ⟨e, he, fun k => (hext k).touchesExactlyThree hT hc⟩

/-- A core in which every circle touches two others has at least six circles. -/
theorem six_le_card_of_isCore [Finite ι] [Nonempty ι] (hT : A.TouchesTwo) (hc : A.IsCore) :
    6 ≤ Nat.card ι := by
  obtain ⟨e, he, -⟩ := A.exists_injective_isExtreme hT hc
  simpa using Nat.card_le_card_of_injective e he

/-- A circle touching exactly three others has degree `3` in the contact graph. -/
theorem TouchesExactlyThree.ncard_neighborSet {i : ι} (h : A.TouchesExactlyThree i) :
    (A.contactGraph.neighborSet i).ncard = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hk⟩ := h
  have : A.contactGraph.neighborSet i = {a, b, c} := by
    ext k
    simp [SimpleGraph.mem_neighborSet, hk]
  rw [this, Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]

/-- **Hull lemma**, counting form: in an arrangement in which every circle touches at least two
others and no circle is removable, at least six circles have degree `3` in the contact
graph. -/
theorem six_le_card_degree_three [Finite ι] [Nonempty ι] (hT : A.TouchesTwo) (hc : A.IsCore) :
    6 ≤ Nat.card {i // (A.contactGraph.neighborSet i).ncard = 3} := by
  obtain ⟨e, he, h3⟩ := A.exists_injective_touchesExactlyThree hT hc
  have := Nat.card_le_card_of_injective (fun k => (⟨e k, (h3 k).ncard_neighborSet⟩ :
    {i // (A.contactGraph.neighborSet i).ncard = 3})) fun k l hkl => he (congrArg Subtype.val hkl)
  simpa using this

/-! ### Six circles -/

/-- Two different circles have at most two common neighbours: the points at distance `2` from
two different centers are mirror images of each other in the line through these centers. -/
theorem not_three_common_neighbors {x y p q r : ι} (hxy : x ≠ y) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hxp : A.contactGraph.Adj x p) (hxq : A.contactGraph.Adj x q)
    (hxr : A.contactGraph.Adj x r) (hyp : A.contactGraph.Adj y p) (hyq : A.contactGraph.Adj y q)
    (hyr : A.contactGraph.Adj y r) : False := by
  have hab : A.center x ≠ A.center y := A.center_injective.ne hxy
  have hd : ∀ m, A.contactGraph.Adj x m → A.contactGraph.Adj y m →
      dist (A.center m) (A.center x) = dist (A.center p) (A.center x) ∧
        dist (A.center m) (A.center y) = dist (A.center p) (A.center y) := by
    intro m hxm hym
    rw [dist_comm, hxm.2, dist_comm, hxp.2, dist_comm, hym.2, dist_comm, hyp.2]
    exact ⟨rfl, rfl⟩
  rcases eq_or_eq_reflect hab (hd q hxq hyq).1 (hd q hxq hyq).2 with h | h
  · exact hpq (A.center_injective h).symm
  rcases eq_or_eq_reflect hab (hd r hxr hyr).1 (hd r hxr hyr).2 with h' | h'
  · exact hpr (A.center_injective h').symm
  · exact hqr (A.center_injective (h.trans h'.symm))

/-- With exactly six elements, five elements always miss a sixth. -/
private theorem exists_ne_five [Finite ι] (hn : Nat.card ι = 6) (a b c d e : ι) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d ∧ x ≠ e := by
  classical
  have := Fintype.ofFinite ι
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset ι) ⊆ {a, b, c, d, e} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hx
    push Not at hx
    exact hx.2.2.2.2 (h x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hn] at h1
  have h2 : ({a, b, c, d, e} : Finset ι).card ≤ 5 := Finset.card_le_five
  omega

/-- With exactly six elements, six different elements are all of them. -/
private theorem eq_of_six [Finite ι] (hn : Nat.card ι = 6) {a b c d e f : ι} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hbf : b ≠ f) (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e)
    (hdf : d ≠ f) (hef : e ≠ f) (x : ι) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  classical
  have := Fintype.ofFinite ι
  by_contra hx
  push Not at hx
  obtain ⟨hxa, hxb, hxc, hxd, hxe, hxf⟩ := hx
  have hnd : [x, a, b, c, d, e, f].Nodup := by
    simp [hxa, hxb, hxc, hxd, hxe, hxf, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce,
      hcf, hde, hdf, hef]
  have h1 := Finset.card_le_univ [x, a, b, c, d, e, f].toFinset
  rw [List.toFinset_card_of_nodup hnd, ← Nat.card_eq_fintype_card, hn] at h1
  simp at h1

/-- A circle that touches exactly three others, one of them `a`: the other two. -/
theorem TouchesExactlyThree.exists_two {i a : ι} (h : A.TouchesExactlyThree i)
    (ha : A.contactGraph.Adj i a) :
    ∃ b c, b ≠ c ∧ b ≠ a ∧ c ≠ a ∧ ∀ k, A.contactGraph.Adj i k ↔ k = a ∨ k = b ∨ k = c := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hk⟩ := h
  rcases (hk a).mp ha with rfl | rfl | rfl
  · exact ⟨y, z, hyz, Ne.symm hxy, Ne.symm hxz, hk⟩
  · exact ⟨x, z, hxz, hxy, Ne.symm hyz, fun k => by rw [hk]; tauto⟩
  · exact ⟨x, y, hxy, hxz, hyz, fun k => by rw [hk]; tauto⟩

/-- A circle that touches exactly three others, two of them `a` and `b`: the third one. -/
theorem TouchesExactlyThree.exists_third {i a b : ι} (h : A.TouchesExactlyThree i)
    (ha : A.contactGraph.Adj i a) (hb : A.contactGraph.Adj i b) (hab : a ≠ b) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ ∀ k, A.contactGraph.Adj i k ↔ k = a ∨ k = b ∨ k = c := by
  obtain ⟨x, y, hxy, hxa, hya, hk⟩ := h.exists_two ha
  rcases (hk b).mp hb with h | rfl | rfl
  · exact absurd h.symm hab
  · exact ⟨y, hya, Ne.symm hxy, hk⟩
  · exact ⟨x, hxa, hxy, fun k => by rw [hk]; tauto⟩

/-- **The triangular prism is impossible.** Two triangles `a₁a₂a₃` and `b₁b₂b₃` joined by the
contacts `aᵢbᵢ`, in a rigid arrangement of six circles. Each quadrilateral `aᵢbᵢbⱼaⱼ` is a
rhombus, so `bᵢ - aᵢ` is the same vector for all `i`, and the shear flex moves one triangle
against the other. -/
private theorem false_of_prism [Finite ι] (h : A.IsRigid) (hn : Nat.card ι = 6)
    (h3 : ∀ i, A.TouchesExactlyThree i) {a₁ a₂ a₃ b₁ b₂ b₃ : ι}
    (ha₁ : ∀ k, A.contactGraph.Adj a₁ k ↔ k = a₂ ∨ k = a₃ ∨ k = b₁)
    (ha₂ : ∀ k, A.contactGraph.Adj a₂ k ↔ k = a₁ ∨ k = a₃ ∨ k = b₂)
    (ha₃ : ∀ k, A.contactGraph.Adj a₃ k ↔ k = a₁ ∨ k = a₂ ∨ k = b₃)
    (hb₁₂ : b₁ ≠ a₂) (hb₁₃ : b₁ ≠ a₃) (hb₂₁ : b₂ ≠ a₁) (hb₂₃ : b₂ ≠ a₃) (hb₃₁ : b₃ ≠ a₁)
    (hb₃₂ : b₃ ≠ a₂) (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃) : False := by
  have e12 : A.contactGraph.Adj a₁ a₂ := (ha₁ a₂).mpr (Or.inl rfl)
  have e13 : A.contactGraph.Adj a₁ a₃ := (ha₁ a₃).mpr (Or.inr (Or.inl rfl))
  have e23 : A.contactGraph.Adj a₂ a₃ := (ha₂ a₃).mpr (Or.inr (Or.inl rfl))
  have f1 : A.contactGraph.Adj a₁ b₁ := (ha₁ b₁).mpr (Or.inr (Or.inr rfl))
  have f2 : A.contactGraph.Adj a₂ b₂ := (ha₂ b₂).mpr (Or.inr (Or.inr rfl))
  have f3 : A.contactGraph.Adj a₃ b₃ := (ha₃ b₃).mpr (Or.inr (Or.inr rfl))
  have hall := eq_of_six hn e12.ne e13.ne f1.ne (Ne.symm hb₂₁) (Ne.symm hb₃₁) e23.ne
    (Ne.symm hb₁₂) f2.ne (Ne.symm hb₃₂) (Ne.symm hb₁₃) (Ne.symm hb₂₃) f3.ne h12 h13 h23
  -- `b₁` touches `b₂` and `b₃`
  obtain ⟨u, v, huv, hua, hva, hb₁⟩ := (h3 b₁).exists_two f1.symm
  have hnot : ∀ w, A.contactGraph.Adj b₁ w → w ≠ a₁ → w = b₂ ∨ w = b₃ := by
    intro w hw hwa
    rcases hall w with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hwa
    · rcases (ha₂ b₁).mp hw.symm with e | e | e
      · exact absurd e f1.ne.symm
      · exact absurd e hb₁₃
      · exact absurd e h12
    · rcases (ha₃ b₁).mp hw.symm with e | e | e
      · exact absurd e f1.ne.symm
      · exact absurd e hb₁₂
      · exact absurd e h13
    · exact absurd rfl hw.ne
    · exact Or.inl rfl
    · exact Or.inr rfl
  have g : A.contactGraph.Adj b₁ b₂ ∧ A.contactGraph.Adj b₁ b₃ := by
    rcases hnot u ((hb₁ u).mpr (Or.inr (Or.inl rfl))) hua with rfl | rfl <;>
      rcases hnot v ((hb₁ v).mpr (Or.inr (Or.inr rfl))) hva with rfl | rfl
    · exact absurd rfl huv
    · exact ⟨(hb₁ _).mpr (Or.inr (Or.inl rfl)), (hb₁ _).mpr (Or.inr (Or.inr rfl))⟩
    · exact ⟨(hb₁ _).mpr (Or.inr (Or.inr rfl)), (hb₁ _).mpr (Or.inr (Or.inl rfl))⟩
    · exact absurd rfl huv
  -- the two rhombi
  have r2 := sub_eq_sub_of_rhombus (norm_adj f1.symm) (norm_adj g.1.symm) (norm_adj f2)
    (norm_adj e12) (A.center_injective.ne (Ne.symm hb₂₁)) (A.center_injective.ne hb₁₂)
  have r3 := sub_eq_sub_of_rhombus (norm_adj f1.symm) (norm_adj g.2.symm) (norm_adj f3)
    (norm_adj e13) (A.center_injective.ne (Ne.symm hb₃₁)) (A.center_injective.ne hb₁₃)
  -- shear the triangle `a₁a₂a₃` along `a₁ - b₁`
  refine A.not_isRigid_of_shear_of_three_le (by omega) {x | x = a₁ ∨ x = a₂ ∨ x = a₃}
    (A.center a₁ - A.center b₁) (fun i j hi hj hij => ?_) (i := a₁) (k := b₁) (Or.inl rfl)
    ?_ h
  · simp only [Set.mem_ofPred_eq, not_or] at hj
    rcases hi with rfl | rfl | rfl
    · rcases (ha₁ j).mp hij with e | e | rfl
      · exact absurd e hj.2.1
      · exact absurd e hj.2.2
      · rfl
    · rcases (ha₂ j).mp hij with e | e | rfl
      · exact absurd e hj.1
      · exact absurd e hj.2.2
      · linear_combination r2
    · rcases (ha₃ j).mp hij with e | e | rfl
      · exact absurd e hj.1
      · exact absurd e hj.2.1
      · linear_combination r3
  · rintro (e | e | e)
    · exact f1.ne e.symm
    · exact hb₁₂ e
    · exact hb₁₃ e

/-- Two circles `a₁, a₂` of a triangle `a₁a₂a₃` share their third neighbour `b`: impossible
in a rigid arrangement of six circles each touching exactly three others. -/
private theorem false_of_shared [Finite ι] (h : A.IsRigid) (hn : Nat.card ι = 6)
    (h3 : ∀ i, A.TouchesExactlyThree i) {a₁ a₂ a₃ b c : ι}
    (ha₁ : ∀ k, A.contactGraph.Adj a₁ k ↔ k = a₂ ∨ k = a₃ ∨ k = b)
    (ha₂ : ∀ k, A.contactGraph.Adj a₂ k ↔ k = a₁ ∨ k = a₃ ∨ k = b)
    (ha₃ : ∀ k, A.contactGraph.Adj a₃ k ↔ k = a₁ ∨ k = a₂ ∨ k = c)
    (hb₃ : b ≠ a₃) (hc₁ : c ≠ a₁) (hc₂ : c ≠ a₂) : False := by
  have e12 : A.contactGraph.Adj a₁ a₂ := (ha₁ a₂).mpr (Or.inl rfl)
  have e13 : A.contactGraph.Adj a₁ a₃ := (ha₁ a₃).mpr (Or.inr (Or.inl rfl))
  have e23 : A.contactGraph.Adj a₂ a₃ := (ha₂ a₃).mpr (Or.inr (Or.inl rfl))
  have f1 : A.contactGraph.Adj a₁ b := (ha₁ b).mpr (Or.inr (Or.inr rfl))
  have f2 : A.contactGraph.Adj a₂ b := (ha₂ b).mpr (Or.inr (Or.inr rfl))
  have f3 : A.contactGraph.Adj a₃ c := (ha₃ c).mpr (Or.inr (Or.inr rfl))
  by_cases hbc : b = c
  · -- `{a₁, a₂, a₃, b}` is a whole component, but there are six circles
    subst hbc
    obtain ⟨w, -, -, hw⟩ := (h3 b).exists_third f1.symm f2.symm e12.ne
    have hw3 : a₃ = w := by
      rcases (hw a₃).mp f3.symm with e | e | e
      · exact absurd e e13.ne.symm
      · exact absurd e e23.ne.symm
      · exact e
    subst hw3
    obtain ⟨x, hx₁, hx₂, hx₃, hxb, -⟩ := exists_ne_five hn a₁ a₂ a₃ b b
    refine A.not_isRigid_of_isolated {y | y = a₁ ∨ y = a₂ ∨ y = a₃ ∨ y = b}
      (fun i j hi hj hij => hj ?_) (i := a₁) (k := x) (Or.inl rfl) (by simp [hx₁, hx₂, hx₃, hxb])
      h
    rcases hi with rfl | rfl | rfl | rfl
    · rcases (ha₁ j).mp hij with rfl | rfl | rfl <;> simp
    · rcases (ha₂ j).mp hij with rfl | rfl | rfl <;> simp
    · rcases (ha₃ j).mp hij with rfl | rfl | rfl <;> simp
    · rcases (hw j).mp hij with rfl | rfl | rfl <;> simp
  · -- a sixth circle `x` could only touch `b` and `c`
    obtain ⟨x, hx₁, hx₂, hx₃, hxb, hxc⟩ := exists_ne_five hn a₁ a₂ a₃ b c
    have hall := eq_of_six hn e12.ne e13.ne f1.ne (Ne.symm hc₁) (Ne.symm hx₁) e23.ne f2.ne
      (Ne.symm hc₂) (Ne.symm hx₂) (Ne.symm hb₃) f3.ne (Ne.symm hx₃) hbc (Ne.symm hxb)
      (Ne.symm hxc)
    have hmem : ∀ m, A.contactGraph.Adj x m → m = b ∨ m = c := by
      intro m hm
      rcases hall m with rfl | rfl | rfl | e | e | rfl
      · rcases (ha₁ x).mp hm.symm with e | e | e <;> contradiction
      · rcases (ha₂ x).mp hm.symm with e | e | e <;> contradiction
      · rcases (ha₃ x).mp hm.symm with e | e | e <;> contradiction
      · exact Or.inl e
      · exact Or.inr e
      · exact absurd rfl hm.ne
    obtain ⟨y₁, y₂, y₃, h12, h13, h23, hy⟩ := h3 x
    rcases hmem y₁ ((hy y₁).mpr (Or.inl rfl)) with e₁ | e₁ <;>
      rcases hmem y₂ ((hy y₂).mpr (Or.inr (Or.inl rfl))) with e₂ | e₂ <;>
      rcases hmem y₃ ((hy y₃).mpr (Or.inr (Or.inr rfl))) with e₃ | e₃
    all_goals first
      | exact h12 (e₁.trans e₂.symm)
      | exact h13 (e₁.trans e₃.symm)
      | exact h23 (e₂.trans e₃.symm)

/-- A rigid arrangement of six circles, each touching exactly three others, contains no
triangle of mutually touching circles. -/
private theorem false_of_triangle [Finite ι] (h : A.IsRigid) (hn : Nat.card ι = 6)
    (h3 : ∀ i, A.TouchesExactlyThree i) {a₁ a₂ a₃ : ι} (h12 : A.contactGraph.Adj a₁ a₂)
    (h13 : A.contactGraph.Adj a₁ a₃) (h23 : A.contactGraph.Adj a₂ a₃) : False := by
  obtain ⟨b₁, hb₁₂, hb₁₃, hb₁⟩ := (h3 a₁).exists_third h12 h13 h23.ne
  obtain ⟨b₂, hb₂₁, hb₂₃, hb₂⟩ := (h3 a₂).exists_third h12.symm h23 h13.ne
  obtain ⟨b₃, hb₃₁, hb₃₂, hb₃⟩ := (h3 a₃).exists_third h13.symm h23.symm h12.ne
  by_cases e12 : b₁ = b₂
  · subst e12
    exact false_of_shared h hn h3 hb₁ hb₂ hb₃ hb₁₃ hb₃₁ hb₃₂
  by_cases e13 : b₁ = b₃
  · subst e13
    exact false_of_shared h hn h3 (a₂ := a₃) (a₃ := a₂) (fun k => by rw [hb₁]; tauto) hb₃ hb₂
      hb₁₂ hb₂₁ hb₂₃
  by_cases e23 : b₂ = b₃
  · subst e23
    exact false_of_shared h hn h3 (a₁ := a₂) (a₂ := a₃) (a₃ := a₁)
      (fun k => by rw [hb₂]; tauto) (fun k => by rw [hb₃]; tauto) hb₁ hb₂₁ hb₁₂ hb₁₃
  exact false_of_prism h hn h3 hb₁ hb₂ hb₃ hb₁₂ hb₁₃ hb₂₁ hb₂₃ hb₃₁ hb₃₂ e12 e13 e23

/-- **No rigid core has six circles.** -/
theorem IsRigid.not_isCore_of_card_eq_six [Finite ι] (h : A.IsRigid) (hn : Nat.card ι = 6) :
    ¬ A.IsCore := by
  intro hc
  have : Nonempty ι := (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨e, he, h3e⟩ := A.exists_injective_touchesExactlyThree (h.touchesTwo (by omega)) hc
  have hsurj := (he.bijective_of_nat_card_le (by simp [hn])).2
  have h3 : ∀ i, A.TouchesExactlyThree i := fun i => by
    obtain ⟨k, rfl⟩ := hsurj i
    exact h3e k
  obtain ⟨v⟩ := ‹Nonempty ι›
  obtain ⟨p, q, r, hpq, hpr, hqr, hv⟩ := h3 v
  have hvp : A.contactGraph.Adj v p := (hv p).mpr (Or.inl rfl)
  have hvq : A.contactGraph.Adj v q := (hv q).mpr (Or.inr (Or.inl rfl))
  have hvr : A.contactGraph.Adj v r := (hv r).mpr (Or.inr (Or.inr rfl))
  by_cases e₁ : A.contactGraph.Adj p q
  · exact false_of_triangle h hn h3 hvp hvq e₁
  by_cases e₂ : A.contactGraph.Adj p r
  · exact false_of_triangle h hn h3 hvp hvr e₂
  by_cases e₃ : A.contactGraph.Adj q r
  · exact false_of_triangle h hn h3 hvq hvr e₃
  -- the neighbours `p, q, r` of `v` are pairwise apart: then `v` and a second circle `p₁`
  -- both touch all three
  obtain ⟨p₁, p₂, hp12, hp1v, hp2v, hp⟩ := (h3 p).exists_two hvp.symm
  have hpp1 : A.contactGraph.Adj p p₁ := (hp p₁).mpr (Or.inr (Or.inl rfl))
  have hpp2 : A.contactGraph.Adj p p₂ := (hp p₂).mpr (Or.inr (Or.inr rfl))
  have hall := eq_of_six hn hvp.ne hvq.ne hvr.ne (Ne.symm hp1v) (Ne.symm hp2v) hpq hpr hpp1.ne
    hpp2.ne hqr (by rintro rfl; exact e₁ hpp1) (by rintro rfl; exact e₁ hpp2)
    (by rintro rfl; exact e₂ hpp1) (by rintro rfl; exact e₂ hpp2) hp12
  have key : ∀ s, A.contactGraph.Adj v s → ¬ A.contactGraph.Adj s p →
      ¬ A.contactGraph.Adj s q → ¬ A.contactGraph.Adj s r → A.contactGraph.Adj s p₁ := by
    intro s hvs hsp hsq hsr
    obtain ⟨s₁, s₂, hs12, hs1v, hs2v, hs⟩ := (h3 s).exists_two hvs.symm
    have hs1 := (hs s₁).mpr (Or.inr (Or.inl rfl))
    have hs2 := (hs s₂).mpr (Or.inr (Or.inr rfl))
    have hmem : ∀ t, A.contactGraph.Adj s t → t ≠ v → t = p₁ ∨ t = p₂ := by
      intro t ht htv
      rcases hall t with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl htv
      · exact absurd ht hsp
      · exact absurd ht hsq
      · exact absurd ht hsr
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hmem s₁ hs1 hs1v with e | e
    · exact e ▸ hs1
    rcases hmem s₂ hs2 hs2v with e' | e'
    · exact e' ▸ hs2
    exact absurd (e.trans e'.symm) hs12
  have hqp1 := key q hvq (fun h => e₁ h.symm) (fun h => h.ne rfl) e₃
  have hrp1 := key r hvr (fun h => e₂ h.symm) (fun h => e₃ h.symm) (fun h => h.ne rfl)
  exact A.not_three_common_neighbors (Ne.symm hp1v) hpq hpr hqr hvp hvq hvr hpp1.symm
    hqp1.symm hrp1.symm

/-- **A rigid core has at least seven circles.** A rigid arrangement of at least three circles
in which no circle is removable has at least seven circles: the hull lemma gives six, and six
is impossible. -/
theorem IsRigid.seven_le_card_of_isCore [Finite ι] (h : A.IsRigid) (hc : A.IsCore)
    (h3 : 3 ≤ Nat.card ι) : 7 ≤ Nat.card ι := by
  have : Nonempty ι := (Nat.card_pos_iff.mp (by omega)).1
  have := A.six_le_card_of_isCore (h.touchesTwo h3) hc
  by_contra h7
  exact h.not_isCore_of_card_eq_six (by omega) hc

/-- Every rigid arrangement of three to six circles has a removable circle. -/
theorem IsRigid.exists_removable_of_card_le_six [Finite ι] (h : A.IsRigid)
    (h3 : 3 ≤ Nat.card ι) (h6 : Nat.card ι ≤ 6) : ∃ w, A.Removable w := by
  by_contra hno
  push Not at hno
  have := h.seven_le_card_of_isCore hno h3
  omega

end Arrangement

/-- No rigid arrangement of three to six circles is a core. -/
theorem noCoresBetween_three_six : NoCoresBetween 3 6 := fun _ _ h3 h6 h =>
  h.exists_removable_of_card_le_six (by simpa using h3) (by simpa using h6)

/-- **No cores with four to six circles**: every rigid arrangement of `4`, `5` or `6` circles
has a removable circle. -/
theorem noCoresBetween_four_six : NoCoresBetween 4 6 := fun n A h4 h6 h =>
  noCoresBetween_three_six n A (by omega) h6 h

end RigidArrangements
