import RigidArrangements.CoreBound

/-!
# Corners: elementary lemmas

This file collects the elementary plane geometry behind the classification of rigid cores of
`7` and `8` circles (`docs/cores.md`, Sections 0 and 1). Everything here holds for every
arrangement, except Lemma 5 and the angle fact F3, which assume that every circle touches two
others and that no circle is removable.

## Notation

* `rho = ρ = e^{iπ/3} = 1/2 + (√3/2) i`, the primitive sixth root of unity, with
  `ρ² = ρ - 1`, `ρ³ = -1`, `ρ⁶ = 1` and `1 - ρ + ρ² = 0`.
* `cross z w = re z * im w - im z * re w = Im (z̄ w)`, the signed area of the parallelogram
  spanned by `z` and `w`: positive when `w` points to the left of `z`. It is real-bilinear, and
  `cross z w = |z| |w| sin (arg w - arg z)`. For two points `a ≠ b`, `x ↦ cross (b - a) (x - a)`
  vanishes exactly on the line through `a` and `b`.
* A **corner** (`Arrangement.IsCorner`) is a circle that is extreme in some direction
  (`Arrangement.IsExtreme`): seen from a corner, all other centers lie in a half-open
  half-plane.

## Main results

* `LexPos.add`, `LexPos.ofReal_mul`, `not_lexPos_zero`, `LexPos.not_neg`: lexicographic
  positivity is a strict positive cone.
* `Arrangement.IsExtreme.unique` (X1): only one circle is extreme in a given direction.
* `Arrangement.isExtreme_add_int_mul_two_pi` (X2): directions are angles modulo `2π`.
* `Arrangement.IsExtreme.exists_int_abs_lt` (F3 and X2): in a core in which every circle
  touches two others, the directions in which a circle is extreme differ by less than `60°`
  modulo `360°`.
* **Lemma 1** `Arrangement.center_not_mem_segment`: the segment between two touching
  circles contains no other center.
* **Lemma 2** `Arrangement.disjoint_segment_of_adj`: segments of two contacts between four
  different circles do not meet.
* **Lemma 3** `Arrangement.ncard_neighborSet_le_six`: every circle touches at most six others.
* **Lemma 4** `Arrangement.IsExtreme.weight_eq_zero`, `Arrangement.IsCorner.weight_eq_zero`:
  a corner is an extreme point of the convex hull of the centers: in every way of writing it
  as a convex combination of centers, the other centers get weight `0`. Consequences:
  * (4a) `Arrangement.IsCorner.not_mem_openSegment`: a corner lies inside no segment between
    two other centers;
  * (4b) `Arrangement.IsCorner.mem_segment_of_cross_eq_zero`: a point of a segment between
    centers that lies on the line through two corners `a ≠ b` lies between `a` and `b`;
  * (4c) `Arrangement.IsCorner.cross_ne_zero`: no three corners are collinear.
* **Lemma 5** `Arrangement.IsCorner.exists_middle`: in a core in which every circle touches two
  others, the three neighbours of a corner `x` can be labelled `y₁, y₂, y₃` so that `y₁` and
  `y₃` lie strictly on opposite sides of the line through `x` and `y₂`.
-/

open Complex

namespace RigidArrangements

/-! ### The sixth root of unity `ρ` -/

/-- `ρ = e^{iπ/3} = 1/2 + (√3/2) i`, the primitive sixth root of unity. -/
noncomputable def rho : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

@[simp] theorem rho_re : rho.re = 1 / 2 := rfl

@[simp] theorem rho_im : rho.im = Real.sqrt 3 / 2 := rfl

private theorem sqrt_three_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- `ρ` lies in the upper half-plane; in particular it is not real. -/
theorem rho_im_pos : 0 < rho.im := by
  rw [rho_im]; positivity

theorem rho_ne_zero : rho ≠ 0 := fun h => by
  have := congrArg Complex.re h
  norm_num at this

/-- `ρ` is a unit complex number. -/
theorem normSq_rho : Complex.normSq rho = 1 := by
  rw [Complex.normSq_apply, rho_re, rho_im]
  nlinarith [sqrt_three_sq]

/-- `ρ` is a unit complex number. -/
theorem norm_rho : ‖rho‖ = 1 := by
  rw [Complex.norm_def, normSq_rho, Real.sqrt_one]

/-- `ρ² = ρ - 1`. -/
theorem rho_sq : rho ^ 2 = rho - 1 := by
  apply Complex.ext <;> simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, rho_re, rho_im] <;> nlinarith [sqrt_three_sq]

/-- `1 - ρ + ρ² = 0`. -/
theorem one_sub_rho_add_rho_sq : 1 - rho + rho ^ 2 = 0 := by
  rw [rho_sq]; ring

/-- `ρ³ = -1`. -/
theorem rho_pow_three : rho ^ 3 = -1 := by
  rw [pow_succ, rho_sq]
  linear_combination rho_sq

/-- `ρ⁶ = 1`. -/
theorem rho_pow_six : rho ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by rfl, pow_mul, rho_pow_three]
  norm_num

/-- Powers of `ρ` only depend on the exponent modulo `6`. -/
theorem rho_pow_mod_six (n : ℕ) : rho ^ (n % 6) = rho ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 6, pow_add, pow_mul, rho_pow_six, one_pow, mul_one]

/-- `ρ⁻¹ = ρ⁵`. -/
theorem rho_inv : rho⁻¹ = rho ^ 5 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', rho_pow_six]

/-- `ρ̄ = ρ⁵`. -/
theorem conj_rho : starRingEnd ℂ rho = rho ^ 5 := by
  rw [← rho_inv, Complex.inv_def, normSq_rho]
  simp

/-- The unit vector of angle `60°` is `ρ`. -/
theorem exp_pi_div_three_mul_I : Complex.exp (↑(Real.pi / 3) * Complex.I) = rho := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three, rho_re]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three, rho_im]

/-- The unit vector of angle `n · 60°` is `ρⁿ`. -/
theorem exp_nat_mul_pi_div_three_mul_I (n : ℕ) :
    Complex.exp (↑(n * Real.pi / 3) * Complex.I) = rho ^ n := by
  rw [← exp_pi_div_three_mul_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `a + b ρ = 0` with `a, b` real forces `a = b = 0`, since `ρ` is not real. -/
theorem ofReal_add_ofReal_mul_rho_eq_zero {a b : ℝ} :
    (a : ℂ) + b * rho = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, rho_re, rho_im, Complex.zero_re, Complex.zero_im] at h1 h2
    have hb : b = 0 := by
      have : b * (Real.sqrt 3 / 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by positivity)
    subst hb
    exact ⟨by linarith, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-! ### The cross product -/

/-- The cross product `cross z w = re z * im w - im z * re w = Im (z̄ w)` of two vectors of the
plane: the signed area of the parallelogram they span. It is positive when `w` points to the
left of `z`. -/
def cross (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

/-- `cross z w = Im (z̄ w)`. -/
theorem cross_eq_im (z w : ℂ) : cross z w = (starRingEnd ℂ z * w).im := by
  simp only [cross, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

@[simp] theorem cross_self (z : ℂ) : cross z z = 0 := by
  simp only [cross]; ring

/-- The cross product is antisymmetric. -/
theorem cross_swap (z w : ℂ) : cross w z = -cross z w := by
  simp only [cross]; ring

@[simp] theorem cross_zero_left (w : ℂ) : cross 0 w = 0 := by
  simp [cross]

@[simp] theorem cross_zero_right (z : ℂ) : cross z 0 = 0 := by
  simp [cross]

theorem cross_add_left (z z' w : ℂ) : cross (z + z') w = cross z w + cross z' w := by
  simp only [cross, Complex.add_re, Complex.add_im]; ring

theorem cross_add_right (z w w' : ℂ) : cross z (w + w') = cross z w + cross z w' := by
  simp only [cross, Complex.add_re, Complex.add_im]; ring

theorem cross_sub_left (z z' w : ℂ) : cross (z - z') w = cross z w - cross z' w := by
  simp only [cross, Complex.sub_re, Complex.sub_im]; ring

theorem cross_sub_right (z w w' : ℂ) : cross z (w - w') = cross z w - cross z w' := by
  simp only [cross, Complex.sub_re, Complex.sub_im]; ring

theorem cross_neg_left (z w : ℂ) : cross (-z) w = -cross z w := by
  simp only [cross, Complex.neg_re, Complex.neg_im]; ring

theorem cross_neg_right (z w : ℂ) : cross z (-w) = -cross z w := by
  simp only [cross, Complex.neg_re, Complex.neg_im]; ring

theorem cross_neg_neg (z w : ℂ) : cross (-z) (-w) = cross z w := by
  rw [cross_neg_left, cross_neg_right, neg_neg]

theorem cross_ofReal_mul_left (t : ℝ) (z w : ℂ) : cross (↑t * z) w = t * cross z w := by
  simp only [cross, Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

theorem cross_ofReal_mul_right (t : ℝ) (z w : ℂ) : cross z (↑t * w) = t * cross z w := by
  simp only [cross, Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

theorem cross_smul_left (t : ℝ) (z w : ℂ) : cross (t • z) w = t * cross z w := by
  rw [Complex.real_smul, cross_ofReal_mul_left]

theorem cross_smul_right (t : ℝ) (z w : ℂ) : cross z (t • w) = t * cross z w := by
  rw [Complex.real_smul, cross_ofReal_mul_right]

/-- A rotation-and-scaling `z ↦ u z` multiplies cross products by `|u|²`. -/
theorem cross_mul_mul (u z w : ℂ) : cross (u * z) (u * w) = Complex.normSq u * cross z w := by
  simp only [cross, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring

/-- Rotations preserve cross products. -/
theorem cross_mul_mul_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (z w : ℂ) :
    cross (u * z) (u * w) = cross z w := by
  rw [cross_mul_mul, Complex.normSq_eq_norm_sq, hu, one_pow, one_mul]

/-- A rotation-and-scaling `z ↦ z u` multiplies cross products by `|u|²`. -/
theorem cross_mul_right_mul_right (u z w : ℂ) :
    cross (z * u) (w * u) = Complex.normSq u * cross z w := by
  rw [mul_comm z, mul_comm w, cross_mul_mul]

/-- The cross product with a real number `t` is `t` times the imaginary part. -/
theorem cross_ofReal_left (t : ℝ) (w : ℂ) : cross t w = t * w.im := by
  simp [cross]

/-- `cross z w = |z| |w| sin (arg w - arg z)`. -/
theorem cross_eq_norm_mul_norm_mul_sin (z w : ℂ) :
    cross z w = ‖z‖ * ‖w‖ * Real.sin (arg w - arg z) := by
  rw [Real.sin_sub, cross, ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
    ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  ring

/-- Along a segment, `x ↦ cross z (x - c)` is affine. -/
theorem cross_add_smul_sub (z x y c : ℂ) {a b : ℝ} (hab : a + b = 1) :
    cross z (a • x + b • y - c) = a * cross z (x - c) + b * cross z (y - c) := by
  simp only [cross, Complex.real_smul, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  linear_combination (z.re * c.im - z.im * c.re) * hab

/-- For `z ≠ 0`, `cross z w = 0` exactly when `w` is a real multiple of `z`. -/
theorem cross_eq_zero_iff {z w : ℂ} (hz : z ≠ 0) : cross z w = 0 ↔ ∃ t : ℝ, w = t * z := by
  constructor
  · intro h
    have hN : Complex.normSq z ≠ 0 := Complex.normSq_eq_zero.not.mpr hz
    rw [Complex.normSq_apply] at hN
    refine ⟨(z.re * w.re + z.im * w.im) / (z.re * z.re + z.im * z.im), ?_⟩
    simp only [cross] at h
    apply Complex.ext <;> simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul] <;>
      rw [div_mul_eq_mul_div, eq_div_iff hN]
    · linear_combination -z.im * h
    · linear_combination z.re * h
  · rintro ⟨t, rfl⟩
    rw [cross_ofReal_mul_right, cross_self, mul_zero]

/-- If `x ↦ cross z (x - c)` is positive at `x` and negative at `y`, it vanishes at a point of
the open segment between `x` and `y`. -/
theorem exists_mem_openSegment_cross_eq_zero {z c x y : ℂ} (hx : 0 < cross z (x - c))
    (hy : cross z (y - c) < 0) : ∃ q ∈ openSegment ℝ x y, cross z (q - c) = 0 := by
  set fx := cross z (x - c)
  set fy := cross z (y - c)
  have hd : 0 < fx - fy := by linarith
  have hab : -fy / (fx - fy) + fx / (fx - fy) = 1 := by field_simp; ring
  refine ⟨(-fy / (fx - fy)) • x + (fx / (fx - fy)) • y,
    ⟨_, _, div_pos (by linarith) hd, div_pos hx hd, hab, rfl⟩, ?_⟩
  rw [cross_add_smul_sub z x y c hab]
  field_simp
  ring

/-- If `x ↦ cross z (x - c)` has opposite signs at `x` and `y`, it vanishes at a point of the
open segment between `x` and `y`. -/
theorem exists_mem_openSegment_cross_eq_zero_of_mul_neg {z c x y : ℂ}
    (h : cross z (x - c) * cross z (y - c) < 0) :
    ∃ q ∈ openSegment ℝ x y, cross z (q - c) = 0 := by
  rcases mul_neg_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact exists_mem_openSegment_cross_eq_zero hx hy
  · obtain ⟨q, hq, hq0⟩ := exists_mem_openSegment_cross_eq_zero hy hx
    exact ⟨q, openSegment_symm ℝ x y ▸ hq, hq0⟩

/-! ### Lexicographic positivity -/

/-- **(L)** The sum of two lexicographically positive numbers is lexicographically positive. -/
theorem LexPos.add {z w : ℂ} (hz : LexPos z) (hw : LexPos w) : LexPos (z + w) := by
  unfold LexPos at *
  simp only [Complex.add_re, Complex.add_im]
  rcases hz with hz | ⟨hz1, hz2⟩ <;> rcases hw with hw | ⟨hw1, hw2⟩
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- **(L)** A positive multiple of a lexicographically positive number is lexicographically
positive. -/
theorem LexPos.ofReal_mul {z : ℂ} {t : ℝ} (hz : LexPos z) (ht : 0 < t) : LexPos (↑t * z) := by
  unfold LexPos at *
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  rcases hz with hz | ⟨hz1, hz2⟩
  · exact Or.inl (mul_pos ht hz)
  · exact Or.inr ⟨by rw [hz1, mul_zero], mul_pos ht hz2⟩

/-- **(L)** `0` is not lexicographically positive. -/
theorem not_lexPos_zero : ¬ LexPos 0 := by
  simp [LexPos]

/-- A lexicographically positive number is not `0`. -/
theorem LexPos.ne_zero {z : ℂ} (h : LexPos z) : z ≠ 0 := by
  rintro rfl
  exact not_lexPos_zero h

/-- **(L)** `z` and `-z` are not both lexicographically positive. -/
theorem LexPos.not_neg {z : ℂ} (h : LexPos z) : ¬ LexPos (-z) := by
  unfold LexPos at *
  simp only [Complex.neg_re, Complex.neg_im]
  rcases h with h | ⟨h1, h2⟩
  · rintro (h' | ⟨h', -⟩) <;> linarith
  · rintro (h' | ⟨-, h'⟩) <;> linarith

/-- Rotating a nonzero vector `z` by `-δ` gives a lexicographically positive vector exactly
when the angle `arg z - δ` points into the lexicographically positive half-plane: its cosine is
positive, or zero with positive sine. (This generalizes `lexPos_mul_exp` from vectors of
length `2` to all nonzero vectors, and gives both directions.) -/
theorem lexPos_mul_exp_iff {z : ℂ} (hz : z ≠ 0) (δ : ℝ) :
    LexPos (z * exp (↑(-δ) * I)) ↔
      0 < Real.cos (arg z - δ) ∨ (Real.cos (arg z - δ) = 0 ∧ 0 < Real.sin (arg z - δ)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have e : z * exp (↑(-δ) * I) = ‖z‖ * exp (↑(arg z - δ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, LexPos, Complex.re_ofReal_mul, Complex.im_ofReal_mul, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (pos_of_mul_pos_right h hn.le)
    · exact Or.inr ⟨(mul_eq_zero.mp h1).resolve_left hn.ne', pos_of_mul_pos_right h2 hn.le⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (mul_pos hn h)
    · exact Or.inr ⟨by rw [h1, mul_zero], mul_pos hn h2⟩

namespace Arrangement

variable {ι : Type*} {A : Arrangement ι}

/-! ### Corners -/

variable (A) in
/-- A *corner*: a circle that is extreme in some direction (`Arrangement.IsExtreme`). Seen from
a corner, all other centers lie in a half-open half-plane. -/
def IsCorner (i : ι) : Prop :=
  ∃ θ, A.IsExtreme θ i

/-- A circle extreme in some direction is a corner. -/
theorem IsExtreme.isCorner {θ : ℝ} {i : ι} (h : A.IsExtreme θ i) : A.IsCorner i :=
  ⟨θ, h⟩

/-- **X1.** At most one circle is extreme in a given direction. -/
theorem IsExtreme.unique {θ : ℝ} {i j : ι} (hi : A.IsExtreme θ i) (hj : A.IsExtreme θ j) :
    i = j := by
  by_contra hij
  have h := hj i hij
  rw [show (A.center j - A.center i) * exp (↑(-θ) * I) =
    -((A.center i - A.center j) * exp (↑(-θ) * I)) by ring] at h
  exact (hi j (Ne.symm hij)).not_neg h

variable (A) in
/-- **X2.** Directions are angles modulo `2π`. -/
theorem isExtreme_add_int_mul_two_pi {θ : ℝ} {i : ι} (n : ℤ) :
    A.IsExtreme (θ + n * (2 * Real.pi)) i ↔ A.IsExtreme θ i := by
  have e : exp (↑(-(θ + n * (2 * Real.pi))) * I) = exp (↑(-θ) * I) := by
    rw [show (↑(-(θ + n * (2 * Real.pi))) * I : ℂ) = ↑(-θ) * I - n * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  simp only [IsExtreme, e]

variable (A) in
/-- **X1.** In a finite nonempty arrangement, exactly one circle is extreme in each
direction. -/
theorem existsUnique_isExtreme [Finite ι] [Nonempty ι] (θ : ℝ) : ∃! i, A.IsExtreme θ i := by
  obtain ⟨i, hi⟩ := A.exists_isExtreme θ
  exact ⟨i, hi, fun j hj => hj.unique hi⟩

/-- In a core in which every circle touches two others, a corner touches exactly three
others. -/
theorem IsCorner.touchesExactlyThree {i : ι} (hT : A.TouchesTwo) (hc : A.IsCore)
    (hi : A.IsCorner i) : A.TouchesExactlyThree i := by
  obtain ⟨θ, h⟩ := hi
  exact h.touchesExactlyThree hT hc

/-- **F3 and X2.** In a core in which every circle touches two others, if a circle is extreme in
the directions `α` and `β`, then `α - β` is less than `60°` away from a multiple of `360°`. -/
theorem IsExtreme.exists_int_abs_lt (hT : A.TouchesTwo) (hc : A.IsCore) {α β : ℝ} {i : ι}
    (hα : A.IsExtreme α i) (hβ : A.IsExtreme β i) :
    ∃ n : ℤ, |α - β - n * (2 * Real.pi)| < Real.pi / 3 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hγ := toIocMod_add_toIocDiv_zsmul hp (-Real.pi) (α - β)
  have hmem := toIocMod_mem_Ioc hp (-Real.pi) (α - β)
  set γ := toIocMod hp (-Real.pi) (α - β)
  set n := toIocDiv hp (-Real.pi) (α - β)
  rw [zsmul_eq_mul] at hγ
  refine ⟨n, ?_⟩
  rw [show α - β - n * (2 * Real.pi) = γ by linarith, abs_lt]
  constructor
  · by_contra hle
    push Not at hle
    refine hα.not_isExtreme_add hT hc (δ := -γ) (by linarith) (by linarith [hmem.1]) ?_
    rw [show α + -γ = β + n * (2 * Real.pi) by linarith, A.isExtreme_add_int_mul_two_pi]
    exact hβ
  · by_contra hle
    push Not at hle
    refine hβ.not_isExtreme_add hT hc (δ := γ) hle (by linarith [hmem.2]) ?_
    rw [show β + γ = α + ((-n : ℤ) : ℝ) * (2 * Real.pi) by push_cast; linarith,
      A.isExtreme_add_int_mul_two_pi]
    exact hα

/-! ### Lemmas 1–3: contacts -/

/-- **Lemma 1.** The segment between the centers of two touching circles contains no other
center. -/
theorem center_not_mem_segment {i j k : ι} (hij : A.contactGraph.Adj i j) (hki : k ≠ i)
    (hkj : k ≠ j) : A.center k ∉ segment ℝ (A.center i) (A.center j) := by
  intro h
  have h0 := dist_add_dist_of_mem_segment h
  have h1 : dist (A.center i) (A.center j) = 2 := hij.2
  have h2 := A.nonoverlap hki.symm
  have h3 := A.nonoverlap hkj
  linarith

/-- On the segment from `x` to `y`, the point `a • x + b • y` is at distance `b ‖y - x‖` from
`x`. -/
private theorem norm_add_smul_sub_left {x y : ℂ} {a b : ℝ} (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • x + b • y - x‖ = b * ‖y - x‖ := by
  obtain rfl : a = 1 - b := by linarith
  rw [show (1 - b) • x + b • y - x = b • (y - x) by
    simp only [sub_smul, one_smul, smul_sub]; abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]

/-- **Lemma 2.** The segments of two contacts between four different circles do not meet. -/
theorem disjoint_segment_of_adj {i j k l : ι} (hij : A.contactGraph.Adj i j)
    (hkl : A.contactGraph.Adj k l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Disjoint (segment ℝ (A.center i) (A.center j)) (segment ℝ (A.center k) (A.center l)) := by
  rw [Set.disjoint_left]
  rintro q ⟨a, b, ha, hb, hab, rfl⟩ ⟨c, d, hc, hd, hcd, hq⟩
  have nij : ‖A.center j - A.center i‖ = 2 := by rw [← dist_eq_norm, dist_comm]; exact hij.2
  have nkl : ‖A.center l - A.center k‖ = 2 := by rw [← dist_eq_norm, dist_comm]; exact hkl.2
  have nji : ‖A.center i - A.center j‖ = 2 := by rw [← dist_eq_norm]; exact hij.2
  have nlk : ‖A.center k - A.center l‖ = 2 := by rw [← dist_eq_norm]; exact hkl.2
  set q := a • A.center i + b • A.center j
  -- the distances from `q` to the four centers
  have di : dist q (A.center i) = b * 2 := by
    rw [dist_eq_norm, norm_add_smul_sub_left hb hab, nij]
  have dj : dist q (A.center j) = a * 2 := by
    rw [dist_eq_norm, show q = b • A.center j + a • A.center i from add_comm _ _,
      norm_add_smul_sub_left ha (by linarith), nji]
  have dk : dist q (A.center k) = d * 2 := by
    rw [dist_eq_norm, ← hq, norm_add_smul_sub_left hd hcd, nkl]
  have dl : dist q (A.center l) = c * 2 := by
    rw [dist_eq_norm, ← hq, show c • A.center k + d • A.center l = d • A.center l + c • A.center k
      from add_comm _ _, norm_add_smul_sub_left hc (by linarith), nlk]
  -- triangle inequalities through `q` force `a = b = c = d = 1/2`
  have t1 := dist_triangle_left (A.center i) (A.center k) q
  have t2 := dist_triangle_left (A.center j) (A.center l) q
  have t3 := dist_triangle_left (A.center i) (A.center l) q
  have t4 := dist_triangle_left (A.center j) (A.center k) q
  have s1 := A.nonoverlap hik
  have s2 := A.nonoverlap hjl
  have s3 := A.nonoverlap hil
  have s4 := A.nonoverlap hjk
  have hb2 : b = 1 / 2 := by linarith
  have hd2 : d = 1 / 2 := by linarith
  -- then `q` is the midpoint of both segments, and the parallelogram law fails
  set u := A.center i - q
  set w := A.center k - q
  have nu : ‖u‖ = 1 := by rw [← dist_eq_norm, dist_comm, di, hb2]; norm_num
  have nw : ‖w‖ = 1 := by rw [← dist_eq_norm, dist_comm, dk, hd2]; norm_num
  have e1 : ‖u - w‖ = dist (A.center i) (A.center k) := by
    rw [dist_eq_norm]; congr 1; simp only [u, w]; ring
  have e2 : ‖u + w‖ = dist (A.center i) (A.center l) := by
    rw [dist_eq_norm]
    congr 1
    obtain rfl : c = 1 / 2 := by linarith
    subst hd2
    simp only [u, w]
    rw [← hq, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have := parallelogram_law_with_norm ℝ u w
  rw [nu, nw, e1, e2] at this
  nlinarith

/-- **Lemma 3.** Every circle touches at most six others. Seen from the circle, its
neighbours are pairwise at least `60°` apart, so no two of them lie in the same one of the six
arcs `((m - 1) · 60°, m · 60°]`, `m = -2, …, 3`. -/
theorem ncard_neighborSet_le_six (A : Arrangement ι) (i : ι) :
    (A.contactGraph.neighborSet i).ncard ≤ 6 := by
  have hπ := Real.pi_pos
  have hπ3 : 0 < Real.pi / 3 := by positivity
  set f : ι → ℤ := fun y => ⌈arg (A.center y - A.center i) / (Real.pi / 3)⌉
  have hmaps : ∀ y ∈ A.contactGraph.neighborSet i, f y ∈ Set.Icc (-2 : ℤ) 3 := by
    intro y _
    have h1 := Complex.neg_pi_lt_arg (A.center y - A.center i)
    have h2 := Complex.arg_le_pi (A.center y - A.center i)
    constructor
    · have : ((-3 : ℤ) : ℝ) < arg (A.center y - A.center i) / (Real.pi / 3) := by
        rw [lt_div_iff₀ hπ3]; push_cast; linarith
      have := Int.lt_ceil.mpr this
      simp only [f]
      omega
    · exact Int.ceil_le.mpr (by rw [div_le_iff₀ hπ3]; push_cast; linarith)
  have hinj : Set.InjOn f (A.contactGraph.neighborSet i) := by
    intro y hy y' hy' hf
    by_contra hne
    have hy2 : ‖A.center y - A.center i‖ = 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy.2
    have hy2' : ‖A.center y' - A.center i‖ = 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'.2
    have hsep := pi_div_three_le_abs_arg_sub hy2 hy2'
      (by rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact A.nonoverlap hne)
    set x := arg (A.center y - A.center i) / (Real.pi / 3)
    set x' := arg (A.center y' - A.center i) / (Real.pi / 3)
    have ex : arg (A.center y - A.center i) = x * (Real.pi / 3) := by
      simp only [x]; field_simp
    have ex' : arg (A.center y' - A.center i) = x' * (Real.pi / 3) := by
      simp only [x']; field_simp
    have c1 := Int.le_ceil x
    have c2 := Int.ceil_lt_add_one x
    have c3 := Int.le_ceil x'
    have c4 := Int.ceil_lt_add_one x'
    have hf' : (⌈x⌉ : ℝ) = ⌈x'⌉ := by exact_mod_cast hf
    rw [ex, ex', ← sub_mul, abs_mul, abs_of_pos hπ3] at hsep
    have : |x - x'| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    nlinarith
  calc (A.contactGraph.neighborSet i).ncard ≤ (Set.Icc (-2 : ℤ) 3).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj (Set.finite_Icc _ _)
    _ = 6 := by
        rw [← Finset.coe_Icc, Set.ncard_coe_finset]
        rfl

/-! ### Lemma 4: corners are extreme points -/

/-- **Lemma 4.** A circle `v` that is extreme in some direction is an extreme point of the
convex hull of the centers: if its center is a convex combination `∑ₜ μₜ p_{c t}` of centers,
every center other than `v` gets weight `0`. (Rotated by `-θ`, every vector from another center
to `v` is lexicographically positive, and a positive combination of such vectors is not `0`.) -/
theorem IsExtreme.weight_eq_zero {θ : ℝ} {v : ι} (hv : A.IsExtreme θ v) {σ : Type*}
    (s : Finset σ) (c : σ → ι) (μ : σ → ℝ) (hμ : ∀ t ∈ s, 0 ≤ μ t) (h1 : ∑ t ∈ s, μ t = 1)
    (hs : ∑ t ∈ s, (μ t : ℂ) * A.center (c t) = A.center v) {t : σ} (ht : t ∈ s)
    (hct : c t ≠ v) : μ t = 0 := by
  set w : σ → ℂ := fun t => (A.center v - A.center (c t)) * exp (↑(-θ) * I)
  have hsum : ∑ t ∈ s, (μ t : ℂ) * w t = 0 := by
    have : ∑ t ∈ s, (μ t : ℂ) * w t = ((∑ t ∈ s, (μ t : ℂ)) * A.center v -
        ∑ t ∈ s, (μ t : ℂ) * A.center (c t)) * exp (↑(-θ) * I) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
      exact Finset.sum_congr rfl fun t _ => by simp only [w]; ring
    rw [this, ← Complex.ofReal_sum, h1, hs, Complex.ofReal_one, one_mul, sub_self, zero_mul]
  have hw : ∀ t ∈ s, c t ≠ v → LexPos (w t) := fun t _ h => hv (c t) h
  have hw0 : ∀ t ∈ s, c t = v → w t = 0 := fun t _ h => by simp [w, h]
  -- the real parts: all terms are nonnegative, so all vanish
  have hre : ∀ t ∈ s, 0 ≤ μ t * (w t).re := by
    intro t' ht'
    refine mul_nonneg (hμ t' ht') ?_
    by_cases h : c t' = v
    · rw [hw0 t' ht' h, Complex.zero_re]
    · rcases hw t' ht' h with h | ⟨h, -⟩ <;> linarith
  have hre0 : ∀ t ∈ s, μ t * (w t).re = 0 := by
    rw [← Finset.sum_eq_zero_iff_of_nonneg hre]
    have := congrArg Complex.re hsum
    simpa only [Complex.re_sum, Complex.re_ofReal_mul, Complex.zero_re] using this
  -- then the imaginary parts: all terms are nonnegative, so all vanish
  have him : ∀ t ∈ s, 0 ≤ μ t * (w t).im := by
    intro t' ht'
    rcases (hμ t' ht').eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
    · have hr : (w t').re = 0 := (mul_eq_zero.mp (hre0 t' ht')).resolve_left hpos.ne'
      by_cases h : c t' = v
      · rw [hw0 t' ht' h, Complex.zero_im, mul_zero]
      · rcases hw t' ht' h with h' | ⟨-, h'⟩
        · linarith
        · exact (mul_pos hpos h').le
  have him0 : ∀ t ∈ s, μ t * (w t).im = 0 := by
    rw [← Finset.sum_eq_zero_iff_of_nonneg him]
    have := congrArg Complex.im hsum
    simpa only [Complex.im_sum, Complex.im_ofReal_mul, Complex.zero_im] using this
  by_contra hne
  have hr := (mul_eq_zero.mp (hre0 t ht)).resolve_left hne
  have hi := (mul_eq_zero.mp (him0 t ht)).resolve_left hne
  exact (hw t ht hct).ne_zero (Complex.ext hr hi)

/-- **Lemma 4** for corners: if the center of a corner `v` is a convex combination of centers,
every center other than `v` gets weight `0`. -/
theorem IsCorner.weight_eq_zero {v : ι} (hv : A.IsCorner v) {σ : Type*} (s : Finset σ)
    (c : σ → ι) (μ : σ → ℝ) (hμ : ∀ t ∈ s, 0 ≤ μ t) (h1 : ∑ t ∈ s, μ t = 1)
    (hs : ∑ t ∈ s, (μ t : ℂ) * A.center (c t) = A.center v) {t : σ} (ht : t ∈ s)
    (hct : c t ≠ v) : μ t = 0 := by
  obtain ⟨θ, h⟩ := hv
  exact h.weight_eq_zero s c μ hμ h1 hs ht hct

/-- **Lemma 4**, three-point form: if the center of a corner `v` is the convex combination
`α p_x + β p_y + γ p_z` of three centers (not necessarily different) and `x ≠ v`, then
`α = 0`. -/
theorem IsCorner.eq_zero_of_eq_add_add {v x y z : ι} (hv : A.IsCorner v) {α β γ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (h1 : α + β + γ = 1)
    (h : A.center v = α * A.center x + β * A.center y + γ * A.center z) (hx : x ≠ v) :
    α = 0 := by
  refine hv.weight_eq_zero Finset.univ ![x, y, z] ![α, β, γ] (fun t _ => ?_) ?_ ?_
    (Finset.mem_univ 0) hx
  · fin_cases t <;> simpa
  · simpa [Fin.sum_univ_three, add_assoc] using h1
  · simpa [Fin.sum_univ_three, add_assoc] using h.symm

/-- **(4a)** A corner `v` does not lie inside a segment between two centers, one of which is
not `v`. (The other one is then not `v` either.) -/
theorem IsCorner.not_mem_openSegment {v c c' : ι} (hv : A.IsCorner v) (hc : c ≠ v) :
    A.center v ∉ openSegment ℝ (A.center c) (A.center c') := by
  rintro ⟨a, b, ha, hb, hab, h⟩
  have := hv.eq_zero_of_eq_add_add (y := c') (z := v) (γ := 0) ha.le hb.le le_rfl (by linarith)
    (by rw [← h, Complex.real_smul, Complex.real_smul]; push_cast; ring) hc
  linarith

/-- **(4b)** Let `a ≠ b` be corners. A point of a segment between two centers that lies on the
line through `a` and `b` lies on the segment between `a` and `b`. -/
theorem IsCorner.mem_segment_of_cross_eq_zero {a b c c' : ι} (ha : A.IsCorner a)
    (hb : A.IsCorner b) (hab : a ≠ b) {q : ℂ} (hq : q ∈ segment ℝ (A.center c) (A.center c'))
    (hl : cross (A.center b - A.center a) (q - A.center a) = 0) :
    q ∈ segment ℝ (A.center a) (A.center b) := by
  have hne : A.center b - A.center a ≠ 0 := sub_ne_zero.mpr (A.center_injective.ne (Ne.symm hab))
  obtain ⟨t, ht⟩ := (cross_eq_zero_iff hne).mp hl
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hq
  simp only [Complex.real_smul] at ht ⊢
  rcases lt_or_ge 1 t with h1 | h1
  · -- `b` would be a convex combination of `a`, `c`, `c'` with positive weight on `a`
    exfalso
    have ht0 : t ≠ 0 := by positivity
    have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have := hb.eq_zero_of_eq_add_add (x := a) (y := c) (z := c') (α := 1 - 1 / t) (β := α / t)
      (γ := β / t) (by rw [sub_nonneg, div_le_one (by linarith)]; exact h1.le) (by positivity)
      (by positivity) (by field_simp; linarith) (by
        push_cast
        field_simp
        linear_combination -ht) hab
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq ht0] at this
    linarith
  rcases lt_or_ge t 0 with h0 | h0
  · -- `a` would be a convex combination of `b`, `c`, `c'` with positive weight on `b`
    exfalso
    have ht1 : (1 - t) ≠ 0 := by linarith
    have ht1' : (1 - t : ℂ) ≠ 0 := by exact_mod_cast ht1
    have := ha.eq_zero_of_eq_add_add (x := b) (y := c) (z := c') (α := -t / (1 - t))
      (β := α / (1 - t)) (γ := β / (1 - t)) (div_nonneg (by linarith) (by linarith))
      (div_nonneg hα (by linarith)) (div_nonneg hβ (by linarith))
      (by field_simp; linarith) (by
        push_cast
        field_simp
        linear_combination -ht) (Ne.symm hab)
    rw [div_eq_zero_iff] at this
    rcases this with h | h <;> linarith
  · refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    linear_combination -ht

/-- **(4c)** No three different corners are collinear. -/
theorem IsCorner.cross_ne_zero {a b c : ι} (ha : A.IsCorner a) (hb : A.IsCorner b)
    (hc : A.IsCorner c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cross (A.center b - A.center a) (A.center c - A.center a) ≠ 0 := by
  intro h
  have hseg := ha.mem_segment_of_cross_eq_zero hb hab (c := c) (c' := c)
    (left_mem_segment ℝ _ _) h
  exact hc.not_mem_openSegment hac
    (mem_openSegment_of_ne_left_right (A.center_injective.ne hac) (A.center_injective.ne hbc) hseg)

/-! ### Lemma 5: the middle neighbour of a corner -/

/-- Seen from a circle `x` extreme in direction `θ`, let `j` and `k` be two neighbours, with
directions measured relative to `θ + 180°`. If `j` comes before `k`, then `j` lies to the right
of the line from `x` to `k`. -/
private theorem IsExtreme.cross_neg_of_arg_lt {θ : ℝ} {x j k : ι} (he : A.IsExtreme θ x)
    (hj : A.contactGraph.Adj x j) (hk : A.contactGraph.Adj x k)
    (hlt : arg ((A.center x - A.center j) * exp (↑(-θ) * I)) <
      arg ((A.center x - A.center k) * exp (↑(-θ) * I))) :
    cross (A.center k - A.center x) (A.center j - A.center x) < 0 := by
  obtain ⟨hj1, hj2, -⟩ := he.arg_mem hj
  obtain ⟨hk1, -, hk3⟩ := he.arg_mem hk
  have e : cross (A.center k - A.center x) (A.center j - A.center x) =
      cross ((A.center x - A.center k) * exp (↑(-θ) * I))
        ((A.center x - A.center j) * exp (↑(-θ) * I)) := by
    rw [cross_mul_right_mul_right, Complex.normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow,
      one_mul, ← cross_neg_neg, neg_sub, neg_sub]
  rw [e, cross_eq_norm_mul_norm_mul_sin, hj1, hk1]
  have := Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hlt) (by linarith)
  linarith

/-- **Lemma 5.** In a core in which every circle touches two others, the three neighbours of a
corner `x` can be labelled `y₁, y₂, y₃` so that `y₁` and `y₃` lie strictly on opposite sides of
the line through `x` and `y₂`: `y₁` on the right, `y₃` on the left. -/
theorem IsCorner.exists_middle (hT : A.TouchesTwo) (hc : A.IsCore) {x : ι} (hx : A.IsCorner x) :
    ∃ y₁ y₂ y₃, y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧
      (∀ k, A.contactGraph.Adj x k ↔ k = y₁ ∨ k = y₂ ∨ k = y₃) ∧
      cross (A.center y₂ - A.center x) (A.center y₁ - A.center x) < 0 ∧
      0 < cross (A.center y₂ - A.center x) (A.center y₃ - A.center x) := by
  obtain ⟨θ, he⟩ := hx
  obtain ⟨a, b, c, hab, hac, hbc, hk⟩ := he.touchesExactlyThree hT hc
  set φ : ι → ℝ := fun m => arg ((A.center x - A.center m) * exp (↑(-θ) * I))
  have adj : ∀ m, m = a ∨ m = b ∨ m = c → A.contactGraph.Adj x m := fun m hm => (hk m).mpr hm
  have ha := adj a (Or.inl rfl)
  have hb := adj b (Or.inr (Or.inl rfl))
  have hc' := adj c (Or.inr (Or.inr rfl))
  have hπ := Real.pi_pos
  have sep : ∀ m m', A.contactGraph.Adj x m → A.contactGraph.Adj x m' → m ≠ m' → φ m ≠ φ m' :=
    fun m m' hm hm' hmm' e => by
      have := he.pi_div_three_le hm hm' hmm'
      simp only [φ] at e
      rw [e, sub_self, abs_zero] at this
      linarith
  have key : ∀ y₁ y₂ y₃, y₁ ≠ y₂ → y₁ ≠ y₃ → y₂ ≠ y₃ →
      (∀ k, A.contactGraph.Adj x k ↔ k = y₁ ∨ k = y₂ ∨ k = y₃) → φ y₁ < φ y₂ → φ y₂ < φ y₃ →
      ∃ y₁ y₂ y₃, y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧
        (∀ k, A.contactGraph.Adj x k ↔ k = y₁ ∨ k = y₂ ∨ k = y₃) ∧
        cross (A.center y₂ - A.center x) (A.center y₁ - A.center x) < 0 ∧
        0 < cross (A.center y₂ - A.center x) (A.center y₃ - A.center x) := by
    intro y₁ y₂ y₃ h12 h13 h23 hy l12 l23
    have a1 := (hy y₁).mpr (Or.inl rfl)
    have a2 := (hy y₂).mpr (Or.inr (Or.inl rfl))
    have a3 := (hy y₃).mpr (Or.inr (Or.inr rfl))
    refine ⟨y₁, y₂, y₃, h12, h13, h23, hy, he.cross_neg_of_arg_lt a1 a2 l12, ?_⟩
    rw [cross_swap]
    exact neg_pos.mpr (he.cross_neg_of_arg_lt a2 a3 l23)
  rcases (sep a b ha hb hab).lt_or_gt with h1 | h1 <;>
    rcases (sep a c ha hc' hac).lt_or_gt with h2 | h2 <;>
    rcases (sep b c hb hc' hbc).lt_or_gt with h3 | h3
  · exact key a b c hab hac hbc hk h1 h3
  · exact key a c b hac hab (Ne.symm hbc) (fun k => by rw [hk]; tauto) h2 h3
  · exact absurd (h1.trans h3) h2.not_gt
  · exact key c a b (Ne.symm hac) (Ne.symm hbc) hab (fun k => by rw [hk]; tauto) h2 h1
  · exact key b a c (Ne.symm hab) hbc hac (fun k => by rw [hk]; tauto) h1 h2
  · exact absurd (h3.trans h1) h2.not_gt
  · exact key b c a hbc (Ne.symm hab) (Ne.symm hac) (fun k => by rw [hk]; tauto) h3 h2
  · exact key c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) (fun k => by rw [hk]; tauto) h3 h1

end Arrangement

end RigidArrangements
