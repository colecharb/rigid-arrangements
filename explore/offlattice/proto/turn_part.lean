
/-! ===================== off-lattice by the turn (D = 3k²) ===================== -/

namespace RigidArrangements

/-- When `D = 3k²`, the turn lies in `ℚ(ρ)`: `α = eis (hbNum) / hbDen`. -/
def hbNum (u v : ℤ × ℤ) (σ k : ℤ) : ℤ × ℤ :=
  emul (eNorm u + eNorm v - 1 - σ * k, 2 * σ * k) (emul u (econj v))

def hbDen (u v : ℤ × ℤ) : ℤ := 2 * eNorm u * eNorm v

theorem eis_sub (a b : ℤ × ℤ) : eis (a - b) = eis a - eis b := by
  simp only [eis, Prod.fst_sub, Prod.snd_sub]; push_cast; ring

theorem eis_injective : Function.Injective eis := by
  intro a b h
  by_contra hab
  exact eis_ne_zero (sub_ne_zero.2 hab) (by rw [eis_sub, h, sub_self])

theorem hbAlpha_eq_of_sq {u v : ℤ × ℤ} {σ k : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hk : 0 ≤ k)
    (hDk : hbD u v = 3 * k ^ 2) :
    hbAlpha u v σ = eis (hbNum u v σ k) / (hbDen u v : ℂ) := by
  have hNu := eNorm_pos hu
  have hNv := eNorm_pos hv
  have hsq : Real.sqrt (hbD u v) = k * Real.sqrt 3 := by
    rw [hDk]; push_cast
    rw [show (3 : ℝ) * k ^ 2 = k ^ 2 * 3 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by exact_mod_cast hk)]
  have hW : hbW u v σ = eis (eNorm u + eNorm v - 1 - σ * k, 2 * σ * k) / (2 * eNorm u : ℂ) := by
    apply Complex.ext
    · simp only [hbW, Complex.div_re, eis_re]
      simp [Complex.normSq_apply]
      field_simp
      ring
    · simp only [hbW, hsq, Complex.div_im, eis_im]
      simp [Complex.normSq_apply]
      field_simp
      ring
  simp only [hbAlpha, hW, hbNum, hbDen, eis_mul, eis_econj]
  push_cast
  field_simp

/-- `eis` of a unit is a power of `ρ`, and conversely. -/
theorem exists_unit_eis_eq_rho_pow (m : ℕ) : ∃ r ∈ latticeUnits, eis r = rho ^ m := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  rw [← rho_pow_mod_six]
  have : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 6)
  · exact ⟨(1, 0), by decide, by simp [eis]⟩
  · exact ⟨(0, 1), by decide, by simp [eis]⟩
  · exact ⟨(-1, 1), by decide, by simp [eis, rho_sq]; ring⟩
  · exact ⟨(-1, 0), by decide, by simp [eis, rho_pow_three]⟩
  · exact ⟨(0, -1), by decide, by simp [eis, h4]⟩
  · exact ⟨(1, -1), by decide, by simp [eis, h5]; ring⟩

/-- **The turn is not a lattice rotation** when its `ℚ(ρ)` form misses the six units. -/
theorem hbAlpha_pow_six_ne_one {u v : ℤ × ℤ} {σ k : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hk : 0 ≤ k)
    (hDk : hbD u v = 3 * k ^ 2)
    (hnum : ∀ r ∈ latticeUnits, hbNum u v σ k ≠ (hbDen u v * r.1, hbDen u v * r.2)) :
    hbAlpha u v σ ^ 6 ≠ 1 := by
  intro h6
  obtain ⟨m, -, hm⟩ := rho_isPrimitiveRoot.eq_pow_of_pow_eq_one h6
  obtain ⟨r, hr, hre⟩ := exists_unit_eis_eq_rho_pow m
  have hden : (hbDen u v : ℂ) ≠ 0 := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (eNorm_pos hu)) (eNorm_pos hv)
    simp only [hbDen]; push_cast; exact_mod_cast this.ne'
  rw [hbAlpha_eq_of_sq hu hv hk hDk, ← hre] at hm
  have : eis (hbNum u v σ k) = eis (hbDen u v * r.1, hbDen u v * r.2) := by
    rw [← hm]; simp only [eis]; push_cast; field_simp
  exact hnum r hr (eis_injective this)

/-- **Off the lattice by the turn.** If `hbCheck` passes, `D = 3k²`, the turn is not a lattice
rotation, and each body has a contact (body 2's away from the hinge), the arrangement is off the
lattice: a contact of body 1 and a contact of body 2 are in different frames. Here the hinge and
both bar ends may all be lattice points. -/
theorem hbArr_not_isLattice_of_turn {l₁ l₂ : List (ℤ × ℤ)} {u v : ℤ × ℤ} {σ : ℤ}
    (h : hbCheck l₁ l₂ u v σ = true) {k : ℤ} (hk : 0 ≤ k) (hDk : hbD u v = 3 * k ^ 2)
    (hnum : ∀ r ∈ latticeUnits, hbNum u v σ k ≠ (hbDen u v * r.1, hbDen u v * r.2))
    {p p' q q' : ℤ × ℤ} (hp : p ∈ l₁) (hp' : p' ∈ l₁) (hpp : eNorm (p' - p) = 1)
    (hq : q ∈ l₂) (hq' : q' ∈ l₂) (hqq : eNorm (q' - q) = 1) : ¬ (hbArr h).IsLattice := by
  have ok := HBOk.of_check h
  obtain ⟨ip, hip⟩ := List.mem_iff_get.1 hp
  obtain ⟨ip', hip'⟩ := List.mem_iff_get.1 hp'
  obtain ⟨iq, hiq⟩ := List.mem_iff_get.1 hq
  obtain ⟨iq', hiq'⟩ := List.mem_iff_get.1 hq'
  have t₁ : Tangent (hbArr h).center (Sum.inl ip) (Sum.inl ip') := by
    show dist (latticePoint (l₁.get ip)) (latticePoint (l₁.get ip')) = 2
    rw [hip, hip', tangent_latticePoint_iff, ← eNorm_neg', neg_sub, hpp]
  have t₂ : Tangent (hbArr h).center (Sum.inr iq) (Sum.inr iq') := by
    show dist (hbAlpha u v σ * latticePoint (l₂.get iq)) (hbAlpha u v σ * latticePoint (l₂.get iq')) = 2
    rw [hiq, hiq', dist_eq_norm, ← mul_sub, norm_mul, ok.normα, one_mul, ← dist_eq_norm,
      tangent_latticePoint_iff, ← eNorm_neg', neg_sub, hqq]
  refine Arrangement.not_isLattice_of_frameInv_ne t₁ t₂ ?_
  show (latticePoint (l₁.get ip') - latticePoint (l₁.get ip)) ^ 6 ≠
    (hbAlpha u v σ * latticePoint (l₂.get iq') - hbAlpha u v σ * latticePoint (l₂.get iq)) ^ 6
  rw [hip, hip', hiq, hiq', ← mul_sub, ← latticePoint_sub, ← latticePoint_sub, mul_pow,
    latticePoint_unit_pow_six hpp, latticePoint_unit_pow_six hqq]
  intro e
  apply hbAlpha_pow_six_ne_one ok.hu0 ok.v0 hk hDk hnum
  have : (64 : ℂ) * 1 = 64 * hbAlpha u v σ ^ 6 := by rw [mul_one, e, mul_comm]
  exact (mul_left_cancel₀ (by norm_num) this).symm

/-- **An off-lattice arrangement whose hinge triangle is a lattice triangle** (`n = 15`). The
hinge `0`, the bar ends `X = latticePoint (0, 2) = 2 + 2√3 i` and `Y = 1 + 3√3 i` are lattice
points (`|HX|² = 16`, `|HY|² = 28`, `|XY| = 2`, so the hinge angle `arccos (5/(2√7))` occurs
between lattice vectors), yet body 2 (11 circles) is turned by `α ∈ ℚ(ρ)` with `α⁶ ≠ 1`. -/
def ex15L₂ : List (ℤ × ℤ) :=
  [(-1, 0), (0, -1), (-1, -1), (-2, 0), (-2, 1), (-3, 1), (-3, 2), (-2, 2), (-3, 3), (-2, 3)]

theorem ex15Check : hbCheck ex13L₁ ex15L₂ (0, 2) (-2, 3) 1 = true := by decide +kernel

noncomputable def ex15 := hbArr ex15Check

theorem ex15_isRigid : ex15.IsRigid := hbArr_isRigid ex15Check

theorem ex15_not_isLattice : ¬ ex15.IsLattice :=
  hbArr_not_isLattice_of_turn ex15Check (k := 2) (by norm_num) (by decide) (by decide)
    (p := (0, 1)) (p' := (1, 0)) (by decide) (by decide) (by decide)
    (q := (-1, 0)) (q' := (0, -1)) (by decide) (by decide) (by decide)

/-- The hinge triangle of `ex15` passes both `ℤ × ℤ` tests: T1 and T2 cannot see that it is off
the lattice. -/
example : normTriangle 4 7 = true ∧ frameCompatible (0, 2) (-2, 3) = true := by decide

end RigidArrangements

#print axioms RigidArrangements.ex15_not_isLattice
#print axioms RigidArrangements.ex15_isRigid
