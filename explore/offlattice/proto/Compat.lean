import RigidArrangements

/-!
# Scratch prototype (not in the repo): decidable off-lattice tests on `ℤ × ℤ` data

Two tests, both generalizing `Arrangement.o11_not_isLattice`.

* **T1, the hinge-triangle test** `normTriangle N₁ N₂`: is there a lattice triangle with side
  norms `N₁`, `N₂`, `1`? If not, any arrangement with circles `h, x, y`, `|hx|² = 4N₁`,
  `|hy|² = 4N₂` and `x, y` touching is off the lattice
  (`Arrangement.not_isLattice_of_normTriangle_eq_false`). O11 is `N₁ = N₂ = 3`.
* **T2, the frame-compatibility test** `frameCompatible u v`: some lattice symmetry `M` has
  `eNorm (u - M v) = 1`. If it fails for the bar vectors `u = x - h`, `v = y - h` of two lattice
  bodies (each placed by a plane isometry and each containing one contact), the union is off
  the lattice (`Arrangement.not_isLattice_of_frameCompatible_eq_false`).
-/

open ComplexConjugate

namespace RigidArrangements

theorem latticePoint_eq' (v : ℤ × ℤ) : latticePoint v = 2 * ((v.1 : ℂ) + (v.2 : ℂ) * rho) := by
  apply Complex.ext <;> simp [latticePoint] <;> ring

theorem latticePoint_sub' (v w : ℤ × ℤ) :
    latticePoint (v - w) = latticePoint v - latticePoint w := by
  rw [latticePoint_eq', latticePoint_eq', latticePoint_eq']
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-! ### T1: the hinge triangle -/

/-- All lattice vectors of `eNorm` `N` (they lie in the box `[-N, N]²`). -/
def vecsOfNorm (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N).filter fun v => eNorm v = N

theorem mem_vecsOfNorm {N : ℕ} {v : ℤ × ℤ} (h : eNorm v = N) : v ∈ vecsOfNorm N := by
  obtain ⟨a, b⟩ := v
  simp only [eNorm] at h
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, h⟩
  all_goals rcases Nat.eq_zero_or_pos N with hN | hN
  all_goals first
    | (subst hN; push_cast at h; nlinarith [sq_nonneg (a + 2 * b), sq_nonneg (2 * a + b)])
    | (have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
       nlinarith [sq_nonneg (a + 2 * b), sq_nonneg (2 * a + b), sq_nonneg (a - N),
         sq_nonneg (b - N), sq_nonneg (a + N), sq_nonneg (b + N)])

/-- **T1.** Is there a lattice triangle with side norms `N₁`, `N₂`, `1`? (The third vertex is
the first plus a unit vector.) -/
def normTriangle (N₁ N₂ : ℕ) : Bool :=
  decide (∃ a ∈ vecsOfNorm N₁, ∃ e ∈ latticeUnits, eNorm (a + e) = N₂)

theorem eNorm_neg' (v : ℤ × ℤ) : eNorm (-v) = eNorm v := by
  simp only [eNorm, Prod.fst_neg, Prod.snd_neg]; ring

theorem normTriangle_of_exists {N₁ N₂ : ℕ} {a b : ℤ × ℤ} (ha : eNorm a = N₁) (hb : eNorm b = N₂)
    (hab : eNorm (a - b) = 1) : normTriangle N₁ N₂ = true := by
  have he : eNorm (b - a) = 1 := by rw [← neg_sub, eNorm_neg', hab]
  have hmem : ∀ e : ℤ × ℤ, eNorm e = 1 → e ∈ latticeUnits := by
    intro e h
    obtain ⟨p, q⟩ := e
    simp only [eNorm] at h
    have h1 : p ≤ 1 := by nlinarith [sq_nonneg (p + 2 * q)]
    have h2 : -1 ≤ p := by nlinarith [sq_nonneg (p + 2 * q)]
    have h3 : q ≤ 1 := by nlinarith [sq_nonneg (2 * p + q)]
    have h4 : -1 ≤ q := by nlinarith [sq_nonneg (2 * p + q)]
    revert h
    interval_cases p <;> interval_cases q <;> decide
  simp only [normTriangle, decide_eq_true_eq]
  exact ⟨a, mem_vecsOfNorm ha, b - a, hmem _ he, by rw [add_sub_cancel, hb]⟩

namespace Arrangement

variable {ι : Type*}

/-- **T1 rules out the lattice.** Circles `h, x, y` with `|hx|² = 4N₁`, `|hy|² = 4N₂`, `x` and `y`
touching, and no lattice triangle with side norms `N₁, N₂, 1`: then `A` is off the lattice. -/
theorem not_isLattice_of_normTriangle_eq_false {A : Arrangement ι} {h x y : ι} {N₁ N₂ : ℕ}
    (hx : dist (A.center h) (A.center x) ^ 2 = 4 * N₁)
    (hy : dist (A.center h) (A.center y) ^ 2 = 4 * N₂)
    (hxy : Tangent A.center x y) (hT : normTriangle N₁ N₂ = false) : ¬ A.IsLattice := by
  rintro ⟨g, f, hf⟩
  have hd : ∀ i j, dist (latticePoint (f i)) (latticePoint (f j)) =
      dist (A.center i) (A.center j) := fun i j => by rw [← hf, ← hf, g.dist_map]
  have en : ∀ j (N : ℕ), dist (A.center h) (A.center j) ^ 2 = 4 * N →
      eNorm (f h - f j) = N := by
    intro j N hj
    have := dist_latticePoint_sq (f h) (f j)
    rw [hd, hj] at this
    exact_mod_cast (by linarith : ((eNorm (f h - f j) : ℤ) : ℝ) = (N : ℝ))
  have e1 : eNorm (f x - f y) = 1 := (tangent_latticePoint_iff _ _).1 ((hd x y).trans hxy)
  have := normTriangle_of_exists (en x N₁ hx) (en y N₂ hy)
    (by rw [show f h - f x - (f h - f y) = -(f x - f y) by abel, eNorm_neg', e1])
  rw [this] at hT
  exact Bool.noConfusion hT

/-- `O11` once more: `normTriangle 3 3 = false` by the kernel. -/
theorem o11_not_isLattice'' : ¬ o11.IsLattice :=
  not_isLattice_of_normTriangle_eq_false (N₁ := 3) (N₂ := 3)
    (by rw [o11_dist_sq_five_zero]; norm_num) (by rw [o11_dist_sq_five_six]; norm_num)
    o11_tangent_zero_six (by decide)

end Arrangement

/-! ### T2: frame compatibility -/

/-- **T2.** Some lattice symmetry `M` puts `M v` at distance one from `u`. -/
def frameCompatible (u v : ℤ × ℤ) : Bool :=
  latticeSymmetries.any fun M => eNorm (u - latticeMatApply M v) == 1

/-- Composition of integer matrices `(a, b, c, d)`. -/
def matMul : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ
  | (a, b, c, d), (a', b', c', d') => (a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d')

theorem latticeMatApply_matMul (M N : ℤ × ℤ × ℤ × ℤ) (v : ℤ × ℤ) :
    latticeMatApply (matMul M N) v = latticeMatApply M (latticeMatApply N v) := by
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨a', b', c', d'⟩ := N
  obtain ⟨p, q⟩ := v
  simp only [latticeMatApply, matMul, Prod.mk.injEq]
  constructor <;> ring

/-- The twelve symmetries form a group: `M₁⁻¹ M₂` is again a symmetry. -/
theorem exists_latticeSymmetry_div : ∀ M₁ ∈ latticeSymmetries, ∀ M₂ ∈ latticeSymmetries,
    ∃ M ∈ latticeSymmetries, matMul M₁ M = M₂ := by
  decide

/-- Rotations by `ρ^k` act on the lattice by symmetries. -/
theorem exists_latticeSymmetry_rho_pow (k : ℕ) :
    ∃ M ∈ latticeSymmetries, ∀ v, rho ^ k * latticePoint v = latticePoint (latticeMatApply M v) := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  rw [← rho_pow_mod_six]
  have : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 6)
  · exact ⟨(1, 0, 0, 1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq']; simp [latticeMatApply]⟩
  · exact ⟨(0, -1, 1, 1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq']; simp only [latticeMatApply]; push_cast
      linear_combination 2 * (v.2 : ℂ) * rho_sq⟩
  · exact ⟨(-1, -1, 1, 0), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', rho_sq]; simp only [latticeMatApply]; push_cast
      linear_combination 2 * (v.2 : ℂ) * rho_sq⟩
  · exact ⟨(-1, 0, 0, -1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', rho_pow_three]; simp only [latticeMatApply]
      push_cast; ring⟩
  · exact ⟨(0, 1, -1, -1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', h4]; simp only [latticeMatApply]; push_cast
      linear_combination -2 * (v.2 : ℂ) * rho_sq⟩
  · exact ⟨(1, 1, -1, 0), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', h5]; simp only [latticeMatApply]; push_cast
      linear_combination -2 * (v.2 : ℂ) * rho_sq⟩

/-- Complex conjugation acts on the lattice by the reflection `(p, q) ↦ (p + q, -q)`. -/
theorem conj_latticePoint (v : ℤ × ℤ) :
    conj (latticePoint v) = latticePoint (latticeMatApply (1, 1, 0, -1) v) := by
  apply Complex.ext <;> simp [latticePoint, latticeMatApply] <;> ring

/-- `ρ^k ∘ conj` acts on the lattice by symmetries. -/
theorem exists_latticeSymmetry_rho_pow_conj (k : ℕ) :
    ∃ M ∈ latticeSymmetries, ∀ v, rho ^ k * conj (latticePoint v) =
      latticePoint (latticeMatApply M v) := by
  obtain ⟨M, hM, h⟩ := exists_latticeSymmetry_rho_pow k
  refine ⟨matMul M (1, 1, 0, -1), ?_, fun v => by rw [conj_latticePoint, h, latticeMatApply_matMul]⟩
  have key : ∀ M ∈ latticeSymmetries, matMul M (1, 1, 0, -1) ∈ latticeSymmetries := by decide
  exact key M hM

/-- **Lattice-preserving linear isometries.** If the linear isometry `L` of the plane maps one
unit lattice vector to a unit lattice vector, it acts on the whole lattice as one of the twelve
symmetries. -/
theorem exists_latticeSymmetry_of_linearIsometry (L : ℂ ≃ₗᵢ[ℝ] ℂ) {e e' : ℤ × ℤ}
    (he : eNorm e = 1) (he' : eNorm e' = 1) (hL : L (latticePoint e) = latticePoint e') :
    ∃ M ∈ latticeSymmetries, ∀ v, L (latticePoint v) = latticePoint (latticeMatApply M v) := by
  have unit : ∀ {w : ℤ × ℤ}, eNorm w = 1 → ∃ m : ℕ, latticePoint w = 2 * rho ^ m := by
    intro w hw
    obtain ⟨M, hM, h⟩ := (⟨(1, 0, 0, 1), by decide, fun _ => rfl⟩ :
      ∃ M ∈ latticeSymmetries, ∀ v : ℤ × ℤ, latticeMatApply M v = latticeMatApply M v)
    clear h hM M
    have hm : w ∈ latticeUnits := by
      obtain ⟨p, q⟩ := w
      simp only [eNorm] at hw
      have h1 : p ≤ 1 := by nlinarith [sq_nonneg (p + 2 * q)]
      have h2 : -1 ≤ p := by nlinarith [sq_nonneg (p + 2 * q)]
      have h3 : q ≤ 1 := by nlinarith [sq_nonneg (2 * p + q)]
      have h4 : -1 ≤ q := by nlinarith [sq_nonneg (2 * p + q)]
      revert hw
      interval_cases p <;> interval_cases q <;> decide
    have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
    have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
    simp only [latticeUnits, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by rw [latticePoint_eq']; simp⟩
    · exact ⟨1, by rw [latticePoint_eq']; simp⟩
    · exact ⟨2, by rw [latticePoint_eq', rho_sq]; push_cast; ring⟩
    · exact ⟨3, by rw [latticePoint_eq', rho_pow_three]; push_cast; ring⟩
    · exact ⟨4, by rw [latticePoint_eq', h4]; push_cast; ring⟩
    · exact ⟨5, by rw [latticePoint_eq', h5]; push_cast; ring⟩
  obtain ⟨m, hm⟩ := unit he
  obtain ⟨m', hm'⟩ := unit he'
  have hρ0 : rho ≠ 0 := rho_ne_zero
  -- ρ^(6 m) = 1
  have hinv : rho ^ (5 * m) * rho ^ m = 1 := by
    rw [← pow_add, show 5 * m + m = 6 * m by ring, pow_mul, rho_pow_six, one_pow]
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex L
  · -- rotation: a = ρ^(m' + 5m)
    rw [ha, rotation_apply, hm, hm'] at hL
    have haρ : (a : ℂ) = rho ^ (m' + 5 * m) := by
      have : (a : ℂ) * rho ^ m = rho ^ m' := by
        linear_combination hL / 2
      calc (a : ℂ) = (a : ℂ) * (rho ^ (5 * m) * rho ^ m) := by rw [hinv, mul_one]
        _ = rho ^ (m' + 5 * m) := by rw [pow_add]; linear_combination rho ^ (5 * m) * this
    obtain ⟨M, hM, h⟩ := exists_latticeSymmetry_rho_pow (m' + 5 * m)
    exact ⟨M, hM, fun v => by rw [ha, rotation_apply, haρ, h]⟩
  · -- reflection: a = ρ^(m' + m)
    rw [ha, LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply, hm, hm',
      map_mul, map_pow, conj_rho, map_ofNat] at hL
    have h56 : (rho ^ 5) ^ m * rho ^ m = 1 := by
      rw [← pow_mul, ← pow_add, show 5 * m + m = 6 * m by ring, pow_mul, rho_pow_six, one_pow]
    have haρ : (a : ℂ) = rho ^ (m' + m) := by
      have : (a : ℂ) * (rho ^ 5) ^ m = rho ^ m' := by linear_combination hL / 2
      calc (a : ℂ) = (a : ℂ) * ((rho ^ 5) ^ m * rho ^ m) := by rw [h56, mul_one]
        _ = rho ^ (m' + m) := by rw [pow_add]; linear_combination rho ^ m * this
    obtain ⟨M, hM, h⟩ := exists_latticeSymmetry_rho_pow_conj (m' + m)
    exact ⟨M, hM, fun v => by
      rw [ha, LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply, haρ, h]⟩

namespace Arrangement

variable {ι : Type*}

/-- An isometry of the plane that puts a body (placed on lattice sites by `T`) with one contact
`p p'` onto the lattice moves the body's lattice vectors by a lattice symmetry. -/
theorem body_symm {A : Arrangement ι} (T g : Plane ≃ᵃⁱ[ℝ] Plane) (f : ι → ℤ × ℤ)
    (hf : ∀ i, g (A.center i) = latticePoint (f i)) {p p' : ι} {p₁ p₁' : ℤ × ℤ}
    (ep : A.center p = T (latticePoint p₁)) (ep' : A.center p' = T (latticePoint p₁'))
    (hp : eNorm (p₁ - p₁') = 1) :
    ∃ M ∈ latticeSymmetries, ∀ {i j : ι} {i₁ j₁ : ℤ × ℤ}, A.center i = T (latticePoint i₁) →
      A.center j = T (latticePoint j₁) → f i - f j = latticeMatApply M (i₁ - j₁) := by
  let G := T.trans g
  have hG : ∀ {i : ι} {i₁ : ℤ × ℤ}, A.center i = T (latticePoint i₁) →
      G (latticePoint i₁) = latticePoint (f i) := by
    intro i i₁ hi
    simp only [G, AffineIsometryEquiv.coe_trans, Function.comp_apply, ← hi, hf]
  have hL : ∀ {i j : ι} {i₁ j₁ : ℤ × ℤ}, A.center i = T (latticePoint i₁) →
      A.center j = T (latticePoint j₁) →
      G.linearIsometryEquiv (latticePoint (i₁ - j₁)) = latticePoint (f i - f j) := by
    intro i j i₁ j₁ hi hj
    have := G.map_vsub (latticePoint i₁) (latticePoint j₁)
    simp only [vsub_eq_sub] at this
    rw [latticePoint_sub', this, hG hi, hG hj, latticePoint_sub']
  have hpp : eNorm (f p - f p') = 1 := by
    rw [← tangent_latticePoint_iff, ← hf, ← hf, g.dist_map, ep, ep', T.dist_map,
      tangent_latticePoint_iff, hp]
  obtain ⟨M, hM, hMv⟩ := exists_latticeSymmetry_of_linearIsometry G.linearIsometryEquiv hp hpp
    (hL ep ep')
  exact ⟨M, hM, fun hi hj => latticePoint_injective (by rw [← hMv, hL hi hj])⟩

/-- **T2 rules out the lattice.** Two bodies, placed on lattice sites by plane isometries `T₁`
and `T₂`, each containing a contact (`p p'`, `q q'`), share the hinge `h` and are joined by a
bar `x y`. If no lattice symmetry brings `y₂ - h₂` to distance one from `x₁ - h₁`, the
arrangement is off the lattice. -/
theorem not_isLattice_of_frameCompatible_eq_false {A : Arrangement ι}
    (T₁ T₂ : Plane ≃ᵃⁱ[ℝ] Plane) {h x p p' y q q' : ι}
    {h₁ x₁ p₁ p₁' h₂ y₂ q₂ q₂' : ℤ × ℤ}
    (eh₁ : A.center h = T₁ (latticePoint h₁)) (ex : A.center x = T₁ (latticePoint x₁))
    (ep : A.center p = T₁ (latticePoint p₁)) (ep' : A.center p' = T₁ (latticePoint p₁'))
    (eh₂ : A.center h = T₂ (latticePoint h₂)) (ey : A.center y = T₂ (latticePoint y₂))
    (eq : A.center q = T₂ (latticePoint q₂)) (eq' : A.center q' = T₂ (latticePoint q₂'))
    (hp : eNorm (p₁ - p₁') = 1) (hq : eNorm (q₂ - q₂') = 1) (hxy : Tangent A.center x y)
    (hfc : frameCompatible (x₁ - h₁) (y₂ - h₂) = false) : ¬ A.IsLattice := by
  rintro ⟨g, f, hf⟩
  obtain ⟨M₁, hM₁, hb₁⟩ := body_symm T₁ g f hf ep ep' hp
  obtain ⟨M₂, hM₂, hb₂⟩ := body_symm T₂ g f hf eq eq' hq
  have hx := hb₁ ex eh₁
  have hy := hb₂ ey eh₂
  have e1 : eNorm (f x - f y) = 1 := by
    rw [← tangent_latticePoint_iff, ← hf, ← hf, g.dist_map]; exact hxy
  obtain ⟨M, hM, hMM⟩ := exists_latticeSymmetry_div M₁ hM₁ M₂ hM₂
  have : eNorm ((x₁ - h₁) - latticeMatApply M (y₂ - h₂)) = 1 := by
    rw [← eNorm_latticeMatApply hM₁, ← latticeMatApply_sub, ← latticeMatApply_matMul, hMM, ← hx,
      ← hy, show f x - f h - (f y - f h) = f x - f y by abel, e1]
  have ht : frameCompatible (x₁ - h₁) (y₂ - h₂) = true := by
    simp only [frameCompatible, List.any_eq_true, beq_iff_eq]
    exact ⟨M, hM, this⟩
  rw [ht] at hfc
  exact Bool.noConfusion hfc

end Arrangement

end RigidArrangements

#print axioms RigidArrangements.Arrangement.not_isLattice_of_normTriangle_eq_false
#print axioms RigidArrangements.Arrangement.o11_not_isLattice''
#print axioms RigidArrangements.Arrangement.not_isLattice_of_frameCompatible_eq_false
