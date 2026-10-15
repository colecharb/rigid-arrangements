
/-! ===================== constructor + T1 ===================== -/

namespace RigidArrangements

/-- **Certified off-lattice two-body arrangements.** If `hbCheck` passes and there is no lattice
triangle with side norms `N₁ = eNorm u`, `N₂ = eNorm v`, `1`, then the hinge-and-bar arrangement
is rigid (`hbArr_isRigid`) and off the lattice. -/
theorem hbArr_not_isLattice {l₁ l₂ : List (ℤ × ℤ)} {u v : ℤ × ℤ} {σ : ℤ}
    (h : hbCheck l₁ l₂ u v σ = true)
    (hT : normTriangle (eNorm u).toNat (eNorm v).toNat = false) : ¬ (hbArr h).IsLattice := by
  have ok := HBOk.of_check h
  obtain ⟨a, ha⟩ := List.mem_iff_get.1 ok.h0
  obtain ⟨x, hx⟩ := List.mem_iff_get.1 ok.hu
  obtain ⟨y, hy⟩ := List.mem_iff_get.1 ok.hv
  have cu : ((eNorm u).toNat : ℝ) = eNorm u := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (eNorm_nonneg u)]
  have cv : ((eNorm v).toNat : ℝ) = eNorm v := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (eNorm_nonneg v)]
  refine Arrangement.not_isLattice_of_normTriangle_eq_false (h := Sum.inl a) (x := Sum.inl x)
    (y := Sum.inr y) ?_ ?_ ?_ hT
  · show dist (latticePoint (l₁.get a)) (latticePoint (l₁.get x)) ^ 2 = _
    rw [ha, hx, dist_latticePoint_sq, zero_sub, eNorm_neg', cu]
  · show dist (latticePoint (l₁.get a)) (hbAlpha u v σ * latticePoint (l₂.get y)) ^ 2 = _
    rw [ha, hy, latticePoint_zero', dist_comm, dist_zero_right, norm_mul, ok.normα, one_mul,
      ← dist_zero_right, ← latticePoint_zero', dist_comm, dist_latticePoint_sq, zero_sub,
      eNorm_neg', cv]
  · show dist (latticePoint (l₁.get x)) (hbAlpha u v σ * latticePoint (l₂.get y)) = 2
    rw [hx, hy]
    exact dist_bar ok.hu0 ok.v0 ok.hD (by exact_mod_cast ok.hσ)

/-- `O11` through the constructor is off the lattice (`D = 11`, `normTriangle 3 3 = false`). -/
theorem o11'_not_isLattice : ¬ o11'.IsLattice :=
  hbArr_not_isLattice o11Check (by decide)

/-- **A second certified example**, `n = 13` (`N₁ = N₂ = 4`, `D = 15`): two 7-circle bodies
(`l₁`, `0 :: l₂` below) glued at a hinge, bar between sites at lattice distance `4` from it. -/
def ex13L₁ : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, 1), (2, 2)]

end RigidArrangements

#print axioms RigidArrangements.o11'_not_isLattice
