
/-! ===================== two bodies sharing two circles (Σ7) ===================== -/

namespace RigidArrangements

/-- **Two lattice bodies sharing two circles** (`n = 17`), rebuilt as hinge + bar: body 1 (8
circles) contains the hinge `0` and `u = (1, -3)` (`|u|² = 4·7`); body 2 (11 circles, the body of
`ex15`, mirrored) contains the hinge and a circle that lands exactly on `u`; here it is entered
without that circle, and the bar runs from `u` to its neighbour `v = (-3, 3)` (`N₂ = 9`,
`D = 27 = 3·3²`). The turn is the `Σ7` coincidence rotation; all coordinates lie in `ℚ(√3)`. -/
def ex17L₁ : List (ℤ × ℤ) := [(0, 0), (0, -1), (-1, 0), (-1, -1), (0, -2), (-1, -2), (0, -3), (1, -3)]
def ex17L₂ : List (ℤ × ℤ) :=
  [(-1, 0), (0, -1), (-1, -1), (-2, 0), (-2, 1), (-3, 1), (-3, 2), (-2, 2), (-3, 3)]

theorem ex17Check : hbCheck ex17L₁ ex17L₂ (1, -3) (-3, 3) 1 = true := by decide +kernel

noncomputable def ex17 := hbArr ex17Check

theorem ex17_isRigid : ex17.IsRigid := hbArr_isRigid ex17Check

theorem ex17_not_isLattice : ¬ ex17.IsLattice :=
  hbArr_not_isLattice_of_turn ex17Check (k := 3) (by norm_num) (by decide) (by decide)
    (p := (0, 0)) (p' := (0, -1)) (by decide) (by decide) (by decide)
    (q := (-1, 0)) (q' := (0, -1)) (by decide) (by decide) (by decide)

end RigidArrangements

#print axioms RigidArrangements.ex17_not_isLattice
#print axioms RigidArrangements.ex17_isRigid
