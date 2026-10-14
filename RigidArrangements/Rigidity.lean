import RigidArrangements.Basic

/-!
# Rigid arrangements

This file fixes the formal meaning of the problem in `docs/problem.md`.

* `Arrangement.KeepsContacts A q`: the placement `q` keeps every tangency of `A`.
* `Arrangement.IsLocallyRigid A`: every placement close enough to `A` that keeps every
  tangency is *congruent* to `A`, meaning all pairwise distances are unchanged. This is
  the standard notion of local rigidity of a bar framework (Asimow–Roth). It is the
  nonlinear notion, not infinitesimal rigidity, so "singular" arrangements that are
  rigid only to higher order still count as rigid.
* `Arrangement.TouchesTwo A`: every circle is tangent to at least two others.
* `Arrangement.IsRigid A`: `TouchesTwo` and `IsLocallyRigid`.
* `Arrangement.Congruent A B`: after relabeling, `A` and `B` have the same pairwise
  distances. This is the notion of isomorphism used for the enumeration.

## Main results

* `not_isRigid_of_le_two`: one or two circles are never rigid.
* `tangent_of_touchesTwo_three`: in a rigid arrangement of 3 circles every pair is
  tangent.
* `triangle_isRigid`: the equilateral triangle of side `2` is rigid.
* `congruent_triangle_of_isRigid`: every rigid arrangement of 3 circles is congruent to
  the equilateral triangle.
-/

namespace RigidArrangements

namespace Arrangement

variable {n : ℕ} (A : Arrangement n)

/-- The placement `q` keeps every tangency of `A`: tangent pairs of `A` are still at
distance `2`. New tangencies may appear. -/
def KeepsContacts (q : Fin n → Plane) : Prop :=
  ∀ i j, A.Tangent i j → dist (q i) (q j) = 2

/-- `A` is *locally rigid*: there is an `ε > 0` such that every placement `q` that moves
each center by less than `ε` and keeps every tangency of `A` has the same pairwise
distances as `A`, so it is congruent to `A`.

`q` is not required to be non-overlapping. Pairs that are not tangent in `A` are strictly
more than `2` apart, so they stay apart for small `ε` anyway. -/
def IsLocallyRigid : Prop :=
  ∃ ε > 0, ∀ q : Fin n → Plane, (∀ i, dist (q i) (A.center i) < ε) → A.KeepsContacts q →
    ∀ i j, dist (q i) (q j) = dist (A.center i) (A.center j)

/-- Every circle of `A` is tangent to at least two other circles. -/
def TouchesTwo : Prop :=
  ∀ i, ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧ A.Tangent i j ∧ A.Tangent i k

/-- A *rigid arrangement*: every circle touches at least two others, and no motion that
keeps all tangencies changes the shape. -/
def IsRigid : Prop :=
  A.TouchesTwo ∧ A.IsLocallyRigid

/-- `A` and `B` are *congruent* (isomorphic): some relabeling of `B`'s circles has the
same pairwise distances as `A`. In the plane this is the same as `B` being the image of
`A` under a relabeling and an isometry, reflections allowed. -/
def Congruent (A B : Arrangement n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, dist (B.center (σ i)) (B.center (σ j)) =
    dist (A.center i) (A.center j)

theorem Congruent.refl : A.Congruent A :=
  ⟨1, fun _ _ => rfl⟩

theorem Congruent.symm {A B : Arrangement n} (h : A.Congruent B) : B.Congruent A := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ⁻¹, fun i j => ?_⟩
  simpa using (hσ (σ⁻¹ i) (σ⁻¹ j)).symm

theorem Congruent.trans {A B C : Arrangement n} (hAB : A.Congruent B)
    (hBC : B.Congruent C) : A.Congruent C := by
  obtain ⟨σ, hσ⟩ := hAB
  obtain ⟨τ, hτ⟩ := hBC
  exact ⟨σ.trans τ, fun i j => (hτ (σ i) (σ j)).trans (hσ i j)⟩

/-- One or two circles are never rigid: a circle has no two *other* circles to touch.
(The empty arrangement is rigid vacuously; it is excluded by the hypothesis `0 < n`.) -/
theorem not_isRigid_of_le_two (h0 : 0 < n) (h2 : n ≤ 2) : ¬ A.IsRigid := by
  rintro ⟨hT, -⟩
  obtain ⟨j, k, hjk, hij, hik, -, -⟩ := hT ⟨0, h0⟩
  rw [Ne, Fin.ext_iff] at hjk hij hik
  have := j.isLt
  have := k.isLt
  simp only at hij hik
  omega

/-- In an arrangement of three circles where each touches two others, every pair of
distinct circles is tangent. -/
theorem tangent_of_touchesTwo_three {A : Arrangement 3} (h : A.TouchesTwo) :
    ∀ i j, i ≠ j → A.Tangent i j := by
  intro i j hij
  obtain ⟨a, b, hab, hia, hib, ha, hb⟩ := h i
  have hj : j = a ∨ j = b := by
    rw [Ne, Fin.ext_iff] at hab hia hib hij
    rw [Fin.ext_iff, Fin.ext_iff]
    have := a.isLt; have := b.isLt; have := j.isLt; have := i.isLt
    omega
  rcases hj with rfl | rfl
  · exact ha
  · exact hb

/-- If every pair of distinct circles is tangent, the arrangement is locally rigid:
nothing can move without breaking a tangency. -/
theorem isLocallyRigid_of_complete (h : ∀ i j, i ≠ j → A.Tangent i j) :
    A.IsLocallyRigid := by
  refine ⟨1, one_pos, fun q _ hq i j => ?_⟩
  by_cases hij : i = j
  · subst hij; simp
  · rw [hq i j (h i j hij), h i j hij]

/-! ### The equilateral triangle -/

/-- `dist` between two points of the plane, in coordinates. -/
theorem dist_coords (a b c d : ℝ) :
    dist (!₂[a, b] : Plane) !₂[c, d] = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The three vertices of an equilateral triangle of side `2`. -/
noncomputable def trianglePoint : Fin 3 → Plane :=
  ![!₂[0, 0], !₂[2, 0], !₂[1, Real.sqrt 3]]

theorem trianglePoint_dist {i j : Fin 3} (hij : i ≠ j) :
    dist (trianglePoint i) (trianglePoint j) = 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp only [trianglePoint, Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val, dist_coords]
       rw [← h4]; congr 1; nlinarith [h3])

/-- The equilateral triangle: three mutually tangent unit circles. -/
noncomputable def triangle : Arrangement 3 where
  center := trianglePoint
  nonoverlap _ _ hij := (trianglePoint_dist hij).ge

theorem triangle_tangent {i j : Fin 3} (hij : i ≠ j) : triangle.Tangent i j :=
  trianglePoint_dist hij

/-- **The equilateral triangle is rigid.** -/
theorem triangle_isRigid : triangle.IsRigid := by
  refine ⟨fun i => ?_, isLocallyRigid_of_complete _ fun _ _ => triangle_tangent⟩
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide, triangle_tangent (by decide),
      triangle_tangent (by decide)⟩
  · exact ⟨0, 2, by decide, by decide, by decide, triangle_tangent (by decide),
      triangle_tangent (by decide)⟩
  · exact ⟨0, 1, by decide, by decide, by decide, triangle_tangent (by decide),
      triangle_tangent (by decide)⟩

/-- **The only rigid arrangement of three circles is the equilateral triangle**, up to
congruence. -/
theorem congruent_triangle_of_isRigid {A : Arrangement 3} (h : A.IsRigid) :
    A.Congruent triangle := by
  have hA := tangent_of_touchesTwo_three h.1
  refine ⟨1, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij; simp
  · simp only [Equiv.Perm.coe_one, id]
    rw [triangle_tangent hij, hA i j hij]

end Arrangement

end RigidArrangements
