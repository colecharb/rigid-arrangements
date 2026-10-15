import RigidArrangements.Basic

/-!
# Rigid arrangements

This file fixes the formal meaning of the problem in `docs/problem.md`.

* `Arrangement.IsRigid A`: `A` is locally rigid in the sense of Asimow–Roth (see
  `IsLocallyRigid`). This is the standard notion of a rigid bar framework, applied to the
  contact graph with all bars of length `2`. The user's extra clause "each circle touches two
  others" is *not* part of the definition: for three or more circles it follows from rigidity
  (`Arrangement.IsRigid.touchesTwo` in `RigidArrangements.Flex`), and one circle or two
  tangent circles are rigid in the standard sense (rolling one circle around the other is a
  rigid motion of the pair).
* `Arrangement.Iso A B`: after relabeling, `A` and `B` have the same pairwise distances.
  In the plane this is the same as a relabeling followed by an isometry, reflections
  allowed. This is the notion of isomorphism used for the enumeration.
* `RigidClasses n`: rigid arrangements of `n` circles up to isomorphism, the objects to be
  counted.

## Main results

* `isRigid_of_subsingleton`, `isRigid_pair`: one circle, and two tangent circles, are
  (trivially) rigid.
* `triangle_isRigid`: the equilateral triangle of side `2` is rigid.
* `iso_triangle_of_forall_tangent`: three mutually tangent circles form the triangle, up to
  isomorphism.
-/

namespace RigidArrangements

namespace Arrangement

variable {ι κ ν : Type*} (A : Arrangement ι)

/-- A *rigid arrangement*: no motion that keeps all tangencies changes the shape. -/
def IsRigid : Prop :=
  IsLocallyRigid A.center

/-- `A` and `B` are *isomorphic*: some relabeling makes all pairwise distances agree. -/
def Iso (B : Arrangement κ) : Prop :=
  ∃ e : ι ≃ κ, Congruent A.center (B.center ∘ e)

/-- Every arrangement is isomorphic to itself. -/
theorem Iso.refl : A.Iso A :=
  ⟨Equiv.refl ι, Congruent.refl _⟩

/-- Isomorphism is symmetric. -/
theorem Iso.symm {A : Arrangement ι} {B : Arrangement κ} (h : A.Iso B) : B.Iso A := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [congruent_iff_dist_eq] at he ⊢
  intro i j
  simpa using (he (e.symm i) (e.symm j)).symm

/-- Isomorphism is transitive. -/
theorem Iso.trans {A : Arrangement ι} {B : Arrangement κ} {C : Arrangement ν}
    (h₁ : A.Iso B) (h₂ : B.Iso C) : A.Iso C := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨f, hf⟩ := h₂
  refine ⟨e.trans f, ?_⟩
  rw [congruent_iff_dist_eq] at he hf ⊢
  intro i j
  exact (he i j).trans (by simpa using hf (e i) (e j))

/-! ### Trivial cases -/

/-- A single circle is rigid. -/
theorem isRigid_of_subsingleton [Subsingleton ι] : A.IsRigid :=
  isLocallyRigid_of_forall_tangent fun i j hij => absurd (Subsingleton.elim i j) hij

/-- If every pair of distinct circles is tangent, the arrangement is rigid. -/
theorem isRigid_of_forall_tangent (h : ∀ i j, i ≠ j → Tangent A.center i j) : A.IsRigid :=
  isLocallyRigid_of_forall_tangent h

/-- Two tangent circles are rigid: the pair can only roll around as a whole, which does not
change its shape. -/
theorem isRigid_pair (A : Arrangement (Fin 2)) (h : Tangent A.center 0 1) : A.IsRigid := by
  refine A.isRigid_of_forall_tangent fun i j hij => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h
  · exact tangent_comm.mp h
  · exact absurd rfl hij

/-! ### The equilateral triangle -/

/-- The three vertices of an equilateral triangle of side `2`. -/
noncomputable def trianglePoint : Fin 3 → Plane :=
  ![0, 2, ⟨1, Real.sqrt 3⟩]

/-- Distinct vertices of `trianglePoint` are `2` apart. -/
theorem trianglePoint_dist {i j : Fin 3} (hij : i ≠ j) :
    dist (trianglePoint i) (trianglePoint j) = 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (rw [Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq, ← h4]
       norm_num [trianglePoint])

/-- The equilateral triangle: three mutually tangent unit circles. -/
noncomputable def triangle : Arrangement (Fin 3) where
  center := trianglePoint
  nonoverlap _ _ hij := (trianglePoint_dist hij).ge

/-- Any two distinct circles of the triangle touch. -/
theorem triangle_tangent {i j : Fin 3} (hij : i ≠ j) : Tangent triangle.center i j :=
  trianglePoint_dist hij

/-- **The equilateral triangle is rigid.** -/
theorem triangle_isRigid : triangle.IsRigid :=
  triangle.isRigid_of_forall_tangent fun _ _ => triangle_tangent

/-- Three mutually tangent circles form the equilateral triangle, up to isomorphism. -/
theorem iso_triangle_of_forall_tangent {A : Arrangement (Fin 3)}
    (h : ∀ i j, i ≠ j → Tangent A.center i j) : A.Iso triangle := by
  refine ⟨Equiv.refl _, ?_⟩
  rw [congruent_iff_dist_eq]
  intro i j
  by_cases hij : i = j
  · subst hij; simp
  · simp only [Equiv.coe_refl, Function.comp_apply, id]
    rw [h i j hij, triangle_tangent hij]

end Arrangement

/-- Rigid arrangements of `n` circles. -/
def RigidArr (n : ℕ) : Type :=
  {A : Arrangement (Fin n) // A.IsRigid}

/-- Isomorphism of rigid arrangements of `n` circles, as a setoid. -/
instance RigidArr.isoSetoid (n : ℕ) : Setoid (RigidArr n) where
  r A B := A.1.Iso B.1
  iseqv := ⟨fun A => Arrangement.Iso.refl A.1, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **The objects to be counted**: rigid arrangements of `n` circles up to isomorphism. -/
def RigidClasses (n : ℕ) : Type :=
  Quotient (RigidArr.isoSetoid n)

end RigidArrangements
