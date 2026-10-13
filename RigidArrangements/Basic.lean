import Mathlib

/-!
# Arrangements of unit circles

A unit circle in the plane is determined by its center. Two unit circles are
*(externally) tangent* exactly when their centers are at distance `2`, and they
*overlap* when their centers are closer than `2`.

An `Arrangement n` is a placement of `n` non-overlapping unit circles. Its
*contact graph* has one vertex per circle and an edge between each tangent pair.

The notion of a *rigid* arrangement is not defined yet: it will be added once the
full problem statement is written up in `docs/problem.md`.
-/

namespace RigidArrangements

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- An arrangement of `n` unit circles, recorded by their centers, such that no two
distinct circles overlap. -/
structure Arrangement (n : ℕ) where
  /-- The center of the `i`-th circle. -/
  center : Fin n → Plane
  /-- Distinct circles have centers at distance at least `2`. -/
  nonoverlap : ∀ i j, i ≠ j → 2 ≤ dist (center i) (center j)

namespace Arrangement

variable {n : ℕ} (A : Arrangement n)

/-- Circles `i` and `j` of `A` are tangent. -/
def Tangent (i j : Fin n) : Prop :=
  dist (A.center i) (A.center j) = 2

theorem tangent_comm {i j : Fin n} : A.Tangent i j ↔ A.Tangent j i := by
  simp only [Tangent, dist_comm]

/-- The contact graph of `A`: circles are adjacent when they are tangent. -/
def contactGraph : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ A.Tangent i j
  symm := ⟨fun _ _ ⟨hne, ht⟩ => ⟨hne.symm, A.tangent_comm.mp ht⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- No two circles of an arrangement share a center. -/
theorem center_injective : Function.Injective A.center := by
  intro i j h
  by_contra hij
  have := A.nonoverlap i j hij
  rw [h, dist_self] at this
  norm_num at this

end Arrangement

end RigidArrangements
