import RigidArrangements.Rigidity

/-!
# Removable circles and cores

A circle `w` of an arrangement is *removable* if it touches exactly two other circles,
`u` and `v`, and those two are less than `4` apart (so they are not on opposite sides of
`w`). Removing such a circle keeps a rigid arrangement rigid, and adding it back is a
Henneberg step (see `RigidArrangements.Henneberg`). A *core* is an arrangement with no
removable circle.

Every rigid arrangement is therefore built from a core (or the triangle) by adding circles
one at a time, each touching two earlier ones. Classifying rigid arrangements of up to `N`
circles reduces to classifying the rigid cores of up to `N` circles.

`NoCoresBetween a b` says that no rigid arrangement with between `a` and `b` circles is a
core.
-/

namespace RigidArrangements

namespace Arrangement

variable {ι : Type*} (A : Arrangement ι)

/-- Circle `w` touches exactly the two distinct circles `u` and `v`, which are less than `4`
apart. -/
def Removable (w : ι) : Prop :=
  ∃ u v, u ≠ v ∧ (∀ k, A.contactGraph.Adj w k ↔ k = u ∨ k = v) ∧
    dist (A.center u) (A.center v) < 4

/-- A *core*: no circle is removable. -/
def IsCore : Prop :=
  ∀ w, ¬ A.Removable w

end Arrangement

/-- No rigid arrangement with between `a` and `b` circles (inclusive) is a core: each one
has a removable circle. -/
def NoCoresBetween (a b : ℕ) : Prop :=
  ∀ (n : ℕ) (A : Arrangement (Fin n)), a ≤ n → n ≤ b → A.IsRigid → ∃ w, A.Removable w

end RigidArrangements
