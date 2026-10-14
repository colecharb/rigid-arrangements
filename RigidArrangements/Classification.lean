import RigidArrangements.CoreBound
import RigidArrangements.LatticeCert
import RigidArrangements.OffLattice
import RigidArrangements.Small

/-!
# The classification so far

This file combines the separate pieces into unconditional statements.

* **Complete classification for at most six circles.** `Small.lean` classifies rigid
  arrangements of four to six circles assuming no rigid arrangement of that size is a core,
  and `CoreBound.lean` proves that assumption (`noCoresBetween_four_six`). Up to isomorphism
  the rigid arrangements of `3, 4, 5, 6` circles number `1, 1, 1, 3`: the triangle, the
  rhombus, the trapezoid, and the parallelogram, chevron and big triangle. All of them lie on
  the triangular lattice. These are statements about *all* arrangements, not only lattice
  ones.
* **Lower bounds.** The certified lattice catalogues give at least
  `4, 9, 16, 35, 69, 155` rigid arrangements of `7, …, 12` circles. For eleven circles the
  off-lattice arrangement `O11` adds one more: at least `70`.

## Main results

* `card_rigidClasses_three_to_six`
* `isRigid_four_iff`, `isRigid_five_iff`, `isRigid_six_iff`
* `IsRigid.isLattice_of_card_le_six`
* `seventy_le_card_rigidClasses_eleven`
-/

namespace RigidArrangements

open Arrangement

/-- **Rigid arrangements of three to six circles.** Up to isomorphism there are `1, 1, 1, 3`
rigid arrangements of `3, 4, 5, 6` circles. -/
theorem card_rigidClasses_three_to_six :
    ENat.card (RigidClasses 3) = 1 ∧ ENat.card (RigidClasses 4) = 1 ∧
      ENat.card (RigidClasses 5) = 1 ∧ ENat.card (RigidClasses 6) = 3 :=
  card_rigidClasses_le_six noCoresBetween_four_six

/-- Four circles are rigid exactly when they form the rhombus. -/
theorem isRigid_four_iff (A : Arrangement (Fin 4)) : A.IsRigid ↔ A.Iso rhombus :=
  isRigid_iff_iso_rhombus (fun n A h4 h6 h => noCoresBetween_four_six n A h4 (by omega) h) A

/-- Five circles are rigid exactly when they form the trapezoid (three triangles in a row). -/
theorem isRigid_five_iff (A : Arrangement (Fin 5)) : A.IsRigid ↔ A.Iso trapezoid :=
  isRigid_iff_iso_trapezoid (fun n A h4 h6 h => noCoresBetween_four_six n A h4 (by omega) h) A

/-- Six circles are rigid exactly when they form the parallelogram, the chevron or the big
triangle. -/
theorem isRigid_six_iff (A : Arrangement (Fin 6)) :
    A.IsRigid ↔ A.Iso parallelogram ∨ A.Iso chevron ∨ A.Iso bigTriangle :=
  isRigid_iff_six noCoresBetween_four_six A

/-- Every rigid arrangement of at most six circles lies on the triangular lattice. -/
theorem IsRigid.isLattice_of_card_le_six {n : ℕ} (hn : n ≤ 6) {A : Arrangement (Fin n)}
    (hA : A.IsRigid) : A.IsLattice :=
  IsRigid.isLattice_of_le_six noCoresBetween_four_six hn hA

/-- **At least seventy rigid arrangements of eleven circles**: the `69` certified lattice ones,
and the off-lattice arrangement `O11`, which is isomorphic to none of them. -/
theorem seventy_le_card_rigidClasses_eleven : (70 : ℕ∞) ≤ ENat.card (RigidClasses 11) := by
  have hC := latticeCatalogue_certified_eleven
  let f : Option (Fin latticeCatalogue11.length) → RigidClasses 11 := fun o =>
    match o with
    | none => Quotient.mk (RigidArr.isoSetoid 11) ⟨o11, o11_isRigid⟩
    | some i => Quotient.mk (RigidArr.isoSetoid 11) ⟨hC.arr i, hC.isRigid_arr i⟩
  have hlat : ∀ i, ¬ o11.Iso (hC.arr i) := fun i h =>
    o11_not_iso_ofLattice _ _ (h.trans (ofLatticeFin_iso _ _ _))
  have hf : Function.Injective f := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd (Quotient.exact hij) (hlat j)
    · exact absurd (Quotient.exact hij).symm (hlat i)
    · exact congrArg some (by_contra fun hne => hC.not_iso_arr hne (Quotient.exact hij))
  have h := ENat.card_le_card_of_injective hf
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_option, Fintype.card_fin] at h
  have hlen : latticeCatalogue11.length = 69 := by decide
  rw [hlen] at h
  exact_mod_cast h

end RigidArrangements
