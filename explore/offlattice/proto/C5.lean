import RigidArrangements

/-!
# Scratch prototype (not in the repo): reducing C5 to cores

`C5` (every rigid arrangement of at most `10` circles is on the lattice) is equivalent to: no rigid
core with `9` or `10` circles is off the lattice. The reduction is proved here.
-/

namespace RigidArrangements

namespace Arrangement

variable {ι : Type*}

/-- **Adding a removable circle keeps the lattice.** If `A` without its removable circle `w` is on
the lattice, so is `A`: the circle `w` touches two circles less than `4` apart, so it sits at an
apex over two lattice points, which is a lattice point. -/
theorem isLattice_of_removable {n : ℕ} {A : Arrangement (Fin (n + 1))} {w : Fin (n + 1)}
    (hw : A.Removable w) (h : (A.comap w.succAbove Fin.succAbove_right_injective).IsLattice) :
    A.IsLattice := by
  obtain ⟨g, f, hf⟩ := h
  obtain ⟨u, v, huv, hadj, h4⟩ := hw
  have hu := (hadj u).2 (Or.inl rfl)
  have hv := (hadj v).2 (Or.inr rfl)
  -- every circle other than `w` is on a lattice point
  have hbase : ∀ k, k ≠ w → ∃ x, g (A.center k) = latticePoint x := by
    intro k hk
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    exact ⟨f j, hf j⟩
  obtain ⟨a, ha⟩ := hbase u hu.1.symm
  obtain ⟨b, hb⟩ := hbase v hv.1.symm
  have hab : a ≠ b := by
    intro e
    apply huv
    apply A.center_injective
    apply g.injective
    rw [ha, hb, e]
  have h4' : eNorm (a - b) < 4 := by
    have hsq := dist_latticePoint_sq a b
    rw [← ha, ← hb, g.dist_map] at hsq
    have h0 := dist_nonneg (x := A.center u) (y := A.center v)
    have : (eNorm (a - b) : ℝ) < 4 := by nlinarith
    exact_mod_cast this
  obtain ⟨x, -, hx⟩ := exists_mem_latticeApexes hab h4'
    (by rw [← ha, g.dist_map]; exact hu.2) (by rw [← hb, g.dist_map]; exact hv.2)
  have hall : ∀ k, ∃ x, g (A.center k) = latticePoint x := by
    intro k
    by_cases hk : k = w
    · subst hk; exact ⟨x, hx⟩
    · exact hbase k hk
  choose F hF using hall
  exact ⟨g, F, hF⟩

/-- **C5 reduces to cores.** If every rigid core with `9` or `10` circles lies on the lattice, then
every rigid arrangement of at most `10` circles does. -/
theorem isLattice_of_card_le_ten_of_cores
    (hcore : ∀ n, 9 ≤ n → n ≤ 10 → ∀ A : Arrangement (Fin n), A.IsRigid → A.IsCore →
      A.IsLattice) :
    ∀ n, n ≤ 10 → ∀ A : Arrangement (Fin n), A.IsRigid → A.IsLattice := by
  intro n
  induction n with
  | zero => intro _ A hA; exact hA.isLattice_of_card_le_eight (by omega)
  | succ n ih =>
    intro hn A hA
    by_cases h8 : n + 1 ≤ 8
    · exact hA.isLattice_of_card_le_eight h8
    by_cases hc : A.IsCore
    · exact hcore (n + 1) (by omega) hn A hA hc
    · simp only [IsCore, not_forall, not_not] at hc
      obtain ⟨w, hw⟩ := hc
      exact isLattice_of_removable hw (ih (by omega) _ (hw.isRigid_comap_succAbove hA))

end Arrangement

end RigidArrangements

#print axioms RigidArrangements.Arrangement.isLattice_of_card_le_ten_of_cores
