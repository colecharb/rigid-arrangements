import RigidArrangements

/-!
# Scratch prototype (not in the repo): lattice growth

`Grown A S₀ k`: circle `k` is obtained from the seed `S₀` by repeatedly adding a circle that
touches two already grown circles less than `4` apart. (Two touching grown circles are `2`
apart, so this covers growing through edge-sharing triangles.)

* `Arrangement.isLattice_of_grown`: if the seed is on the lattice and every circle is grown,
  the arrangement is on the lattice.
* `Arrangement.isLattice_of_grown_pair`: the seed may be a single contact.
* `Arrangement.isLattice_of_triGrown`: **triangle-connected arrangements are on the lattice.**
* `Arrangement.isRigid_of_grown_pair`: what is grown from a contact is also rigid, so it is a
  rigid lattice body.
-/

namespace RigidArrangements

namespace Arrangement

variable {ι : Type*}

/-- Lattice growth from a seed set `S₀`. -/
inductive Grown (A : Arrangement ι) (S₀ : Set ι) : ι → Prop
  | base {i : ι} : i ∈ S₀ → Grown A S₀ i
  | step {i j k : ι} : Grown A S₀ i → Grown A S₀ j → i ≠ j →
      dist (A.center i) (A.center j) < 4 → Tangent A.center k i → Tangent A.center k j →
      Grown A S₀ k

/-- Triangle growth from the contact `a b`: add a circle touching both ends of a grown contact. -/
inductive TriGrown (A : Arrangement ι) (a b : ι) : ι → Prop
  | left : TriGrown A a b a
  | right : TriGrown A a b b
  | step {i j k : ι} : TriGrown A a b i → TriGrown A a b j → i ≠ j → Tangent A.center i j →
      Tangent A.center k i → Tangent A.center k j → TriGrown A a b k

theorem TriGrown.grown {A : Arrangement ι} {a b k : ι} (h : A.TriGrown a b k) :
    A.Grown {a, b} k := by
  induction h with
  | left => exact .base (by simp)
  | right => exact .base (by simp)
  | step _ _ hij hij' hki hkj ihi ihj =>
    exact .step ihi ihj hij (by rw [show dist _ _ = 2 from hij']; norm_num) hki hkj

/-- **Growth stays on the lattice.** If an isometry `g` puts the seed on lattice points, it puts
every grown circle on a lattice point. -/
theorem Grown.exists_latticePoint {A : Arrangement ι} {S₀ : Set ι} (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : ∀ i ∈ S₀, ∃ v, g (A.center i) = latticePoint v) {k : ι} (hk : A.Grown S₀ k) :
    ∃ v, g (A.center k) = latticePoint v := by
  induction hk with
  | base hi => exact hS _ hi
  | @step i j k _ _ hij h4 hki hkj ihi ihj =>
    obtain ⟨u, hu⟩ := ihi
    obtain ⟨w, hw⟩ := ihj
    have huw : u ≠ w := by
      intro e
      apply hij
      apply A.center_injective
      apply g.injective
      rw [hu, hw, e]
    have h4' : eNorm (u - w) < 4 := by
      have hsq := dist_latticePoint_sq u w
      rw [← hu, ← hw, g.dist_map] at hsq
      have h0 := dist_nonneg (x := A.center i) (y := A.center j)
      have : (eNorm (u - w) : ℝ) < 4 := by nlinarith
      exact_mod_cast this
    obtain ⟨x, -, hx⟩ := exists_mem_latticeApexes huw h4'
      (by rw [← hu, g.dist_map]; exact hki) (by rw [← hw, g.dist_map]; exact hkj)
    exact ⟨x, hx⟩

/-- **Theorem 1 (general form).** If the seed `S₀` lies on the lattice (via one isometry) and
every circle is grown from it, the arrangement lies on the lattice. -/
theorem isLattice_of_grown {A : Arrangement ι} {S₀ : Set ι} (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : ∀ i ∈ S₀, ∃ v, g (A.center i) = latticePoint v) (hall : ∀ k, A.Grown S₀ k) :
    A.IsLattice := by
  choose f hf using fun k => (hall k).exists_latticePoint g hS
  exact ⟨g, f, hf⟩

/-- A single contact can be put on the lattice. -/
theorem exists_isometry_pair {A : Arrangement ι} {a b : ι} (hab : Tangent A.center a b) :
    ∃ g : Plane ≃ᵃⁱ[ℝ] Plane, g (A.center a) = latticePoint 0 ∧
      g (A.center b) = latticePoint (1, 0) := by
  have hc : Congruent ![A.center a, A.center b] ![latticePoint 0, latticePoint (1, 0)] := by
    rw [congruent_iff_dist_eq]
    have h2 : dist (latticePoint 0) (latticePoint (1, 0)) = 2 :=
      (tangent_latticePoint_iff _ _).2 (by decide)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hab.symm ▸ h2, h2, dist_comm, show dist (A.center a) (A.center b) = 2 from hab]
  obtain ⟨g, hg⟩ := exists_affineIsometryEquiv_of_congruent hc
  exact ⟨g, by simpa using hg 0, by simpa using hg 1⟩

/-- **Theorem 1, seeded by a contact.** -/
theorem isLattice_of_grown_pair {A : Arrangement ι} {a b : ι} (hab : Tangent A.center a b)
    (hall : ∀ k, A.Grown {a, b} k) : A.IsLattice := by
  obtain ⟨g, ha, hb⟩ := exists_isometry_pair hab
  refine isLattice_of_grown g (fun i hi => ?_) hall
  rcases hi with rfl | rfl
  · exact ⟨0, ha⟩
  · exact ⟨(1, 0), hb⟩

/-- **Theorem 1: triangle-connected arrangements lie on the lattice.** If every circle is reached
from the contact `a b` by a chain of triangles, each sharing an edge with grown circles, the
arrangement is congruent to a lattice arrangement. -/
theorem isLattice_of_triGrown {A : Arrangement ι} {a b : ι} (hab : Tangent A.center a b)
    (hall : ∀ k, A.TriGrown a b k) : A.IsLattice :=
  isLattice_of_grown_pair hab fun k => (hall k).grown

/-- Contrapositive, the form that matters for off-lattice arrangements: **an arrangement off the
lattice is not grown from any single contact**; for every contact some circle is missed. -/
theorem exists_not_grown_of_not_isLattice {A : Arrangement ι} (hA : ¬ A.IsLattice) {a b : ι}
    (hab : Tangent A.center a b) : ∃ k, ¬ A.Grown {a, b} k := by
  by_contra h
  push Not at h
  exact hA (isLattice_of_grown_pair hab h)

/-! ### Grown sets are rigid -/

/-- A circle outside a finite set `T` containing the seed, but grown from the seed, forces some
circle outside `T` that touches two distinct circles of `T`. -/
theorem Grown.exists_frontier {A : Arrangement ι} {S₀ T : Set ι} (hST : S₀ ⊆ T) {k : ι}
    (hk : A.Grown S₀ k) (hkT : k ∉ T) :
    ∃ k' ∉ T, ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ Tangent A.center k' i ∧ Tangent A.center k' j := by
  induction hk with
  | base hi => exact absurd (hST hi) hkT
  | @step i j k _ _ hij _ hki hkj ihi ihj =>
    by_cases hi : i ∈ T
    · by_cases hj : j ∈ T
      · exact ⟨k, hkT, i, hi, j, hj, hij, hki, hkj⟩
      · exact ihj hj
    · exact ihi hi

/-- **What is grown from a contact is rigid**: a sequence of Henneberg steps. -/
theorem isRigid_of_grown_pair [Finite ι] {A : Arrangement ι} {a b : ι}
    (hab : Tangent A.center a b) (hne : a ≠ b) (hall : ∀ k, A.Grown {a, b} k) : A.IsRigid := by
  classical
  have := Fintype.ofFinite ι
  let pl : (T : Finset ι) → T → Plane := fun T v => A.center v.1
  -- grow rigid finsets `T ⊇ {a, b}` by induction on the number of missing circles
  have grow : ∀ (n : ℕ) (T : Finset ι), ({a, b} : Set ι) ⊆ (T : Set ι) →
      (Finset.univ \ T).card = n → IsLocallyRigid (pl T) → A.IsRigid := by
    intro n
    induction n with
    | zero =>
      intro T _ hn hT
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hn
      have hTu : ∀ x, x ∈ T := fun x => hn (Finset.mem_univ x)
      let e : ι ≃ T := ⟨fun x => ⟨x, hTu x⟩, fun v => v.1, fun _ => rfl, fun _ => rfl⟩
      have := (isLocallyRigid_comp_equiv_iff (p := pl T) e).2 hT
      exact this
    | succ n ih =>
      intro T hab' hn hT
      obtain ⟨k₀, hk₀⟩ : (Finset.univ \ T).Nonempty := Finset.card_pos.mp (by omega)
      have hk₀T : k₀ ∉ (T : Set ι) := by simpa using hk₀
      obtain ⟨k, hkT, i, hi, j, hj, hij, hki, hkj⟩ := (hall k₀).exists_frontier hab' hk₀T
      have hkT' : k ∉ T := by simpa using hkT
      refine ih (insert k T) (hab'.trans (by simp)) ?_ ?_
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem (by simpa using hkT'), hn,
          Nat.add_sub_cancel]
      · -- Henneberg step
        let f : T → (insert k T : Finset ι) := fun v => ⟨v.1, Finset.mem_insert_of_mem v.2⟩
        let k' : (insert k T : Finset ι) := ⟨k, Finset.mem_insert_self k T⟩
        have hrange : {k'}ᶜ ⊆ Set.range f := by
          intro v hv
          have hvk : v.1 ≠ k := fun e => hv (Subtype.ext e)
          exact ⟨⟨v.1, (Finset.mem_insert.mp v.2).resolve_left hvk⟩, rfl⟩
        have hcomp : pl (insert k T) ∘ f = pl T := rfl
        exact IsLocallyRigid.of_comp_of_tangent (p := pl (insert k T)) (f := f) (i₀ := k')
          hrange (hcomp ▸ hT) (u := ⟨i, by simpa using hi⟩) (w := ⟨j, by simpa using hj⟩) hki hkj
          (A.center_injective.ne hij)
  refine grow _ {a, b} (by simp) rfl ?_
  refine isLocallyRigid_of_forall_tangent fun v w hvw => ?_
  have hv := v.2
  have hw := w.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  have hvw' : v.1 ≠ w.1 := fun e => hvw (Subtype.ext e)
  show dist (A.center v.1) (A.center w.1) = 2
  rcases hv with hv | hv <;> rcases hw with hw | hw <;> rw [hv, hw] at hvw' ⊢
  · exact absurd rfl hvw'
  · exact hab
  · exact tangent_comm.mp hab
  · exact absurd rfl hvw'

end Arrangement

end RigidArrangements

#print axioms RigidArrangements.Arrangement.isLattice_of_triGrown
#print axioms RigidArrangements.Arrangement.isRigid_of_grown_pair
