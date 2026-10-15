import RigidArrangements.LemmaE
import RigidArrangements.SixCorners
import RigidArrangements.Small
import RigidArrangements.LatticeCert

/-!
# Rigid cores of seven and eight circles: the flower

This file proves **Theorem\*** of `docs/cores.md` (Section 4) and draws its consequences for the
classification.

The **flower** (`Arrangement.flower`) is a hexagon of six circles around a seventh: circle `0`
is centered at `0` and circle `k + 1` at `2ρᵏ`, where `ρ = e^{iπ/3}` (`RigidArrangements.rho`).
In lattice coordinates it is `ofLattice flowerSites`. It is rigid (a build order of Henneberg
steps) and it is a core: every circle has at least three contacts, so none is removable.

**Theorem\*.** Let `A` be an arrangement of `n` circles, `7 ≤ n ≤ 8`, in which every circle
touches at least two others and no circle is removable. Then `n = 7` and `A` is isomorphic to
the flower. More generally `1 ≤ n ≤ 8` is enough (Remark 1 of `docs/cores.md`).

## The proof

Let `e₀, …, e₅` be the six different circles extreme in the directions `k · 60°` (the hull lemma
`Arrangement.exists_injective_isExtreme`). A *corner* is a circle extreme in some direction
(`Arrangement.IsCorner`); a corner touches exactly three circles
(`Arrangement.IsCorner.touchesExactlyThree`).

* **Case A: some corner `x` is not among the `eₖ`.** Then at least seven circles are corners,
  so at most one is not.
  * If some circle `r` is not a corner, every other circle is a corner, so by **Lemma E**
    (`Arrangement.adj_of_forall_ne_isCorner`) the seven corners all touch `r`. But no circle
    touches more than six others (`Arrangement.ncard_neighborSet_le_six`).
  * If every circle is a corner, Lemma E with `r = x` says that the six circles `eₖ` touch `x`.
    But the corner `x` touches only three circles.
* **Case B: the corners are exactly the `eₖ`.** This is setting S6 of `docs/cores.md`, and
  there are at most two non-corners. **Lemma S** (`Arrangement.exists_isSixCornerFrame`) and
  **Proposition H** (`Arrangement.IsSixCornerFrame.exists_hub_of_few`) give a circle `o`, not a
  corner, with `eₖ = o + 2ζρᵏ` for a unit complex number `ζ`, and each `eₖ` touches only `o`
  and its two neighbours on the hexagon.
  * Any further circle `d` would touch two circles that are not corners (a corner touches no
    circle besides `o` and two corners), so `d` and its two neighbours would be three
    non-corners.
  * So the circles are exactly `o, e₀, …, e₅`, and `z ↦ o + ζz` carries the flower onto `A`.

## Counts

For rigid arrangements, Theorem\* says that the flower is the only rigid core of seven circles
and that there is no rigid core of eight circles. With the `LatticeCover` machinery of
`RigidArrangements.Small` this completes the classification up to eight circles.

* Seven circles: every rigid arrangement either has a removable circle, and is then an extension
  of one of the three six-circle shapes, or it is the flower, which enters as a core
  (`LatticeCover.succ_of_cores`). The kernel checks that every extension, and the flower, matches
  an entry of `latticeCatalogue7` up to a lattice symmetry; that the four entries are pairwise
  non-isomorphic comes from the key check in `card_rigidClasses_eq_of_latticeCover`.
* Eight circles: every rigid arrangement has a removable circle, and the kernel checks that every
  extension of a seven-circle shape matches an entry of `latticeCatalogue8`; the nine entries are
  pairwise non-isomorphic by the same key check.

So there are exactly `4` rigid arrangements of seven circles and `9` of eight circles, up to
isomorphism, and all of them lie on the triangular lattice. For comparison, there are `4`
pentiamonds and `12` hexiamonds (OEIS A000577): the counts agree with the numbers of
polyiamonds with `n - 2` triangles up to `n = 7` and differ at `n = 8`.

The kernel checks (`decide +kernel`) are dominated by the extension checks `coverStep`: a few
seconds from six to seven circles and about ten seconds from seven to eight circles. The flower
check, the build certificates and the keys take well under a second each.

## Main results

* `flowerSites`, `Arrangement.flower`, `Arrangement.flower_center_zero`,
  `Arrangement.flower_center_succ`: the flower.
* `Arrangement.flower_isRigid`, `Arrangement.flower_isCore`: the flower is a rigid core.
* `Arrangement.card_eq_seven_and_iso_flower_of_card_le_eight`,
  `Arrangement.card_eq_seven_and_iso_flower` (**Theorem\***).
* `Arrangement.IsRigid.card_eq_seven_and_iso_flower`, `Arrangement.IsRigid.iso_flower_of_isCore`,
  `noCoresBetween_eight_eight`: the rigid corollaries (C7) and (C8).
* `latticeCover_seven`, `latticeCover_eight`, `card_rigidClasses_seven`,
  `card_rigidClasses_eight`: exactly `4` and `9` rigid arrangements of seven and eight circles.
* `Arrangement.IsRigid.isLattice_of_card_le_eight`: rigid arrangements of at most eight circles
  lie on the triangular lattice.
-/

namespace RigidArrangements

/-! ### The flower -/

/-- The flower in lattice coordinates: the origin, then its six neighbours in counterclockwise
order, starting from `(1, 0)`. -/
def flowerSites : List (ℤ × ℤ) :=
  [(0, 0), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

/-- The points of `flowerSites` are distinct. -/
theorem flowerSites_nodup : flowerSites.Nodup := by
  decide

namespace Arrangement

/-- The **flower**: six circles in a hexagon around a seventh. Circle `0` is centered at `0`
(`flower_center_zero`) and circle `k + 1` at `2ρᵏ` (`flower_center_succ`). -/
noncomputable def flower : Arrangement (Fin 7) :=
  ofLattice flowerSites flowerSites_nodup

/-- The middle circle of the flower is centered at `0`. -/
theorem flower_center_zero : flower.center 0 = 0 := by
  apply Complex.ext <;> simp [flower, ofLattice, latticePoint, flowerSites]

/-- The outer circles of the flower are centered at `2ρᵏ`, `k = 0, …, 5`. -/
theorem flower_center_succ (k : Fin 6) : flower.center k.succ = 2 * rho ^ (k : ℕ) := by
  have h4 : rho ^ 4 = -rho := by
    rw [pow_succ, rho_pow_three]
    ring
  have h5 : rho ^ 5 = 1 - rho := by
    rw [pow_succ, h4, neg_mul, ← sq, rho_sq]
    ring
  change latticePoint (flowerSites.get k.succ) = _
  fin_cases k <;> apply Complex.ext <;>
    simp [latticePoint, flowerSites, rho_sq, rho_pow_three, h4, h5] <;> ring

/-- The flower is rigid: in the order of `flowerSites`, each circle after the first two touches
two earlier ones (the middle circle and the previous outer circle). -/
theorem flower_isRigid : flower.IsRigid :=
  isRigid_ofLattice_of_latticeBuilt _ (by decide)

/-- Every circle of the flower touches three others. -/
private theorem flower_three_neighbours : ∀ w : Fin 7, ∃ a b c : Fin 7, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    eNorm (flowerSites.get w - flowerSites.get a) = 1 ∧
    eNorm (flowerSites.get w - flowerSites.get b) = 1 ∧
    eNorm (flowerSites.get w - flowerSites.get c) = 1 := by
  decide +kernel

/-- The flower is a core: every circle touches at least three others, so none is
removable. -/
theorem flower_isCore : flower.IsCore := by
  rintro w ⟨u, v, -, hadj, -⟩
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := flower_three_neighbours w
  have key : ∀ x : Fin 7, eNorm (flowerSites.get w - flowerSites.get x) = 1 → x = u ∨ x = v :=
    fun x hx => (hadj x).mp ⟨fun h => by simp [h, eNorm] at hx,
      (tangent_ofLattice_iff flowerSites_nodup w x).mpr hx⟩
  rcases key a ha with rfl | rfl <;> rcases key b hb with rfl | rfl <;>
    rcases key c hc with rfl | rfl <;> simp_all

/-! ### Theorem\* -/

variable {ι : Type*} {A : Arrangement ι}

/-- `m` different neighbours of `i` give at least `m` neighbours. -/
private theorem le_ncard_neighborSet [Finite ι] {i : ι} {m : ℕ} {f : Fin m → ι}
    (hf : Function.Injective f) (h : ∀ k, A.contactGraph.Adj i (f k)) :
    m ≤ (A.contactGraph.neighborSet i).ncard := by
  have := Set.ncard_le_ncard (s := Set.range f) (t := A.contactGraph.neighborSet i)
    (by rintro _ ⟨k, rfl⟩; exact h k)
  rwa [Set.ncard_range_of_injective hf, Nat.card_fin] at this

/-- Six different circles `e₀, …, e₅` and three more circles, different from them and from each
other, make at least nine circles. -/
private theorem nine_le_card [Finite ι] {e : Fin 6 → ι} (he : Function.Injective e) {a b c : ι}
    (ha : a ∉ Set.range e) (hb : b ∉ Set.range e) (hc : c ∉ Set.range e) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : 9 ≤ Nat.card ι := by
  have hf : Function.Injective
      (Fin.cons a (Fin.cons b (Fin.cons c e : Fin 7 → ι) : Fin 8 → ι) : Fin 9 → ι) := by
    simp only [Fin.cons_injective_iff, Fin.range_cons, Set.mem_insert_iff, not_or]
    exact ⟨⟨hab, hac, ha⟩, ⟨hbc, hb⟩, hc, he⟩
  simpa using Nat.card_le_card_of_injective _ hf

/-- **Theorem\***, general form (Remark 1 of `docs/cores.md`). Let `A` be a nonempty arrangement
of at most eight circles in which every circle touches at least two others and no circle is
removable. Then `A` has exactly seven circles and is isomorphic to the flower. In particular
there is no such arrangement of one to six circles, or of eight circles. -/
theorem card_eq_seven_and_iso_flower_of_card_le_eight [Finite ι] [Nonempty ι]
    (hT : A.TouchesTwo) (hc : A.IsCore) (h8 : Nat.card ι ≤ 8) :
    Nat.card ι = 7 ∧ A.Iso flower := by
  obtain ⟨e, he, hext⟩ := A.exists_injective_isExtreme hT hc
  have hnC : ∀ {i}, ¬ A.IsCorner i → i ∉ Set.range e := by
    rintro i hi ⟨k, rfl⟩
    exact hi (hext k).isCorner
  by_cases hA : ∃ x, A.IsCorner x ∧ x ∉ Set.range e
  · -- Case A: a seventh corner `x`
    exfalso
    obtain ⟨x, hx, hxe⟩ := hA
    by_cases hr : ∃ r, ¬ A.IsCorner r
    · -- `r` is the only non-corner, and the seven corners all touch it
      obtain ⟨r, hr⟩ := hr
      have hall : ∀ i, i ≠ r → A.IsCorner i := by
        intro b hbr
        by_contra hb
        have := nine_le_card he (hnC hr) (hnC hb) hxe (Ne.symm hbr) (fun h => hr (h ▸ hx))
          (fun h => hb (h ▸ hx))
        omega
      have hcorner : ∀ k, A.IsCorner ((Fin.cons x e : Fin 7 → ι) k) := fun k =>
        Fin.cases (by simpa using hx) (fun k => by simpa using (hext k).isCorner) k
      have h7 := le_ncard_neighborSet (A := A) (i := r)
        (Fin.cons_injective_iff.mpr ⟨hxe, he⟩) fun k =>
          (adj_of_forall_ne_isCorner hT hc hall fun h => hr (h ▸ hcorner k)).symm
      have := A.ncard_neighborSet_le_six r
      omega
    · -- every circle is a corner, so the six `eₖ` touch the corner `x`
      push Not at hr
      have h6 := le_ncard_neighborSet (A := A) (i := x) he fun k =>
        (adj_of_forall_ne_isCorner hT hc (r := x) (fun i _ => hr i) fun h => hxe ⟨k, h⟩).symm
      rw [(hx.touchesExactlyThree hT hc).ncard_neighborSet] at h6
      omega
  · -- Case B: the corners are exactly the `eₖ`
    push Not at hA
    obtain ⟨ω, L, hF⟩ := exists_isSixCornerFrame hT hc he hext hA
    have hfew : ∀ a b c : ι, ¬ A.IsCorner a → ¬ A.IsCorner b → ¬ A.IsCorner c →
        a = b ∨ a = c ∨ b = c := by
      intro a b c ha hb hc'
      by_contra h
      push Not at h
      have := nine_le_card he (hnC ha) (hnC hb) (hnC hc') h.1 h.2.1 h.2.2
      omega
    obtain ⟨o, ho, -, honly, hcen⟩ := hF.exists_hub_of_few hfew
    -- the circles are exactly `o, e₀, …, e₅`
    have hinj : Function.Injective (Fin.cons o e : Fin 7 → ι) :=
      Fin.cons_injective_iff.mpr ⟨hnC ho, he⟩
    have hsurj : Function.Surjective (Fin.cons o e : Fin 7 → ι) := by
      intro d
      by_contra hd
      push Not at hd
      have hdo : d ≠ o := fun h => hd 0 (by simp [h])
      have hde : ∀ k, d ≠ e k := fun k h => hd k.succ (by simp [h])
      have hdC : ¬ A.IsCorner d := fun h => by
        obtain ⟨k, rfl⟩ := hA d h
        exact hde k rfl
      -- the neighbours of `d` are not corners
      have hnb : ∀ j, A.contactGraph.Adj d j → ¬ A.IsCorner j := by
        intro j hj hjC
        obtain ⟨k, rfl⟩ := hA j hjC
        rcases honly k d hj.symm with h | h | h
        · exact hde _ h
        · exact hde _ h
        · exact hdo h
      obtain ⟨j, k, hjk, hdj, hdk, htj, htk⟩ := hT d
      rcases hfew d j k hdC (hnb j ⟨hdj, htj⟩) (hnb k ⟨hdk, htk⟩) with h | h | h
      · exact hdj h
      · exact hdk h
      · exact hjk h
    have hbij : Function.Bijective (Fin.cons o e : Fin 7 → ι) := ⟨hinj, hsurj⟩
    refine ⟨by rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fin], ?_⟩
    -- `z ↦ o + ζ z` carries the flower onto `A`
    have hζ : ‖ω * rho ^ 4‖ = 1 := by
      rw [norm_mul, norm_pow, norm_rho, one_pow, mul_one, hF.norm_eq_one]
    have hiso : Isometry fun z : Plane => A.center o + ω * rho ^ 4 * z :=
      Isometry.of_dist_eq fun z w => by
        rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hζ,
          one_mul]
    refine (Iso.of_isometry hiso (Equiv.ofBijective _ hbij) fun i => ?_).symm
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [flower_center_zero]
    · rw [Equiv.ofBijective_apply, Fin.cons_succ, flower_center_succ, hcen k]
      ring

/-- **Theorem\*** (`docs/cores.md`, Section 4). Let `A` be an arrangement of seven or eight
circles in which every circle touches at least two others and no circle is removable. Then `A`
has exactly seven circles and is isomorphic to the flower. -/
theorem card_eq_seven_and_iso_flower [Finite ι] (hT : A.TouchesTwo) (hc : A.IsCore)
    (h7 : 7 ≤ Nat.card ι) (h8 : Nat.card ι ≤ 8) : Nat.card ι = 7 ∧ A.Iso flower := by
  have : Nonempty ι := (Nat.card_pos_iff.mp (by omega)).1
  exact card_eq_seven_and_iso_flower_of_card_le_eight hT hc h8

/-- **Rigid cores of seven or eight circles.** A rigid core of seven or eight circles has seven
circles and is isomorphic to the flower. -/
theorem IsRigid.card_eq_seven_and_iso_flower [Finite ι] (h : A.IsRigid) (hc : A.IsCore)
    (h7 : 7 ≤ Nat.card ι) (h8 : Nat.card ι ≤ 8) : Nat.card ι = 7 ∧ A.Iso flower :=
  Arrangement.card_eq_seven_and_iso_flower (h.touchesTwo (by omega)) hc h7 h8

/-- **(C7)** Every rigid core of seven circles is isomorphic to the flower. -/
theorem IsRigid.iso_flower_of_isCore {A : Arrangement (Fin 7)} (h : A.IsRigid)
    (hc : A.IsCore) : A.Iso flower :=
  (h.card_eq_seven_and_iso_flower hc (by simp) (by simp)).2

end Arrangement

open Arrangement

/-- **(C8)** No rigid arrangement of eight circles is a core: each one has a removable
circle. -/
theorem noCoresBetween_eight_eight : NoCoresBetween 8 8 := by
  intro n A h8 h8' hA
  by_contra h
  have := (hA.card_eq_seven_and_iso_flower (fun w hw => h ⟨w, hw⟩)
    (by rw [Nat.card_fin]; omega) (by rw [Nat.card_fin]; omega)).1
  rw [Nat.card_fin] at this
  omega

/-! ### Counts -/

/-- **Seven circles.** Every rigid arrangement of seven circles is isomorphic to one of the four
entries of `latticeCatalogue7`: it is an extension of a six-circle shape by a removable circle,
or it is the flower. -/
theorem latticeCover_seven : LatticeCover 7 latticeCatalogue7 :=
  (latticeCover_six noCoresBetween_four_six).succ_of_cores (C := [flowerSites])
    (fun A hA => by
      by_cases h : ∃ w, A.Removable w
      · exact Or.inl h
      · exact Or.inr ⟨flowerSites, List.mem_singleton_self _, flowerSites_nodup,
          hA.iso_flower_of_isCore fun w hw => h ⟨w, hw⟩⟩)
    (by decide +kernel) (by decide +kernel)

/-- **Eight circles.** Every rigid arrangement of eight circles is isomorphic to one of the nine
entries of `latticeCatalogue8`: it has a removable circle, so it is an extension of a
seven-circle shape. -/
theorem latticeCover_eight : LatticeCover 8 latticeCatalogue8 :=
  latticeCover_seven.succ (fun A hA => noCoresBetween_eight_eight 8 A le_rfl le_rfl hA)
    (by decide +kernel)

/-- **There are exactly four rigid arrangements of seven circles**, up to isomorphism. -/
theorem card_rigidClasses_seven : ENat.card (RigidClasses 7) = 4 := by
  rw [card_rigidClasses_eq_of_latticeCover latticeCover_seven (by decide +kernel)
    (by decide +kernel)]
  rfl

/-- **There are exactly nine rigid arrangements of eight circles**, up to isomorphism. -/
theorem card_rigidClasses_eight : ENat.card (RigidClasses 8) = 9 := by
  rw [card_rigidClasses_eq_of_latticeCover latticeCover_eight (by decide +kernel)
    (by decide +kernel)]
  rfl

/-- **Rigid arrangements of at most eight circles lie on the triangular lattice.** -/
theorem Arrangement.IsRigid.isLattice_of_card_le_eight {n : ℕ} (hn : n ≤ 8)
    {A : Arrangement (Fin n)} (hA : A.IsRigid) : A.IsLattice := by
  rcases (show n ≤ 6 ∨ n = 7 ∨ n = 8 by omega) with h | rfl | rfl
  · exact hA.isLattice_of_le_six noCoresBetween_four_six h
  · exact latticeCover_seven.isLattice hA
  · exact latticeCover_eight.isLattice hA

end RigidArrangements
