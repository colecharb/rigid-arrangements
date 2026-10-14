import RigidArrangements.Henneberg
import RigidArrangements.InfRigid
import RigidArrangements.Isometry
import RigidArrangements.Lattice

/-!
# Certified lower bounds for the counts, from lattice build certificates

This file turns explicit lists of points of the triangular lattice into theorems of the form
"there are at least `k` rigid arrangements of `n` circles, up to isomorphism". An arrangement
on the lattice is given by a list of lattice points (`Arrangement.ofLattice`). Everything we
need to know about it is integer arithmetic, so the Lean kernel checks it with `decide`.

* **Rigidity, by a build certificate.** `checkBuild l` asks that the first two points of `l`
  touch, and that every later point touches at least two distinct earlier points. Reading `l`
  in order then builds the arrangement from two touching circles by Henneberg steps (adding a
  circle that touches two circles), and each step keeps rigidity
  (`IsLocallyRigid.of_comp_of_tangent`). So the arrangement is rigid
  (`isLocallyRigid_of_checkBuild`). A step may put the new circle exactly between two circles
  `4` apart (a *straight* step): the Henneberg step needs no hypothesis on that distance.
* **Non-isomorphism, by an invariant.** Isomorphic arrangements have the same pairwise
  distances after relabeling. For lattice points the squared distance is `4` times the
  `eNorm` of the difference, so the *distance profile* (`latticeProfile`) is an isomorphism
  invariant (`latticeProfile_eq_of_iso`). It records, for each circle, the multiset of the
  `eNorm`s to all circles, and then the multiset of these multisets over all circles. To keep
  `decide` fast we compare a single integer computed from the profile, the *profile key*
  `Σ_v (Σ_w eNorm (v - w) ^ 2) ^ 3` (`profileKey`). Different keys mean different profiles,
  hence non-isomorphic arrangements.
* **Counting.** A *certified catalogue* (`IsCertifiedCatalogue n C`) is a list `C` of lists of
  `n` distinct lattice points, each with a build certificate, whose profile keys strictly
  increase along `C`. Its entries are `C.length` pairwise non-isomorphic rigid arrangements of
  `n` circles, so `C.length ≤ ENat.card (RigidClasses n)`
  (`IsCertifiedCatalogue.le_card_rigidClasses`).

## The catalogue

`latticeCatalogue3`, …, `latticeCatalogue12` list, for `3 ≤ n ≤ 12`, one representative of each
class of rigid lattice arrangements of `n` circles found by the exploratory enumerations (the
closure of the triangle under Henneberg steps on the lattice, computed in Lean). Each entry is
written in build order, starting at `(0, 0)`, and the entries are sorted by profile key. The
kernel checks that each catalogue is certified, which gives the lower bounds

| `n`      | 3 | 4 | 5 | 6 | 7 | 8 | 9  | 10 | 11 | 12  |
|----------|---|---|---|---|---|---|----|----|----|-----|
| at least | 1 | 1 | 1 | 3 | 4 | 9 | 16 | 35 | 69 | 155 |

These are only lower bounds. Nothing here says that the catalogue lists *all* rigid lattice
arrangements, and from `n = 11` on there are also rigid arrangements off the lattice.

The numbers are not those of polyiamonds. The numbers of polyiamonds with `1, …, 8`
triangles are `1, 1, 1, 3, 4, 12, 24, 66` (OEIS A000577), and they agree with the catalogue
(with `n - 2` triangles for `n` circles) only up to `n = 7`. For `n = 8` the catalogue has `9`
entries against `12` hexiamonds: according to the exploratory enumerations, the hexagon
hexiamond has only `7` corners (the same as the fan of `5` triangles), and three hexiamonds
share one set of `8` corners.

The kernel checks take about `10` seconds for `n = 12`, `4` seconds for `n = 11` and under `2`
seconds for each smaller `n`, mostly spent computing profile keys.

## Two special arrangements

* `Arrangement.sing18`: 18 circles, rigid (its build certificate ends with a straight step)
  but not infinitesimally rigid: its last circle sits exactly between two circles `4` apart
  and touches nothing else, so it can move sideways to first order (`not_isInfRigid_of_taut`).
* `Arrangement.r13`: 13 circles, rigid, and its circle at `(3, 0)`, next to the empty site
  `(2, 0)`, lies in no triangle of mutually touching circles: no two of its neighbours touch.
  It is the only such circle. So `r13` is not a union of triangles.

## Main results

* `checkBuild`, `isLocallyRigid_of_checkBuild`, `Arrangement.isRigid_ofLattice_of_checkBuild`:
  build certificates and their soundness.
* `latticeProfile`, `latticeProfile_eq_of_iso`, `profileKey`, `profileKey_eq_of_iso`: the
  isomorphism invariant.
* `IsCertifiedCatalogue`, `IsCertifiedCatalogue.isRigid_arr`,
  `IsCertifiedCatalogue.not_iso_arr`, `IsCertifiedCatalogue.le_card_rigidClasses`.
* `latticeCatalogue3`, …, `latticeCatalogue12`, and `latticeCatalogue_certified_three`, …,
  `latticeCatalogue_certified_twelve` (checked by `decide +kernel`).
* `le_card_rigidClasses_three`, …, `le_card_rigidClasses_twelve`: the lower bounds above.
* `Arrangement.sing18_isRigid`, `Arrangement.sing18_not_isInfRigid`.
* `Arrangement.r13_isRigid`, `Arrangement.r13_not_tangent_of_tangent`,
  `Arrangement.r13_forall_not_tangent_iff`.
-/

namespace RigidArrangements

/-! ### Build certificates -/

/-- The build check read backwards: the *newest* point comes first. A list `v :: S` with at
least two points in `S` passes when `S` passes and `v` touches two distinct points of `S`. A
list of two points passes when they touch. Shorter lists fail. -/
def checkBuildRev : List (ℤ × ℤ) → Bool
  | [] => false
  | [_] => false
  | [v, a] => eNorm (v - a) == 1
  | v :: x :: y :: T => checkBuildRev (x :: y :: T) &&
      (x :: y :: T).any fun u => eNorm (v - u) == 1 &&
        (x :: y :: T).any fun w => u != w && eNorm (v - w) == 1

/-- **Build certificate.** `checkBuild l` holds when `l` has at least two points, the first two
points touch, and every later point touches at least two distinct earlier points. Then the
arrangement of circles at the points of `l` is rigid (`isLocallyRigid_of_checkBuild`). The two
earlier points may be opposite neighbours of the new point (a straight step). -/
def checkBuild (l : List (ℤ × ℤ)) : Bool :=
  checkBuildRev l.reverse

/-- Soundness of `checkBuildRev`: read from the end, the list builds a rigid placement. -/
theorem isLocallyRigid_of_checkBuildRev :
    ∀ l : List (ℤ × ℤ), checkBuildRev l = true →
      IsLocallyRigid fun i : Fin l.length => latticePoint (l.get i)
  | [], h | [_], h => by simp [checkBuildRev] at h
  | [a, b], h => by
    have hab : dist (latticePoint a) (latticePoint b) = 2 :=
      (tangent_latticePoint_iff a b).2 (by simpa [checkBuildRev] using h)
    refine isLocallyRigid_of_forall_tangent fun i j hij => ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [Tangent] using hab
    · simpa [Tangent, dist_comm] using hab
    · exact absurd rfl hij
  | v :: x :: y :: T, h => by
    simp only [checkBuildRev, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨hS, u, hu, hvu, w, hw, huw, hvw⟩ := h
    obtain ⟨i, rfl⟩ := List.get_of_mem hu
    obtain ⟨j, rfl⟩ := List.get_of_mem hw
    exact IsLocallyRigid.of_comp_of_tangent (f := Fin.succ) (i₀ := 0) (Fin.range_succ _).ge
      (isLocallyRigid_of_checkBuildRev _ hS) (u := i) (w := j)
      ((tangent_latticePoint_iff _ _).2 hvu) ((tangent_latticePoint_iff _ _).2 hvw)
      fun he => huw (latticePoint_injective he)

/-- **Soundness of build certificates.** If `checkBuild l` holds, the circles at the lattice
points of `l` form a locally rigid placement: the list describes a sequence of Henneberg steps
starting from two touching circles. -/
theorem isLocallyRigid_of_checkBuild {l : List (ℤ × ℤ)} (h : checkBuild l = true) :
    IsLocallyRigid fun i : Fin l.length => latticePoint (l.get i) := by
  let e : Fin l.reverse.length ≃ Fin l.length := (finCongr List.length_reverse).trans Fin.revPerm
  rw [← isLocallyRigid_comp_equiv_iff e]
  convert isLocallyRigid_of_checkBuildRev _ h using 1
  funext i
  simp only [Function.comp_apply, List.get_eq_getElem, List.getElem_reverse]
  congr 2
  simp [e, Fin.rev]
  omega

namespace Arrangement

/-- **A build certificate proves rigidity** of a lattice arrangement. -/
theorem isRigid_ofLattice_of_checkBuild {l : List (ℤ × ℤ)} (hl : l.Nodup)
    (h : checkBuild l = true) : (ofLattice l hl).IsRigid :=
  isLocallyRigid_of_checkBuild h

/-- `ofLattice l hl`, with its circles numbered by `Fin n` instead of `Fin l.length`, where
`n = l.length`. -/
noncomputable def ofLatticeFin (l : List (ℤ × ℤ)) (hl : l.Nodup) {n : ℕ} (hn : l.length = n) :
    Arrangement (Fin n) :=
  (ofLattice l hl).comap (finCongr hn.symm) (finCongr hn.symm).injective

/-- Renumbering the circles gives an isomorphic arrangement. -/
theorem ofLatticeFin_iso (l : List (ℤ × ℤ)) (hl : l.Nodup) {n : ℕ} (hn : l.length = n) :
    (ofLatticeFin l hl hn).Iso (ofLattice l hl) :=
  ⟨finCongr hn.symm, Congruent.refl _⟩

/-- **A build certificate proves rigidity**, with the circles numbered by `Fin n`. -/
theorem isRigid_ofLatticeFin_of_checkBuild {l : List (ℤ × ℤ)} (hl : l.Nodup) {n : ℕ}
    (hn : l.length = n) (h : checkBuild l = true) : (ofLatticeFin l hl hn).IsRigid :=
  (ofLatticeFin_iso l hl hn).symm.isRigid (isRigid_ofLattice_of_checkBuild hl h)

end Arrangement

/-! ### An isomorphism invariant -/

/-- If two families of lattice points are congruent (same pairwise distances), they have the
same `eNorm`s of differences, since the squared distance is `4` times the `eNorm`. -/
theorem eNorm_sub_eq_of_congruent {ι : Type*} {p q : ι → ℤ × ℤ}
    (h : Congruent (latticePoint ∘ p) (latticePoint ∘ q)) (i j : ι) :
    eNorm (p i - p j) = eNorm (q i - q j) := by
  have hp := dist_latticePoint_sq (p i) (p j)
  have hq := dist_latticePoint_sq (q i) (q j)
  rw [show dist (latticePoint (p i)) (latticePoint (p j)) =
    dist (latticePoint (q i)) (latticePoint (q j)) from h.dist_eq i j, hq] at hp
  have : (eNorm (p i - p j) : ℝ) = eNorm (q i - q j) := by linarith
  exact_mod_cast this

/-- The *distance profile* of a list `l` of lattice points. For each point `v` of `l` take the
multiset of the numbers `eNorm (v - w)` (a quarter of the squared distance), `w` running over
`l`; the profile is the multiset of these multisets, `v` running over `l`. It does not depend
on the order of `l`, and isomorphic arrangements have equal profiles
(`latticeProfile_eq_of_iso`). -/
def latticeProfile (l : List (ℤ × ℤ)) : Multiset (Multiset ℤ) :=
  ↑(l.map fun v => (↑(l.map fun w => eNorm (v - w)) : Multiset ℤ))

/-- The multiset of the values of `g` on a list, as a sum over its positions. -/
private theorem coe_map_eq_map_univ {α β : Type*} (l : List α) (g : α → β) :
    ((l.map g : List β) : Multiset β) =
      (Finset.univ : Finset (Fin l.length)).val.map (g ∘ l.get) := by
  rw [Fin.univ_val_map, ← List.map_ofFn, List.ofFn_get]

/-- Reindexing a multiset of values over a finite type along an equivalence. -/
private theorem map_univ_val_comp_equiv {α β γ : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : β → γ) :
    (Finset.univ : Finset α).val.map (f ∘ e) = (Finset.univ : Finset β).val.map f := by
  rw [← Finset.map_univ_equiv e, Finset.map_val, Multiset.map_map]
  rfl

/-- The distance profile, indexed by the positions in the list. -/
theorem latticeProfile_eq_map_univ (l : List (ℤ × ℤ)) :
    latticeProfile l = (Finset.univ : Finset (Fin l.length)).val.map fun i =>
      (Finset.univ : Finset (Fin l.length)).val.map fun j => eNorm (l.get i - l.get j) := by
  simp only [latticeProfile, coe_map_eq_map_univ]
  rfl

/-- **The distance profile is an isomorphism invariant.** If the lattice arrangements of `l`
and `l'` are isomorphic, they have the same distance profile. -/
theorem latticeProfile_eq_of_iso {l l' : List (ℤ × ℤ)} {hl : l.Nodup} {hl' : l'.Nodup}
    (h : (Arrangement.ofLattice l hl).Iso (Arrangement.ofLattice l' hl')) :
    latticeProfile l = latticeProfile l' := by
  obtain ⟨e, he⟩ := h
  have hd : ∀ i j, eNorm (l.get i - l.get j) = eNorm (l'.get (e i) - l'.get (e j)) :=
    eNorm_sub_eq_of_congruent (p := l.get) (q := l'.get ∘ e) he
  rw [latticeProfile_eq_map_univ, latticeProfile_eq_map_univ]
  simp only [hd]
  rw [← map_univ_val_comp_equiv e]
  congr 1
  funext i
  exact map_univ_val_comp_equiv e fun j => eNorm (l'.get (e i) - l'.get j)

/-- The *profile key* `Σ_v (Σ_w eNorm (v - w) ^ 2) ^ 3` of a list of lattice points: a single
integer computed from the distance profile. Comparing keys is much faster for `decide` than
comparing profiles; different keys mean different profiles. -/
def profileKey (l : List (ℤ × ℤ)) : ℤ :=
  ((latticeProfile l).map fun m => (m.map (· ^ 2)).sum ^ 3).sum

/-- **The profile key is an isomorphism invariant.** -/
theorem profileKey_eq_of_iso {l l' : List (ℤ × ℤ)} {hl : l.Nodup} {hl' : l'.Nodup}
    (h : (Arrangement.ofLattice l hl).Iso (Arrangement.ofLattice l' hl')) :
    profileKey l = profileKey l' := by
  rw [profileKey, profileKey, latticeProfile_eq_of_iso h]

/-! ### Certified catalogues -/

/-- A *certified catalogue* of rigid lattice arrangements of `n` circles: every entry of `C` is a
list of `n` distinct lattice points with a build certificate, and the profile keys of the
entries strictly increase along `C`. Hence the entries are rigid and pairwise non-isomorphic.
This is decidable, so `decide` can check it. -/
def IsCertifiedCatalogue (n : ℕ) (C : List (List (ℤ × ℤ))) : Prop :=
  (∀ l ∈ C, l.length = n ∧ l.Nodup ∧ checkBuild l = true) ∧ (C.map profileKey).IsChain (· < ·)

instance (n : ℕ) (C : List (List (ℤ × ℤ))) : Decidable (IsCertifiedCatalogue n C) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace IsCertifiedCatalogue

variable {n : ℕ} {C : List (List (ℤ × ℤ))} (hC : IsCertifiedCatalogue n C)
include hC

/-- The arrangement of `n` circles at the points of the `i`-th entry of the catalogue. -/
noncomputable def arr (i : Fin C.length) : Arrangement (Fin n) :=
  Arrangement.ofLatticeFin (C.get i) (hC.1 _ (List.get_mem C i)).2.1
    (hC.1 _ (List.get_mem C i)).1

/-- Every entry of a certified catalogue is rigid. -/
theorem isRigid_arr (i : Fin C.length) : (hC.arr i).IsRigid :=
  Arrangement.isRigid_ofLatticeFin_of_checkBuild _ _ (hC.1 _ (List.get_mem C i)).2.2

/-- Profile keys strictly increase along a certified catalogue. -/
theorem profileKey_lt {i j : Fin C.length} (hij : i < j) :
    profileKey (C.get i) < profileKey (C.get j) := by
  have h := List.isChain_iff_pairwise.1 hC.2
  rw [List.pairwise_map] at h
  exact List.pairwise_iff_get.1 h i j hij

/-- **Distinct entries of a certified catalogue are not isomorphic.** -/
theorem not_iso_arr {i j : Fin C.length} (hij : i ≠ j) : ¬ (hC.arr i).Iso (hC.arr j) := by
  intro h
  have h' := (Arrangement.ofLatticeFin_iso _ _ _).symm.trans
    (h.trans (Arrangement.ofLatticeFin_iso _ _ _))
  have hk := profileKey_eq_of_iso h'
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact (hC.profileKey_lt hlt).ne hk
  · exact (hC.profileKey_lt hlt).ne' hk

/-- **A certified catalogue gives a lower bound** for the number of rigid arrangements of `n`
circles up to isomorphism. -/
theorem le_card_rigidClasses : (C.length : ℕ∞) ≤ ENat.card (RigidClasses n) := by
  let f : Fin C.length → RigidClasses n := fun i =>
    Quotient.mk (RigidArr.isoSetoid n) ⟨hC.arr i, hC.isRigid_arr i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hC.not_iso_arr hne (Quotient.exact hij)
  have h := ENat.card_le_card_of_injective hf
  rwa [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h

/-- `le_card_rigidClasses`, with the length of the catalogue given explicitly. -/
theorem le_card_rigidClasses_of_length {k : ℕ} (hk : C.length = k) :
    (k : ℕ∞) ≤ ENat.card (RigidClasses n) :=
  hk ▸ hC.le_card_rigidClasses

end IsCertifiedCatalogue

/-! ### The catalogue -/

/-- A list of lattice points: the identity function. Writing `pts [...]` for each entry of a
catalogue gives Lean the type of the entry up front, which makes elaborating the long lists
below several times faster. -/
private abbrev pts (l : List (ℤ × ℤ)) : List (ℤ × ℤ) := l

/-- The catalogue of rigid lattice arrangements of `3` circles (1 entry), each in
build order, sorted by profile key. -/
def latticeCatalogue3 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0)]]

/-- The catalogue of rigid lattice arrangements of `4` circles (1 entry), each in
build order, sorted by profile key. -/
def latticeCatalogue4 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1)]]

/-- The catalogue of rigid lattice arrangements of `5` circles (1 entry), each in
build order, sorted by profile key. -/
def latticeCatalogue5 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2)]]

/-- The catalogue of rigid lattice arrangements of `6` circles (3 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue6 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2)]]

/-- The catalogue of rigid lattice arrangements of `7` circles (4 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue7 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3)]]

/-- The catalogue of rigid lattice arrangements of `8` circles (9 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue8 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3)]]

/-- The catalogue of rigid lattice arrangements of `9` circles (16 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue9 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4)]]

/-- The catalogue of rigid lattice arrangements of `10` circles (35 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue10 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, 0), (3, -2), (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (3, -2), (3, -3), (2, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4)]]

/-- The catalogue of rigid lattice arrangements of `11` circles (69 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue11 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (3, -1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (2, 0), (2, 1), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (2, 0), (2, 1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, 0), (3, -1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (3, -1), (3, -2), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2), (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (3, -2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (3, -1), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, -1), (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1), (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, 0), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, 0),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (3, -2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 0), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, 1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (3, -2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 1), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (3, 0), (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, 0),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, 0), (3, -2), (3, -3),
    (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 1), (2, 2), (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (3, 0), (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2), (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3),
    (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, 0), (4, -1), (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (4, -2), (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (3, -2),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (3, -2), (3, -3),
    (2, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (1, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (1, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4), (0, 5)]]

/-- The catalogue of rigid lattice arrangements of `12` circles (155 entries), each in
build order, sorted by profile key. -/
def latticeCatalogue12 : List (List (ℤ × ℤ)) := [
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (2, 0), (2, 1), (3, -1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, -2),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (2, 2),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 0), (2, 1),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 0), (3, -1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 0), (2, 1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (3, -1), (3, -2),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (3, 0),
    (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (2, 1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (2, 2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (3, 0), (3, -1),
    (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, 0), (2, 1),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (3, 0),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, 0), (3, -1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (2, 1),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (2, 2),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (2, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 0), (2, 1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0),
    (3, -3), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, -1), (3, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, 0), (2, 1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (3, 0),
    (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, 0), (2, 1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (3, -1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 1), (3, -2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, -1), (2, 1), (1, 2), (2, 2), (1, 3), (0, 3),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (3, -1), (3, -2), (3, 0),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, 0),
    (3, -2), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (2, 0), (2, 1), (3, 0),
    (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, 0), (2, 1), (1, 2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (1, 2), (2, 2), (1, 3), (0, 3), (3, 0),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, 1), (2, 2),
    (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, -1), (3, 1),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (2, -2), (3, 0),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 0), (2, 1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, 0),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2), (3, 0),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (3, -1), (3, -2), (3, 0),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, -2),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, -1), (2, 1), (1, 2), (2, 2), (1, 3), (0, 3),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 1), (2, 2), (3, 1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 1), (2, 2),
    (3, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, 0),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2), (2, -2),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3),
    (3, -1), (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3), (3, -1),
    (4, -2), (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (3, -2), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (2, 0), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, 0),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, 0), (2, 1), (1, 2), (2, 2), (1, 3), (0, 3),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (3, -2),
    (3, -1), (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, -1), (3, 1),
    (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0), (3, -1),
    (3, 0), (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (3, -2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1),
    (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2), (4, -2),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, 0),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, 1),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, 0), (3, -1), (3, -2),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (3, 0), (4, -2),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 0),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, 1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, 0), (3, -1), (3, -2), (4, -2),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (3, 0), (4, -1),
    (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, -1), (4, -1),
    (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (2, 1), (3, -1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3),
    (4, -3), (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, 0),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1), (3, 0),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, 1), (2, 2),
    (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1), (3, -2),
    (3, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 0),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 1), (2, 2),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (3, -2),
    (3, -3), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -2), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, 0), (3, -1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, 0), (4, -1), (4, -2),
    (4, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, 0),
    (3, -3), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, -4),
    (3, -2), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, -1),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, -4),
    (2, 0), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, -1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, -4),
    (2, 0), (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3), (2, 0),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3), (3, -1),
    (4, -3), (4, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, -4),
    (2, 0), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 0),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (3, -2), (3, -3),
    (2, -3), (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1), (3, -2),
    (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (2, 1),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, 0), (3, -2), (3, -3),
    (4, -3), (4, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -3), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (2, 0), (3, -2), (3, -3), (2, -3),
    (4, -3), (4, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (3, 0), (4, -2),
    (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, 1), (2, 2), (3, 1),
    (3, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (3, -2),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (3, -3), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, 1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (2, 1), (3, -1), (3, -2), (4, -2),
    (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (1, -2),
    (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (3, -2),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3), (2, -4),
    (2, 0), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (2, -4), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (2, -1), (3, -1), (3, -2), (4, -2), (4, -3),
    (4, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, -2),
    (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (1, -2),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, -2),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 0), (2, -1),
    (3, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (2, -4), (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (1, -3), (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, -1),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (3, -2), (3, -3),
    (4, -3), (4, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (3, -2),
    (3, -3), (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (2, 0), (2, -1), (3, -1), (3, -2),
    (4, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (2, 1), (2, 2), (1, 3), (2, 3), (1, 4),
    (0, 4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, -1),
    (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (3, -2), (3, -3), (2, -3),
    (4, -3), (4, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, -1),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0),
    (4, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, -2),
    (2, 2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (1, -3), (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (1, -2),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (3, -3),
    (3, -4), (2, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (3, -2), (3, -3),
    (2, -3), (4, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (3, -2), (3, -3),
    (2, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (1, -2), (2, -3), (1, -3),
    (2, -4), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, 2),
    (2, 3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (2, -1), (2, -2), (3, -2), (3, -3), (4, -3),
    (4, -4), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, -2),
    (3, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4), (0, 5),
    (2, 1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4),
    (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (1, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, -1), (2, -2),
    (1, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (1, -2), (2, -3),
    (3, -3), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (2, -1), (2, -2), (3, -2), (3, -3),
    (2, -3), (3, -4)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (3, -2),
    (3, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4), (0, 5),
    (2, 0)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4),
    (2, -1)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (2, -1), (2, -2), (1, -2),
    (2, -3)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (2, -1),
    (2, -2)],
  pts [(0, 0), (0, 1), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4),
    (0, 5)]]

/-- The number of entries of `latticeCatalogue3`, …, `latticeCatalogue12`. -/
theorem latticeCatalogue_lengths :
    [latticeCatalogue3.length, latticeCatalogue4.length, latticeCatalogue5.length,
      latticeCatalogue6.length, latticeCatalogue7.length, latticeCatalogue8.length,
      latticeCatalogue9.length, latticeCatalogue10.length, latticeCatalogue11.length,
      latticeCatalogue12.length] = [1, 1, 1, 3, 4, 9, 16, 35, 69, 155] := by
  decide +kernel

/-! ### Kernel checks of the catalogue

Each theorem below says: every entry of the catalogue is a list of `n` distinct lattice points
with a build certificate (so it is rigid), and the profile keys strictly increase (so distinct
entries are not isomorphic). The kernel checks this by evaluation. -/

/-- The catalogue for `3` circles is certified. -/
theorem latticeCatalogue_certified_three : IsCertifiedCatalogue 3 latticeCatalogue3 := by
  decide +kernel

/-- The catalogue for `4` circles is certified. -/
theorem latticeCatalogue_certified_four : IsCertifiedCatalogue 4 latticeCatalogue4 := by
  decide +kernel

/-- The catalogue for `5` circles is certified. -/
theorem latticeCatalogue_certified_five : IsCertifiedCatalogue 5 latticeCatalogue5 := by
  decide +kernel

/-- The catalogue for `6` circles is certified. -/
theorem latticeCatalogue_certified_six : IsCertifiedCatalogue 6 latticeCatalogue6 := by
  decide +kernel

/-- The catalogue for `7` circles is certified. -/
theorem latticeCatalogue_certified_seven : IsCertifiedCatalogue 7 latticeCatalogue7 := by
  decide +kernel

/-- The catalogue for `8` circles is certified. -/
theorem latticeCatalogue_certified_eight : IsCertifiedCatalogue 8 latticeCatalogue8 := by
  decide +kernel

/-- The catalogue for `9` circles is certified. -/
theorem latticeCatalogue_certified_nine : IsCertifiedCatalogue 9 latticeCatalogue9 := by
  decide +kernel

/-- The catalogue for `10` circles is certified. -/
theorem latticeCatalogue_certified_ten : IsCertifiedCatalogue 10 latticeCatalogue10 := by
  decide +kernel

/-- The catalogue for `11` circles is certified. -/
theorem latticeCatalogue_certified_eleven : IsCertifiedCatalogue 11 latticeCatalogue11 := by
  decide +kernel

/-- The catalogue for `12` circles is certified. -/
theorem latticeCatalogue_certified_twelve : IsCertifiedCatalogue 12 latticeCatalogue12 := by
  decide +kernel

/-! ### Lower bounds for the counts -/

/-- There is at least one rigid arrangement of `3` circles, up to isomorphism: the triangle. -/
theorem le_card_rigidClasses_three : (1 : ℕ∞) ≤ ENat.card (RigidClasses 3) := by
  simpa using latticeCatalogue_certified_three.le_card_rigidClasses_of_length (k := 1) rfl

/-- There is at least one rigid arrangement of `4` circles, up to isomorphism. -/
theorem le_card_rigidClasses_four : (1 : ℕ∞) ≤ ENat.card (RigidClasses 4) := by
  simpa using latticeCatalogue_certified_four.le_card_rigidClasses_of_length (k := 1) rfl

/-- There is at least one rigid arrangement of `5` circles, up to isomorphism. -/
theorem le_card_rigidClasses_five : (1 : ℕ∞) ≤ ENat.card (RigidClasses 5) := by
  simpa using latticeCatalogue_certified_five.le_card_rigidClasses_of_length (k := 1) rfl

/-- There are at least `3` rigid arrangements of `6` circles, up to isomorphism. -/
theorem le_card_rigidClasses_six : (3 : ℕ∞) ≤ ENat.card (RigidClasses 6) := by
  simpa using latticeCatalogue_certified_six.le_card_rigidClasses_of_length (k := 3) rfl

/-- There are at least `4` rigid arrangements of `7` circles, up to isomorphism. -/
theorem le_card_rigidClasses_seven : (4 : ℕ∞) ≤ ENat.card (RigidClasses 7) := by
  simpa using latticeCatalogue_certified_seven.le_card_rigidClasses_of_length (k := 4) rfl

/-- There are at least `9` rigid arrangements of `8` circles, up to isomorphism. -/
theorem le_card_rigidClasses_eight : (9 : ℕ∞) ≤ ENat.card (RigidClasses 8) := by
  simpa using latticeCatalogue_certified_eight.le_card_rigidClasses_of_length (k := 9) rfl

/-- There are at least `16` rigid arrangements of `9` circles, up to isomorphism. -/
theorem le_card_rigidClasses_nine : (16 : ℕ∞) ≤ ENat.card (RigidClasses 9) := by
  simpa using latticeCatalogue_certified_nine.le_card_rigidClasses_of_length (k := 16) rfl

/-- There are at least `35` rigid arrangements of `10` circles, up to isomorphism. -/
theorem le_card_rigidClasses_ten : (35 : ℕ∞) ≤ ENat.card (RigidClasses 10) := by
  simpa using latticeCatalogue_certified_ten.le_card_rigidClasses_of_length (k := 35) rfl

/-- There are at least `69` rigid arrangements of `11` circles, up to isomorphism. -/
theorem le_card_rigidClasses_eleven : (69 : ℕ∞) ≤ ENat.card (RigidClasses 11) := by
  simpa using latticeCatalogue_certified_eleven.le_card_rigidClasses_of_length (k := 69) rfl

/-- There are at least `155` rigid arrangements of `12` circles, up to isomorphism. -/
theorem le_card_rigidClasses_twelve : (155 : ℕ∞) ≤ ENat.card (RigidClasses 12) := by
  simpa using latticeCatalogue_certified_twelve.le_card_rigidClasses_of_length (k := 155) rfl

/-! ### A rigid arrangement that is not infinitesimally rigid -/

/-- Two lattice points `v`, `w` with `eNorm (v - w) = 4` are `4` apart. -/
private theorem dist_latticePoint_eq_four {v w : ℤ × ℤ} (h : eNorm (v - w) = 4) :
    dist (latticePoint v) (latticePoint w) = 4 := by
  have hsq := dist_latticePoint_sq v w
  rw [h] at hsq
  have h0 := dist_nonneg (x := latticePoint v) (y := latticePoint w)
  push_cast at hsq
  nlinarith

/-- The `18` lattice points of `Arrangement.sing18`, in build order. The last one, `(1, 0)`, is
added by a straight step between `(0, 0)` and `(2, 0)`. -/
def sing18Points : List (ℤ × ℤ) :=
  [(-1, 1), (0, 0), (-1, 0), (-2, 1), (-2, 2), (-1, 2), (-2, 3), (-1, 3), (0, 2), (0, 3),
    (1, 2), (1, 3), (2, 2), (2, 1), (3, 1), (3, 0), (2, 0), (1, 0)]

/-- The points of `sing18Points` are distinct. -/
theorem sing18Points_nodup : sing18Points.Nodup := by
  decide +kernel

namespace Arrangement

/-- **`sing18`**: an arrangement of `18` circles on the lattice that is rigid but not
infinitesimally rigid. The first `17` circles form a rigid cluster in which the circles at
`(0, 0)` and `(2, 0)` (circles `1` and `16`) are `4` apart. The last circle, at `(1, 0)`,
sits between them, touching only those two. -/
noncomputable def sing18 : Arrangement (Fin 18) :=
  ofLattice sing18Points sing18Points_nodup

/-- **`sing18` is rigid**: it has a build certificate, whose last step is straight. -/
theorem sing18_isRigid : sing18.IsRigid :=
  isRigid_ofLattice_of_checkBuild sing18Points_nodup (by decide +kernel)

/-- Tangency in `sing18`, in lattice coordinates. -/
theorem sing18_tangent_iff_eNorm (a b : Fin 18) :
    Tangent sing18.center a b ↔ eNorm (sing18Points.get a - sing18Points.get b) = 1 :=
  tangent_ofLattice_iff sing18Points_nodup a b

/-- The last circle of `sing18` touches exactly the circles `1` and `16`. -/
theorem sing18_tangent_iff (k : Fin 18) : Tangent sing18.center 17 k ↔ k = 1 ∨ k = 16 := by
  rw [sing18_tangent_iff_eNorm]
  revert k
  decide +kernel

/-- The circles `1` and `16` of `sing18`, at `(0, 0)` and `(2, 0)`, are `4` apart. -/
theorem sing18_dist_one_sixteen : dist (sing18.center 1) (sing18.center 16) = 4 :=
  dist_latticePoint_eq_four (by decide +kernel)

/-- **`sing18` is not infinitesimally rigid**: its last circle can move sideways to first
order. Together with `sing18_isRigid`, this shows that infinitesimal rigidity is strictly
stronger than rigidity, already for arrangements on the lattice. -/
theorem sing18_not_isInfRigid : ¬ IsInfRigid sing18.center :=
  RigidArrangements.not_isInfRigid_of_taut (w := 17) (fun k hk => (sing18_tangent_iff k).1 hk)
    ((sing18_tangent_iff 1).2 (Or.inl rfl)) ((sing18_tangent_iff 16).2 (Or.inr rfl))
    sing18_dist_one_sixteen

end Arrangement

/-! ### A rigid arrangement with a circle in no triangle -/

/-- The `13` lattice points of `Arrangement.r13`, in build order. The site `(2, 0)` is empty;
the last point, `(3, 0)`, touches `(3, -1)` and `(2, 1)` only. -/
def r13Points : List (ℤ × ℤ) :=
  [(0, 1), (0, 0), (1, 0), (1, -1), (1, 1), (0, 2), (1, 2), (2, -1), (2, -2), (2, 1), (3, -2),
    (3, -1), (3, 0)]

/-- The points of `r13Points` are distinct. -/
theorem r13Points_nodup : r13Points.Nodup := by
  decide +kernel

namespace Arrangement

/-- **`r13`**: a rigid arrangement of `13` circles on the lattice, around the empty site
`(2, 0)`, whose circle `12` (at `(3, 0)`) lies in no triangle of mutually touching circles. -/
noncomputable def r13 : Arrangement (Fin 13) :=
  ofLattice r13Points r13Points_nodup

/-- **`r13` is rigid**: it has a build certificate. -/
theorem r13_isRigid : r13.IsRigid :=
  isRigid_ofLattice_of_checkBuild r13Points_nodup (by decide +kernel)

/-- Tangency in `r13`, in lattice coordinates. -/
theorem r13_tangent_iff_eNorm (a b : Fin 13) :
    Tangent r13.center a b ↔ eNorm (r13Points.get a - r13Points.get b) = 1 :=
  tangent_ofLattice_iff r13Points_nodup a b

/-- **Circle `12` is the only circle of `r13` that lies in no triangle**: it is the only circle
`i` such that no two circles touching `i` touch each other. -/
theorem r13_forall_not_tangent_iff (i : Fin 13) :
    (∀ j k, Tangent r13.center i j → Tangent r13.center i k → ¬ Tangent r13.center j k) ↔
      i = 12 := by
  simp only [r13_tangent_iff_eNorm]
  revert i
  decide +kernel

/-- **The circle of `r13` at the gap lies in no triangle**: no two neighbours of circle `12`
(at `(3, 0)`, next to the empty site `(2, 0)`) touch each other. -/
theorem r13_not_tangent_of_tangent {j k : Fin 13} (hj : Tangent r13.center 12 j)
    (hk : Tangent r13.center 12 k) : ¬ Tangent r13.center j k :=
  (r13_forall_not_tangent_iff 12).2 rfl j k hj hk

end Arrangement

end RigidArrangements
