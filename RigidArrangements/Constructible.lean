import RigidArrangements.Cluster
import RigidArrangements.Small

/-!
# Constructible arrangements, the Henneberg step, and the smallest emergent arrangement

`RigidArrangements.Cluster` makes "these circles do not move relative to one another" into the
predicate `Arrangement.RigidIn` and proves the merging rules R1, R2, R3. This file asks which
clusters those rules actually *produce* when one starts from nothing but the contacts, and
answers the question the census raises: a rigid arrangement that the rules cannot assemble is
called *emergent*, and the smallest emergent arrangement is a core.

## Constructibility

`Arrangement.Constructible A S` is an inductive predicate: `S` is a cluster that the calculus
*derives*, starting from the **atoms** — the tangent pairs — and closing under R1, R2 and R3.
`Arrangement.Constructible.rigidIn` is soundness: a derived set really is a cluster.

The restriction to atoms is the whole content of the definition and must not be relaxed. It is
tempting to allow a rigid sub-arrangement to be fed in as a "body", since
`Arrangement.rigidIn_of_comap` says bodies are clusters; but taking the body to be the whole
arrangement (`f = id`) would then make *every* rigid arrangement constructible in one step and
emergence vacuous. Bodies are legitimate only when they have themselves been derived, which is
what `Arrangement.Constructible.image_comap` below provides.

## The replay principle

`Arrangement.Constructible.image_comap`: a derivation inside a sub-arrangement is a derivation
inside the ambient arrangement. Along an injection `f`, a derivation of `S` in `A.comap f`
becomes a derivation of `f '' S` in `A`. The proof is an induction on the derivation and is
mechanical in the exact sense that there is no geometry in it: an atom transfers because
tangency is a statement about centers and `(A.comap f).center = A.center ∘ f`, and each rule is
a statement about the ambient arrangement already, so the images of the shared circles serve as
the shared circles of the image rule. Injectivity is used only to keep the shared circles
distinct.

## The Henneberg step

`Arrangement.RigidIn.henneberg`: if `S` is a cluster and a circle `w` touches two distinct
circles of `S`, then `insert w S` is a cluster. This is one application of R2 to `S`, `{w, a}`
and `{w, b}`, whose pairwise intersections contain the three distinct circles `a`, `w`, `b`.
`Arrangement.Constructible.henneberg` is the same step at the level of derivations.

Two things are *not* assumed. Nothing about `dist (A.center a) (A.center b)`: the **collinear**
(straight) Henneberg step, where `a`, `w`, `b` are in a line, is covered on the same footing as
the bent one, because R2 needs no non-degeneracy. And `w ∉ S` is not assumed either — `w ≠ a`
and `w ≠ b` come free from tangency, and that is all R2 wants. The hypothesis
`dist (A.center u) (A.center v) < 4` in `Arrangement.Removable` belongs to the *reverse*
direction, where a circle is taken away; see `RigidArrangements.Core`.

## The smallest emergent arrangement is a core

`Arrangement.Emergent A` is `A.IsRigid ∧ ¬ A.Constructible Set.univ`. The theorem
(`Arrangement.isCore_of_least_emergent`) is a minimal-counterexample argument, and "smallest"
means fewest circles:

> let `A` be emergent on `n` circles with `n` least; if `A` were not a core it would have a
> removable circle `w`; peeling `w` leaves a rigid arrangement on `n - 1` circles, which is
> constructible because `n` was least; replaying that derivation inside `A` and adding one
> Henneberg step for `w` makes `A` constructible, a contradiction.

A peel drops the number of circles by **exactly** one — `Arrangement.comap w.succAbove` turns an
arrangement on `Fin (k + 1)` into one on `Fin k` — which is what makes the induction on `n` go
through. Note what the argument does *not* use: no canonical core, and so no confluence of
peeling. One peel and one Henneberg step suffice.

`Arrangement.constructible_univ_of_isRigid_of_cores` is the form the census needs: if every
rigid *core* with at most `N` circles is constructible, then so is every rigid arrangement with
at most `N` circles. This is what turns "no emergent arrangement below `n = 20`" from a
heuristic into a complete answer: only cores have to be examined.

The census enumerates arrangements *on the lattice*, and its verdict is about those. Since a
sub-arrangement of a lattice arrangement is again one (`Arrangement.IsLattice.comap`), the peel
never leaves the lattice and every statement here has a lattice counterpart with the same proof:
`Arrangement.constructible_univ_of_isRigid_of_lattice_cores`,
`Arrangement.no_emergent_iff_no_emergent_lattice_core` and
`Arrangement.isCore_of_least_emergent_lattice`. Those are the ones to point at the census; the
unrestricted versions quantify over off-lattice arrangements too, which no census has covered.

## The two degenerate sizes

`n ≥ 2` is a real restriction, not a convenience.

* Every derivation produces at least two circles (`Arrangement.Constructible.exists_ne`), so for
  one circle or none the closure of the atoms is *empty* and nothing at all is constructible
  (`Arrangement.not_constructible_of_subsingleton`). Such an arrangement is vacuously rigid, so
  it is emergent (`Arrangement.emergent_of_card_le_one`) and would otherwise be the smallest
  emergent arrangement, which is why the least is taken over `n ≥ 2`.
* At `n = 2` nothing has to be stipulated: a rigid pair is a tangent pair
  (`Arrangement.isRigid_two_iff`), and a tangent pair is an atom, so it is constructible
  (`Arrangement.constructible_univ_of_isRigid_two`). Both circles are also a core
  (`Arrangement.isCore_of_card_le_two`), since a removable circle brings three distinct circles
  with it.

The census declares every arrangement of at most two circles constructible by fiat. The line
above says what that convention is worth: at `n = 2` it is a theorem, and at `n ≤ 1` it is a
genuine convention with no content behind it. Either way the counts the census reports for
`n ≥ 2` are the counts of this file's predicate.

## Adding R4

R4 — two clusters joined by three contacts whose lines are neither all concurrent nor all
parallel — is not part of the calculus yet. When it arrives it is a one-constructor change in
three places and nowhere else: a constructor `r4` on `Arrangement.Constructible`, a case in
`Arrangement.Constructible.rigidIn` discharged by the new library lemma, and a case in
`Arrangement.Constructible.image_comap` transferring its three bars along `f`. Every result
after those three — the Henneberg step, the peel, and the theorem on the smallest emergent
arrangement — is stated in terms of `Constructible` alone and does not mention the rules.

## Main results

* `Arrangement.RigidIn.henneberg`, `Arrangement.isRigid_of_rigidIn_henneberg`,
  `Arrangement.isRigid_of_erase_cluster`: the Henneberg step for clusters.
* `Arrangement.Constructible`, `Arrangement.Constructible.rigidIn`: the calculus and soundness.
* `Arrangement.Constructible.image_comap`, `Arrangement.Constructible.range_comap`: replay.
* `Arrangement.Constructible.henneberg`, `Arrangement.Removable.henneberg_data`,
  `Arrangement.Removable.isRigid_of_peel`,
  `Arrangement.Removable.constructible_univ_of_peel`: the round trip across one removable circle.
* `Arrangement.constructible_univ_of_isRigid_of_cores`,
  `Arrangement.no_emergent_iff_no_emergent_core`,
  `Arrangement.isCore_of_emergent_of_minimal`, `Arrangement.isCore_of_least_emergent`.
* `Arrangement.IsLattice.comap`,
  `Arrangement.constructible_univ_of_isRigid_of_lattice_cores`,
  `Arrangement.no_emergent_iff_no_emergent_lattice_core`,
  `Arrangement.isCore_of_least_emergent_lattice`: the same, on the lattice.
* `Arrangement.triangle_constructible`: the calculus derives something, so soundness is not
  vacuous.
-/

open Filter Topology

namespace RigidArrangements

namespace Arrangement

variable {ι κ : Type*}

/-! ## The Henneberg step for clusters -/

/-- A tangency joins two *distinct* circles: the centers are `2` apart, and a center is at
distance `0` from itself. -/
theorem ne_of_tangent {A : Arrangement ι} {x y : ι} (h : Tangent A.center x y) : x ≠ y := by
  intro he
  have : (2 : ℝ) = 0 := by rw [← h, he, dist_self]
  norm_num at this

/-- **The Henneberg step for clusters.** If `S` is a cluster of `A` and the circle `w` touches
two distinct circles `a`, `b` of `S`, then `insert w S` is a cluster of `A`.

This is R2 (`Arrangement.RigidIn.union_of_ring`) on the three clusters `S`, `{w, a}`, `{w, b}`,
whose pairwise intersections contain the three distinct circles `a`, `w`, `b`.

Note what is **not** assumed: nothing about `dist (A.center a) (A.center b)`, so the *collinear*
(straight) Henneberg step is covered on the same footing as the bent one, and `w` may touch any
number of further circles of `S`. Nor is `w ∉ S` needed; `w ≠ a` and `w ≠ b` are free from
tangency, and only `a ≠ b` is a real hypothesis. -/
theorem RigidIn.henneberg [Finite ι] {A : Arrangement ι} {S : Set ι} (hS : A.RigidIn S)
    {w a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hwa : Tangent A.center w a) (hwb : Tangent A.center w b) :
    A.RigidIn (insert w S) := by
  have hwa' : w ≠ a := ne_of_tangent hwa
  have hwb' : w ≠ b := ne_of_tangent hwb
  have h2 : A.RigidIn ({w, a} : Set ι) := rigidIn_pair hwa
  have h3 : A.RigidIn ({w, b} : Set ι) := rigidIn_pair hwb
  refine (hS.union_of_ring h2 h3 (c₁ := w) (c₂ := b) (c₃ := a)
    ⟨ha, by simp⟩ ⟨by simp, by simp⟩ ⟨hb, by simp⟩ hwb' hwa' hab.symm).mono ?_
  intro x hx
  simp only [Set.mem_insert_iff] at hx
  rcases hx with rfl | hx
  · exact Or.inl (Or.inr (by simp))
  · exact Or.inl (Or.inl hx)

/-- **The Henneberg step, cashed in.** If the circles other than `w` form a cluster and `w`
touches two distinct ones of them, the whole arrangement is rigid. -/
theorem isRigid_of_rigidIn_henneberg [Finite ι] {A : Arrangement ι} {S : Set ι}
    (hS : A.RigidIn S) {w a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hwa : Tangent A.center w a) (hwb : Tangent A.center w b)
    (hcov : ∀ i, i ≠ w → i ∈ S) : A.IsRigid := by
  rw [← rigidIn_univ_iff]
  refine (hS.henneberg ha hb hab hwa hwb).mono ?_
  intro i _
  by_cases h : i = w
  · exact Or.inl h
  · exact Or.inr (hcov i h)

/-- The library's Henneberg step (`Arrangement.IsRigid.of_erase`) re-proved from the cluster
calculus, confirming that `Arrangement.RigidIn.henneberg` really is that step and not something
weaker. -/
theorem isRigid_of_erase_cluster [Finite ι] {A : Arrangement (Option ι)}
    (h : A.erase.IsRigid) {u v : ι}
    (hu : Tangent A.center none (some u)) (hv : Tangent A.center none (some v))
    (huv : u ≠ v) : A.IsRigid := by
  have hbody : A.RigidIn (Set.range (some : ι → Option ι)) :=
    A.rigidIn_of_comap some (Option.some_injective ι) h
  refine isRigid_of_rigidIn_henneberg hbody (w := none) (a := some u) (b := some v)
    ⟨u, rfl⟩ ⟨v, rfl⟩ (by simpa using huv) hu hv ?_
  intro i hi
  cases i with
  | none => exact absurd rfl hi
  | some j => exact ⟨j, rfl⟩

/-! ## Constructible clusters -/

/-- **The clusters the calculus derives.** `Constructible A S` says that `S` is obtained from the
*atoms* of `A` — its tangent pairs — by the merging rules R1, R2 and R3.

Only atoms seed the derivation. A rigid sub-arrangement is a cluster
(`Arrangement.rigidIn_of_comap`), but admitting one as a starting point would be fatal: taking
it to be the whole arrangement makes every rigid arrangement constructible at once. A body may
be used once it has itself been derived, which is `Arrangement.Constructible.image_comap`.

The four constructors mirror `Arrangement.rigidIn_pair`, `Arrangement.RigidIn.union_of_two`,
`Arrangement.RigidIn.union_of_ring` and `Arrangement.RigidIn.union_chain` hypothesis for
hypothesis, so soundness is one line per rule. -/
inductive Constructible (A : Arrangement ι) : Set ι → Prop where
  /-- **An atom.** A tangent pair is a cluster. -/
  | atom {x y : ι} (hxy : Tangent A.center x y) : Constructible A {x, y}
  /-- **R1.** Two derived clusters sharing two distinct circles `a`, `b` merge. -/
  | r1 {S T : Set ι} (hS : Constructible A S) (hT : Constructible A T) {a b : ι}
      (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) (hab : a ≠ b) :
      Constructible A (S ∪ T)
  /-- **R2.** Three derived clusters pairwise sharing a circle, the three shared circles `c₁`,
  `c₂`, `c₃` being distinct, merge. -/
  | r2 {S₁ S₂ S₃ : Set ι} (h₁ : Constructible A S₁) (h₂ : Constructible A S₂)
      (h₃ : Constructible A S₃) {c₁ c₂ c₃ : ι}
      (h12 : c₃ ∈ S₁ ∩ S₂) (h23 : c₁ ∈ S₂ ∩ S₃) (h13 : c₂ ∈ S₁ ∩ S₃)
      (h₁₂ : c₁ ≠ c₂) (h₁₃ : c₁ ≠ c₃) (h₂₃ : c₂ ≠ c₃) :
      Constructible A (S₁ ∪ S₂ ∪ S₃)
  /-- **R3.** A taut chain of `k` contacts whose ends lie in a derived cluster and are exactly
  `2 * k` apart merges into that cluster. -/
  | r3 {S : Set ι} (hS : Constructible A S) {k : ℕ} (hk : 0 < k) (w : ℕ → ι)
      (h0 : w 0 ∈ S) (hkS : w k ∈ S)
      (hstep : ∀ i < k, Tangent A.center (w i) (w (i + 1)))
      (hlen : dist (A.center (w 0)) (A.center (w k)) = 2 * k) :
      Constructible A (S ∪ w '' Set.Iic k)

/-- **Soundness of the calculus.** A derived set really is a cluster. One case per rule, each
discharged by the matching lemma of `RigidArrangements.Cluster`. -/
theorem Constructible.rigidIn [Finite ι] {A : Arrangement ι} {S : Set ι}
    (h : A.Constructible S) : A.RigidIn S := by
  induction h with
  | atom hxy => exact rigidIn_pair hxy
  | r1 _ _ haS haT hbS hbT hab ih₁ ih₂ => exact ih₁.union_of_two ih₂ haS haT hbS hbT hab
  | r2 _ _ _ h12 h23 h13 h₁₂ h₁₃ h₂₃ ih₁ ih₂ ih₃ =>
      exact ih₁.union_of_ring ih₂ ih₃ h12 h23 h13 h₁₂ h₁₃ h₂₃
  | r3 _ hk w h0 hkS hstep hlen ih => exact ih.union_chain hk w h0 hkS hstep hlen

/-- A derived cluster has at least two circles: the atoms do, and every rule only grows a
cluster it is given. So the closure of the atoms is empty in an arrangement of fewer than two
circles. -/
theorem Constructible.exists_ne {A : Arrangement ι} {S : Set ι} (h : A.Constructible S) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
  induction h with
  | atom hxy => exact ⟨_, by simp, _, by simp, ne_of_tangent hxy⟩
  | r1 _ _ _ _ _ _ _ ih₁ _ =>
      obtain ⟨x, hx, y, hy, hxy⟩ := ih₁
      exact ⟨x, Or.inl hx, y, Or.inl hy, hxy⟩
  | r2 _ _ _ _ _ _ _ _ _ ih₁ _ _ =>
      obtain ⟨x, hx, y, hy, hxy⟩ := ih₁
      exact ⟨x, Or.inl (Or.inl hx), y, Or.inl (Or.inl hy), hxy⟩
  | r3 _ _ _ _ _ _ _ ih =>
      obtain ⟨x, hx, y, hy, hxy⟩ := ih
      exact ⟨x, Or.inl hx, y, Or.inl hy, hxy⟩

/-- **Nothing is constructible in an arrangement of at most one circle**: there is no contact,
hence no atom, hence no derivation. This is why the smallest emergent arrangement has to be
sought among arrangements of at least two circles. -/
theorem not_constructible_of_subsingleton [Subsingleton ι] {A : Arrangement ι} {S : Set ι} :
    ¬ A.Constructible S := by
  intro h
  obtain ⟨x, _, y, _, hxy⟩ := h.exists_ne
  exact hxy (Subsingleton.elim x y)

/-! ## The replay principle -/

/-- **Replay.** A derivation inside a sub-arrangement is a derivation inside the ambient
arrangement: along an injection `f`, a derivation of `S` in `A.comap f` becomes a derivation of
`f '' S` in `A`.

There is no geometry in the proof. An atom transfers because tangency depends only on centers
and `(A.comap f).center = A.center ∘ f`; each rule is a statement about the ambient arrangement
to begin with, so the images of the circles it shares, chains and anchors serve for the image
rule. Injectivity of `f` enters only to keep shared circles distinct. -/
theorem Constructible.image_comap {A : Arrangement ι} {f : κ → ι}
    {hf : Function.Injective f} {S : Set κ} (h : (A.comap f hf).Constructible S) :
    A.Constructible (f '' S) := by
  induction h with
  | atom hxy =>
      rw [Set.image_pair]
      exact Constructible.atom hxy
  | r1 _ _ haS haT hbS hbT hab ih₁ ih₂ =>
      rw [Set.image_union]
      exact ih₁.r1 ih₂ ⟨_, haS, rfl⟩ ⟨_, haT, rfl⟩ ⟨_, hbS, rfl⟩ ⟨_, hbT, rfl⟩ (hf.ne hab)
  | r2 _ _ _ h12 h23 h13 h₁₂ h₁₃ h₂₃ ih₁ ih₂ ih₃ =>
      rw [Set.image_union, Set.image_union]
      exact ih₁.r2 ih₂ ih₃ ⟨⟨_, h12.1, rfl⟩, ⟨_, h12.2, rfl⟩⟩ ⟨⟨_, h23.1, rfl⟩, ⟨_, h23.2, rfl⟩⟩
        ⟨⟨_, h13.1, rfl⟩, ⟨_, h13.2, rfl⟩⟩ (hf.ne h₁₂) (hf.ne h₁₃) (hf.ne h₂₃)
  | r3 _ hk w h0 hkS hstep hlen ih =>
      rw [Set.image_union, ← Set.image_comp]
      exact ih.r3 hk (f ∘ w) ⟨_, h0, rfl⟩ ⟨_, hkS, rfl⟩ hstep hlen

/-- **Replay, for a full derivation.** If the sub-arrangement on the circles `f k` derives all
of its circles, then the set of those circles is derived in the ambient arrangement. -/
theorem Constructible.range_comap {A : Arrangement ι} {f : κ → ι}
    {hf : Function.Injective f} (h : (A.comap f hf).Constructible Set.univ) :
    A.Constructible (Set.range f) := by
  rw [← Set.image_univ]
  exact h.image_comap

/-! ## The Henneberg step for derivations -/

/-- **The Henneberg step at the level of derivations.** If `S` is derived and `w` touches two
distinct circles of `S`, then `insert w S` is derived — by one R2 step on `S` and the two atoms
`{w, a}`, `{w, b}`.

As in `Arrangement.RigidIn.henneberg`, nothing is assumed about the distance from `a` to `b`, so
a straight Henneberg step is as good as a bent one, and `w ∉ S` is not required. -/
theorem Constructible.henneberg {A : Arrangement ι} {S : Set ι} (hS : A.Constructible S)
    {w a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hwa : Tangent A.center w a) (hwb : Tangent A.center w b) :
    A.Constructible (insert w S) := by
  have key : A.Constructible (S ∪ ({w, a} : Set ι) ∪ ({w, b} : Set ι)) :=
    hS.r2 (Constructible.atom hwa) (Constructible.atom hwb) (c₁ := w) (c₂ := b) (c₃ := a)
      ⟨ha, by simp⟩ ⟨by simp, by simp⟩ ⟨hb, by simp⟩
      (ne_of_tangent hwb) (ne_of_tangent hwa) hab.symm
  have hset : S ∪ ({w, a} : Set ι) ∪ ({w, b} : Set ι) = insert w S := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ((hx | hx) | hx)
      · exact Set.mem_insert_of_mem _ hx
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ha
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hb
    · rintro x hx
      simp only [Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact Or.inl (Or.inr (by simp))
      · exact Or.inl (Or.inl hx)
  rwa [hset] at key

/-- `Arrangement.Constructible.henneberg` with the union written the other way round. -/
theorem Constructible.henneberg_union {A : Arrangement ι} {S : Set ι} (hS : A.Constructible S)
    {w a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hwa : Tangent A.center w a) (hwb : Tangent A.center w b) :
    A.Constructible (S ∪ {w}) := by
  rw [Set.union_singleton]
  exact hS.henneberg ha hb hab hwa hwb

/-! ## Peeling one removable circle -/

/-- A removable circle brings three distinct circles with it: its two neighbours, and itself.
The contact graph has no loop, so `w` is neither of the two circles it touches. -/
theorem Removable.exists_three {A : Arrangement ι} {w : ι} (hw : A.Removable w) :
    ∃ u v : ι, u ≠ v ∧ w ≠ u ∧ w ≠ v := by
  obtain ⟨u, v, huv, hadj, _⟩ := hw
  refine ⟨u, v, huv, ?_, ?_⟩
  · exact fun he => ((hadj w).2 (Or.inl he)).1 rfl
  · exact fun he => ((hadj w).2 (Or.inr he)).1 rfl

/-- An arrangement with a removable circle has at least three circles. -/
theorem Removable.three_le {n : ℕ} {A : Arrangement (Fin n)} {w : Fin n} (hw : A.Removable w) :
    3 ≤ n := by
  obtain ⟨u, v, huv, hwu, hwv⟩ := hw.exists_three
  have hcard : ({u, v, w} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, Ne.symm hwu]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hwv]), Finset.card_singleton]
  have hle : ({u, v, w} : Finset (Fin n)).card ≤ Fintype.card (Fin n) :=
    Finset.card_le_univ _
  rw [hcard, Fintype.card_fin] at hle
  exact hle

/-- **At most two circles make a core.** A removable circle comes with three distinct circles
(`Arrangement.Removable.exists_three`), so nothing is removable below three circles. -/
theorem isCore_of_card_le_two {n : ℕ} (hn : n ≤ 2) (A : Arrangement (Fin n)) : A.IsCore :=
  fun _ hw => absurd hw.three_le (by omega)

/-- The two contacts of a removable circle, named among the circles that survive the peel. No
rigidity is needed for this half of `Arrangement.Removable.henneberg_data`. -/
theorem Removable.exists_tangent_succAbove {n : ℕ} {A : Arrangement (Fin (n + 1))}
    {w : Fin (n + 1)} (hw : A.Removable w) :
    ∃ a ∈ Set.range w.succAbove, ∃ b ∈ Set.range w.succAbove, a ≠ b ∧
      Tangent A.center w a ∧ Tangent A.center w b := by
  obtain ⟨u, v, huv, hadj, _⟩ := hw
  have hu := (hadj u).2 (Or.inl rfl)
  have hv := (hadj v).2 (Or.inr rfl)
  exact ⟨u, Fin.exists_succAbove_eq hu.1.symm, v, Fin.exists_succAbove_eq hv.1.symm,
    huv, hu.2, hv.2⟩

/-- **The data a peel hands to the Henneberg step.** If `w` is removable in the rigid
arrangement `A`, then the circles other than `w` form a cluster of `A`, and `w` touches two
distinct circles among them — exactly what `Arrangement.RigidIn.henneberg` consumes. So `A` is
reconstructed from the peeled arrangement by one Henneberg step, with no confluence of peeling
used anywhere. -/
theorem Removable.henneberg_data {n : ℕ} {A : Arrangement (Fin (n + 1))}
    {w : Fin (n + 1)} (hw : A.Removable w) (h : A.IsRigid) :
    A.RigidIn (Set.range w.succAbove) ∧
      ∃ a ∈ Set.range w.succAbove, ∃ b ∈ Set.range w.succAbove, a ≠ b ∧
        Tangent A.center w a ∧ Tangent A.center w b :=
  ⟨A.rigidIn_of_comap _ Fin.succAbove_right_injective (hw.isRigid_comap_succAbove h),
    hw.exists_tangent_succAbove⟩

/-- Adding back a removable circle: `insert w` of the circles that survive the peel is
everything. The peel drops the number of circles by exactly one, which is what makes the
induction on the number of circles below go through. -/
theorem insert_range_succAbove {n : ℕ} (w : Fin (n + 1)) :
    insert w (Set.range w.succAbove) = Set.univ := by
  rw [Fin.range_succAbove]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ,
    iff_true]
  exact eq_or_ne x w

/-- **The peel round trip, for rigidity.** If `w` is removable in `A` and the peeled arrangement
is rigid, then `A` is rigid: the peel is a cluster of `A` by `Arrangement.rigidIn_of_comap`, and
one Henneberg step puts `w` back.

This is `Arrangement.IsRigid.of_comap_succAbove` re-proved through the cluster calculus. -/
theorem Removable.isRigid_of_peel {n : ℕ} {A : Arrangement (Fin (n + 1))} {w : Fin (n + 1)}
    (hw : A.Removable w)
    (h : (A.comap w.succAbove Fin.succAbove_right_injective).IsRigid) : A.IsRigid := by
  obtain ⟨a, ha, b, hb, hab, hwa, hwb⟩ := hw.exists_tangent_succAbove
  refine isRigid_of_rigidIn_henneberg
    (A.rigidIn_of_comap _ Fin.succAbove_right_injective h) ha hb hab hwa hwb ?_
  intro i hi
  exact Fin.exists_succAbove_eq hi

/-- **The peel round trip, for constructibility.** If `w` is removable in `A` and the peeled
arrangement derives all of its circles, then `A` derives all of its circles: replay the peel's
derivation inside `A` (`Arrangement.Constructible.range_comap`) and add one Henneberg step for
`w`. -/
theorem Removable.constructible_univ_of_peel {n : ℕ} {A : Arrangement (Fin (n + 1))}
    {w : Fin (n + 1)} (hw : A.Removable w)
    (h : (A.comap w.succAbove Fin.succAbove_right_injective).Constructible Set.univ) :
    A.Constructible Set.univ := by
  obtain ⟨a, ha, b, hb, hab, hwa, hwb⟩ := hw.exists_tangent_succAbove
  have key := (Constructible.range_comap h).henneberg ha hb hab hwa hwb
  rwa [insert_range_succAbove] at key

/-! ## Emergence, and the smallest emergent arrangement -/

/-- **An emergent arrangement**: rigid, but not assembled by the calculus from its contacts. -/
def Emergent (A : Arrangement ι) : Prop :=
  A.IsRigid ∧ ¬ A.Constructible Set.univ

/-- Not being emergent is the implication "rigid, therefore constructible". -/
theorem not_emergent_iff {A : Arrangement ι} :
    ¬ A.Emergent ↔ (A.IsRigid → A.Constructible Set.univ) := by
  rw [Emergent, not_and, not_not]

/-- **The triangle is constructible**, so the calculus derives something and the soundness
theorem is not vacuous: one atom for the contact `0 1`, then one Henneberg step for circle `2`,
which touches both. -/
theorem triangle_constructible : triangle.Constructible Set.univ := by
  have hset : insert (2 : Fin 3) ({0, 1} : Set (Fin 3)) = Set.univ := by
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    fin_cases i <;> simp
  rw [← hset]
  exact (Constructible.atom (triangle_tangent (by decide))).henneberg
    (a := 0) (b := 1) (by simp) (by simp) (by decide)
    (triangle_tangent (by decide)) (triangle_tangent (by decide))

/-- **Two circles are constructible when they are rigid.** A rigid pair is a tangent pair
(`Arrangement.isRigid_two_iff`), and a tangent pair is an atom. So nothing has to be stipulated
at `n = 2`. -/
theorem constructible_univ_of_isRigid_two {A : Arrangement (Fin 2)} (h : A.IsRigid) :
    A.Constructible Set.univ := by
  have hset : ({0, 1} : Set (Fin 2)) = Set.univ := by
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    fin_cases i <;> simp
  rw [← hset]
  exact Constructible.atom (isRigid_two_iff A |>.mp h)

/-- **The degenerate emergence.** An arrangement of at most one circle is rigid and has no
contact at all, so it is emergent for want of any atom. Hence "smallest" in
`Arrangement.isCore_of_least_emergent` must be read among arrangements of at least two
circles. -/
theorem emergent_of_card_le_one {n : ℕ} (hn : n ≤ 1) (A : Arrangement (Fin n)) : A.Emergent := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  exact ⟨A.isRigid_of_subsingleton, not_constructible_of_subsingleton⟩

/-- **Cores decide constructibility.** If every rigid *core* with between `2` and `N` circles is
constructible, then so is every rigid arrangement with between `2` and `N` circles.

The induction is on the number of circles: a rigid arrangement that is not a core has a
removable circle `w`; peeling `w` drops the count by exactly one and leaves a rigid arrangement
(`Arrangement.Removable.isRigid_comap_succAbove`) with at least two circles
(`Arrangement.Removable.three_le`), so the inductive hypothesis derives it, and
`Arrangement.Removable.constructible_univ_of_peel` puts `w` back.

This is what makes a census of cores a complete answer about constructibility. -/
theorem constructible_univ_of_isRigid_of_cores {N : ℕ}
    (hcore : ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsRigid → B.IsCore →
      B.Constructible Set.univ) :
    ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsRigid →
      B.Constructible Set.univ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro B hm2 hmN hB
    by_cases hc : B.IsCore
    · exact hcore m B hm2 hmN hB hc
    · obtain ⟨w, hw⟩ : ∃ w, B.Removable w := by
        simp only [IsCore, not_forall, not_not] at hc
        exact hc
      have h3 : 3 ≤ m := hw.three_le
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact hw.constructible_univ_of_peel
        (ih k (by omega) _ (by omega) (by omega) (hw.isRigid_comap_succAbove hB))

/-- **The census only has to examine cores.** There is no emergent arrangement with between `2`
and `N` circles exactly when there is no emergent *core* in that range.

One direction is a specialization; the other is
`Arrangement.constructible_univ_of_isRigid_of_cores`. -/
theorem no_emergent_iff_no_emergent_core {N : ℕ} :
    (∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → ¬ B.Emergent) ↔
      ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsCore → ¬ B.Emergent := by
  refine ⟨fun h m B hm2 hmN _ => h m B hm2 hmN, fun h m B hm2 hmN => ?_⟩
  rw [not_emergent_iff]
  refine constructible_univ_of_isRigid_of_cores (fun j C hj2 hjN hr hc => ?_) m B hm2 hmN
  exact (not_emergent_iff.mp (h j C hj2 hjN hc)) hr

/-! ### The same statements for arrangements on the lattice

The census enumerates rigid *lattice* arrangements, so this is the form in which its verdict can
be used. Nothing changes in the argument: a sub-arrangement of a lattice arrangement is a
lattice arrangement, so the peel stays on the lattice. -/

/-- A sub-arrangement of a lattice arrangement is on the lattice: the same isometry works, and
the lattice point of a circle `f j` is the one `A` already assigned to it. (The converse, that
putting a removable circle back keeps the lattice, is
`Arrangement.isLattice_of_removable` — that one has content.) -/
theorem IsLattice.comap {A : Arrangement ι} (h : A.IsLattice) {f : κ → ι}
    (hf : Function.Injective f) : (A.comap f hf).IsLattice := by
  obtain ⟨g, F, hF⟩ := h
  exact ⟨g, F ∘ f, fun j => hF (f j)⟩

/-- **Lattice cores decide constructibility on the lattice.** If every rigid lattice *core* with
between `2` and `N` circles is constructible, then so is every rigid lattice arrangement with
between `2` and `N` circles.

This is `Arrangement.constructible_univ_of_isRigid_of_cores` with the hypothesis and the
conclusion both restricted to the lattice, which is what a census of lattice arrangements
supplies and what it is asked for. -/
theorem constructible_univ_of_isRigid_of_lattice_cores {N : ℕ}
    (hcore : ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsRigid → B.IsLattice →
      B.IsCore → B.Constructible Set.univ) :
    ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsRigid → B.IsLattice →
      B.Constructible Set.univ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro B hm2 hmN hB hlat
    by_cases hc : B.IsCore
    · exact hcore m B hm2 hmN hB hlat hc
    · obtain ⟨w, hw⟩ : ∃ w, B.Removable w := by
        simp only [IsCore, not_forall, not_not] at hc
        exact hc
      have h3 : 3 ≤ m := hw.three_le
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact hw.constructible_univ_of_peel
        (ih k (by omega) _ (by omega) (by omega) (hw.isRigid_comap_succAbove hB)
          (hlat.comap Fin.succAbove_right_injective))

/-- **The census only has to examine lattice cores.** There is no emergent lattice arrangement
with between `2` and `N` circles exactly when there is no emergent lattice *core* in that
range. -/
theorem no_emergent_iff_no_emergent_lattice_core {N : ℕ} :
    (∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsLattice → ¬ B.Emergent) ↔
      ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m ≤ N → B.IsLattice → B.IsCore →
        ¬ B.Emergent := by
  refine ⟨fun h m B hm2 hmN hlat _ => h m B hm2 hmN hlat, fun h m B hm2 hmN hlat => ?_⟩
  rw [not_emergent_iff]
  intro hr
  refine constructible_univ_of_isRigid_of_lattice_cores
    (fun j C hj2 hjN hrC hlC hcC => ?_) m B hm2 hmN hr hlat
  exact (not_emergent_iff.mp (h j C hj2 hjN hlC hcC)) hrC

/-- **The smallest emergent arrangement is a core**, in minimal-counterexample form: if no
emergent arrangement has between `2` and `n - 1` circles, then every emergent arrangement with
`n` circles is a core.

If such an `A` were not a core it would have a removable circle `w`; the peel is rigid on exactly
one circle fewer, and has at least two circles, so by hypothesis it is not emergent, hence
constructible; replaying that derivation in `A` and adding one Henneberg step for `w` makes `A`
constructible, contradicting emergence.

No canonical core and no confluence of peeling is used: one peel and one Henneberg step.

The hypothesis only constrains arrangements of at least two circles, which is the whole scope of
the question: below two circles nothing is constructible
(`Arrangement.not_constructible_of_subsingleton`) and everything is a core
(`Arrangement.isCore_of_card_le_two`), so no bound on `n` is needed in the statement. The peel
is where `2 ≤ m` is spent: a removable circle forces at least three circles
(`Arrangement.Removable.three_le`), so the peel has at least two. -/
theorem isCore_of_emergent_of_minimal {n : ℕ}
    (hmin : ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → m < n → ¬ B.Emergent)
    {A : Arrangement (Fin n)} (hA : A.Emergent) : A.IsCore := by
  intro w hw
  have h3 : 3 ≤ n := hw.three_le
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hpeel := hw.isRigid_comap_succAbove hA.1
  have hne := hmin k (A.comap w.succAbove Fin.succAbove_right_injective) (by omega) (by omega)
  rw [not_emergent_iff] at hne
  exact hA.2 (hw.constructible_univ_of_peel (hne hpeel))

/-- **The smallest emergent arrangement is a core.** If `A` is emergent and no emergent
arrangement of at least two circles has fewer circles than `A`, then `A` is a core.

"Smallest" means fewest circles. The least is taken over arrangements of at least two circles
because below that everything is emergent for want of a contact
(`Arrangement.emergent_of_card_le_one`), so an unrestricted least would always be the empty
arrangement and the statement would say nothing. -/
theorem isCore_of_least_emergent {n : ℕ} {A : Arrangement (Fin n)}
    (hA : A.Emergent)
    (hleast : ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → B.Emergent → n ≤ m) :
    A.IsCore :=
  isCore_of_emergent_of_minimal
    (fun m B hm2 hmn hB => absurd (hleast m B hm2 hB) (by omega)) hA

/-- **The smallest emergent lattice arrangement is a core.** The lattice form of
`Arrangement.isCore_of_least_emergent`: the peel of a lattice arrangement is a lattice
arrangement (`Arrangement.IsLattice.comap`), so the minimality hypothesis need only speak about
arrangements on the lattice — which is what a census of lattice arrangements establishes. -/
theorem isCore_of_least_emergent_lattice {n : ℕ} {A : Arrangement (Fin n)} (hlat : A.IsLattice)
    (hA : A.Emergent)
    (hleast : ∀ (m : ℕ) (B : Arrangement (Fin m)), 2 ≤ m → B.IsLattice → B.Emergent → n ≤ m) :
    A.IsCore := by
  intro w hw
  have h3 : 3 ≤ n := hw.three_le
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hne : ¬ (A.comap w.succAbove Fin.succAbove_right_injective).Emergent := fun he =>
    absurd (hleast k _ (by omega) (hlat.comap Fin.succAbove_right_injective) he) (by omega)
  rw [not_emergent_iff] at hne
  exact hA.2 (hw.constructible_univ_of_peel (hne (hw.isRigid_comap_succAbove hA.1)))

end Arrangement

end RigidArrangements
