import RigidArrangements.Core
import RigidArrangements.Flex
import RigidArrangements.Henneberg
import RigidArrangements.Isometry
import RigidArrangements.Lattice

/-!
# Rigid arrangements of at most six circles

This file classifies the rigid arrangements of at most six circles, up to isomorphism. Up to
three circles the classification is unconditional. From four circles on it assumes that no
rigid arrangement of four to six circles is a *core* (`NoCoresBetween 4 6`, see
`RigidArrangements.Core`): every such arrangement has a *removable* circle, one that touches
exactly two others, less than `4` apart. That hypothesis is proved separately; here it is an
explicit hypothesis of each theorem that needs it.

| circles | rigid arrangements up to isomorphism                       |
|---------|------------------------------------------------------------|
| 1       | one circle                                                 |
| 2       | two touching circles                                       |
| 3       | the triangle                                               |
| 4       | the rhombus: two triangles                                 |
| 5       | the trapezoid: three triangles in a row (half a hexagon)   |
| 6       | the parallelogram: four triangles in a row                 |
|         | the chevron: a fan of four triangles around one circle     |
|         | the big triangle: side `2`, three circles on each side     |

So there are `1, 1, 1, 1, 1, 3` of them for `n = 1, …, 6`, and all of them lie on the
triangular lattice. For `3 ≤ n ≤ 6` they are the corner sets of the polyiamonds with `n - 2`
triangles, and the counts `1, 1, 1, 3` agree with the numbers of polyiamonds (OEIS A000577).
According to the exploratory enumerations this agreement stops at `n = 8` (twelve hexiamonds,
but nine rigid arrangements of eight circles), beyond the range of this file.

## The method

Suppose that `A` is a rigid arrangement of `n + 1 ≥ 4` circles with a removable circle `w`.

1. **Remove.** Without `w`, the other circles still form a rigid arrangement
   (`Arrangement.Removable.isRigid_comap_succAbove`, a reverse Henneberg step). By induction it
   is isomorphic to a known lattice arrangement `ofLattice l`.
2. **Put back.** Move `A` by the isometry of the plane that carries the other circles onto the
   points of `l`. The center of `w` is then at distance `2` from two lattice points `a`, `b`
   that are less than `4` apart. In the plane only two points are at distance `2` from both
   (`eq_or_eq_of_dist_eq_of_dist_eq`, from the mirror-image lemma `eq_or_eq_reflect`), and for
   lattice points `a`, `b` less than `4` apart these two points are lattice points, the apexes
   of the two lattice triangles over `a b` (`exists_mem_latticeApexes`). So `w` lands on a
   lattice point `x`, and since `w` touches no other circle, `x` is an *extension site* of `l`:
   a lattice point outside `l` touching exactly two points of `l`, less than `4` apart. Hence
   `A` is isomorphic to `ofLattice (x :: l)` for one of the finitely many extension sites `x`
   of `l`, listed by the computable function `extensionSites`
   (`Arrangement.Removable.exists_iso_cons`).
3. **Recognise.** The Lean kernel checks (`decide +kernel`) that each extension `x :: l` is
   carried onto one of the claimed shapes by one of the twelve symmetries of the lattice,
   followed by a translation (`latticeMatch`, `coverStep`). A lattice symmetry keeps all
   distances, so it gives an isomorphism (`Arrangement.iso_ofLattice_of_map`).

This proves `LatticeCover n T` for the list `T` of shapes: every rigid arrangement of `n`
circles is isomorphic to `ofLattice t` for some `t ∈ T` (`LatticeCover.succ`). The variant
`LatticeCover.succ_of_cores` also accepts a list of known cores, for use with more circles.

To *count*, two more facts are needed, both checked by the kernel.

* **The shapes are rigid.** Each shape is listed in a *build order* (`latticeBuilt`): its first
  two circles touch, and every later circle touches two earlier ones. Adding a circle that
  touches two circles keeps rigidity (a Henneberg step), so the shape is rigid
  (`Arrangement.isRigid_ofLattice_of_latticeBuilt`).
* **The shapes are pairwise non-isomorphic.** The integer `latticeKey`, computed from the
  pairwise distances, is an isomorphism invariant (`Arrangement.latticeKey_eq_of_iso`) and
  takes different values on the shapes. For six circles all three shapes have `9` contacts, so
  counting contacts would not tell them apart.

`card_rigidClasses_eq_of_latticeCover` then counts the classes.

## Main results

* `eq_or_eq_of_dist_eq_of_dist_eq`, `exists_mem_latticeApexes`: the geometry of step 2.
* `extensionSites`, `Arrangement.Removable.exists_iso_cons`: **one-step extension**.
* `latticeMatch`, `Arrangement.iso_ofLattice_of_latticeMatch`: recognising lattice
  arrangements up to a lattice symmetry.
* `LatticeCover`, `coverStep`, `LatticeCover.succ`, `LatticeCover.succ_of_cores`: the
  induction step of the classification.
* `latticeBuilt`, `Arrangement.isRigid_ofLattice_of_latticeBuilt`: build certificates.
* `latticeKey`, `Arrangement.latticeKey_eq_of_iso`: an isomorphism invariant.
* `card_rigidClasses_eq_of_latticeCover`: counting from a certified cover.
* `Arrangement.trapezoid`, `Arrangement.parallelogram`, `Arrangement.chevron`,
  `Arrangement.bigTriangle`: the shapes with five and six circles (the triangle and the rhombus
  are `Arrangement.triangle` and `Arrangement.rhombus`).
* `Arrangement.isRigid_iff_iso_rhombus`, `Arrangement.isRigid_iff_iso_trapezoid`,
  `Arrangement.isRigid_iff_six`: the explicit classification for four, five and six circles.
* `card_rigidClasses_zero`, `card_rigidClasses_one`, `card_rigidClasses_two`,
  `card_rigidClasses_three` (unconditional), `card_rigidClasses_four`,
  `card_rigidClasses_five`, `card_rigidClasses_six`, and **`card_rigidClasses_le_six`**: the
  counts.
* `Arrangement.IsRigid.isLattice_of_le_six`: rigid arrangements of at most six circles lie on
  the triangular lattice.

The kernel checks take well under a second each.
-/

namespace RigidArrangements

/-! ### Two distances pin a point down to two positions -/

/-- **At most two positions.** Let `a ≠ b` be points of the plane, and `x ≠ y` two points with
the same distances to `a` and to `b`. Then every point `z` with these distances to `a` and `b` is
`x` or `y`. (The two positions are mirror images in the line `ab`, see `eq_or_eq_reflect`.) -/
theorem eq_or_eq_of_dist_eq_of_dist_eq {a b x y z : ℂ} (hab : a ≠ b) (hxy : x ≠ y)
    (hya : dist y a = dist x a) (hyb : dist y b = dist x b)
    (hza : dist z a = dist x a) (hzb : dist z b = dist x b) : z = x ∨ z = y := by
  rcases eq_or_eq_reflect hab hya hyb with h | h
  · exact absurd h.symm hxy
  · rcases eq_or_eq_reflect hab hza hzb with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.trans h.symm)

/-! ### Lattice arithmetic -/

private theorem eNorm_sub_comm (v w : ℤ × ℤ) : eNorm (v - w) = eNorm (w - v) := by
  simp only [eNorm, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Lattice points whose differences have the same `eNorm` are the same distance apart. -/
theorem dist_latticePoint_eq_of_eNorm_eq {a b c d : ℤ × ℤ}
    (h : eNorm (a - b) = eNorm (c - d)) :
    dist (latticePoint a) (latticePoint b) = dist (latticePoint c) (latticePoint d) :=
  (sq_eq_sq₀ dist_nonneg dist_nonneg).1 (by rw [dist_latticePoint_sq, dist_latticePoint_sq, h])

/-- Pairs of lattice points the same distance apart have differences of the same `eNorm`. -/
theorem eNorm_eq_of_dist_latticePoint_eq {a b c d : ℤ × ℤ}
    (h : dist (latticePoint a) (latticePoint b) = dist (latticePoint c) (latticePoint d)) :
    eNorm (a - b) = eNorm (c - d) := by
  have h1 := dist_latticePoint_sq a b
  rw [h, dist_latticePoint_sq] at h1
  have : (eNorm (a - b) : ℝ) = eNorm (c - d) := by linarith
  exact_mod_cast this

/-- The six unit vectors of the triangular lattice, in counterclockwise order: the lattice
points touching the origin. -/
def latticeUnits : List (ℤ × ℤ) :=
  [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

/-- The unit vectors have `eNorm` one. -/
theorem eNorm_of_mem_latticeUnits {k : ℤ × ℤ} (hk : k ∈ latticeUnits) : eNorm k = 1 := by
  have : ∀ k ∈ latticeUnits, eNorm k = 1 := by decide
  exact this k hk

/-- The lattice points that touch both `a` and `b`. When `a ≠ b` are less than `4` apart, these
are the two apexes of the lattice triangles over `a` and `b`, and no other point of the plane
is at distance `2` from both (`exists_mem_latticeApexes`). -/
def latticeApexes (a b : ℤ × ℤ) : List (ℤ × ℤ) :=
  (latticeUnits.map (a + ·)).filter fun x => eNorm (x - b) = 1

/-- The points of `latticeApexes a b` touch `a` and `b`. -/
theorem eNorm_of_mem_latticeApexes {a b x : ℤ × ℤ} (hx : x ∈ latticeApexes a b) :
    eNorm (x - a) = 1 ∧ eNorm (x - b) = 1 := by
  simp only [latticeApexes, List.mem_filter, List.mem_map, decide_eq_true_eq] at hx
  obtain ⟨⟨k, hk, rfl⟩, hb⟩ := hx
  exact ⟨by simpa using eNorm_of_mem_latticeUnits hk, hb⟩

private theorem bounds_of_eNorm_lt_four {d : ℤ × ℤ} (h : eNorm d < 4) :
    -2 ≤ d.1 ∧ d.1 ≤ 2 ∧ -2 ≤ d.2 ∧ d.2 ≤ 2 := by
  unfold eNorm at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (2 * d.1 + d.2), sq_nonneg (d.1 + 2 * d.2)]

/-- If the lattice vector `d ≠ 0` has `eNorm d < 4` (so `eNorm d` is `1` or `3`), the lattice
points `0` and `d` have two distinct common neighbours `k₁`, `k₂`. Such a `d` has coordinates
between `-2` and `2`, and the kernel checks these finitely many cases. -/
private theorem exists_two_latticeUnits {d : ℤ × ℤ} (h0 : d ≠ 0) (h4 : eNorm d < 4) :
    ∃ k₁ ∈ latticeUnits, ∃ k₂ ∈ latticeUnits,
      k₁ ≠ k₂ ∧ eNorm (k₁ - d) = 1 ∧ eNorm (k₂ - d) = 1 := by
  have key : ∀ p ∈ ([-2, -1, 0, 1, 2] : List ℤ), ∀ q ∈ ([-2, -1, 0, 1, 2] : List ℤ),
      (p, q) ≠ 0 → eNorm (p, q) < 4 → ∃ k₁ ∈ latticeUnits, ∃ k₂ ∈ latticeUnits,
        k₁ ≠ k₂ ∧ eNorm (k₁ - (p, q)) = 1 ∧ eNorm (k₂ - (p, q)) = 1 := by
    decide +kernel
  obtain ⟨h1, h2, h3, h4'⟩ := bounds_of_eNorm_lt_four h4
  exact key d.1 (by simp; omega) d.2 (by simp; omega) h0 h4

/-- **Apexes over a short lattice edge are lattice points.** If the lattice points `a ≠ b` are
less than `4` apart, every point of the plane at distance `2` from both of them is a lattice
point, one of `latticeApexes a b`. -/
theorem exists_mem_latticeApexes {a b : ℤ × ℤ} (hab : a ≠ b) (h4 : eNorm (a - b) < 4)
    {c : Plane} (ha : dist c (latticePoint a) = 2) (hb : dist c (latticePoint b) = 2) :
    ∃ x ∈ latticeApexes a b, c = latticePoint x := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hk, h₁, h₂⟩ :=
    exists_two_latticeUnits (sub_ne_zero.2 hab.symm) (by rwa [eNorm_sub_comm])
  have mem : ∀ k ∈ latticeUnits, eNorm (k - (b - a)) = 1 → a + k ∈ latticeApexes a b ∧
      dist (latticePoint (a + k)) (latticePoint a) = 2 ∧
      dist (latticePoint (a + k)) (latticePoint b) = 2 := by
    intro k hk hkd
    have e : a + k - b = k - (b - a) := by abel
    refine ⟨?_, ?_, ?_⟩
    · simp only [latticeApexes, List.mem_filter, List.mem_map, decide_eq_true_eq]
      exact ⟨⟨k, hk, rfl⟩, by rw [e, hkd]⟩
    · rw [tangent_latticePoint_iff, add_sub_cancel_left]
      exact eNorm_of_mem_latticeUnits hk
    · rw [tangent_latticePoint_iff, e]
      exact hkd
  obtain ⟨m₁, d₁a, d₁b⟩ := mem k₁ hk₁ h₁
  obtain ⟨m₂, d₂a, d₂b⟩ := mem k₂ hk₂ h₂
  have hne : latticePoint (a + k₁) ≠ latticePoint (a + k₂) :=
    latticePoint_injective.ne fun h => hk (add_left_cancel h)
  rcases eq_or_eq_of_dist_eq_of_dist_eq (latticePoint_injective.ne hab) hne
      (d₂a.trans d₁a.symm) (d₂b.trans d₁b.symm) (ha.trans d₁a.symm) (hb.trans d₁b.symm) with
    h | h
  · exact ⟨_, m₁, h⟩
  · exact ⟨_, m₂, h⟩

/-! ### Extension sites and the one-step extension -/

/-- The *extension sites* of the lattice arrangement `l`: the lattice points `x ∉ l` that touch
two points `a ≠ b` of `l` less than `4` apart, and no other point of `l`. A circle added at `x`
is removable. (A site may be listed more than once.) -/
def extensionSites (l : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  l.flatMap fun a => l.flatMap fun b =>
    if a ≠ b ∧ eNorm (a - b) < 4 then
      (latticeApexes a b).filter fun x => x ∉ l ∧ ∀ m ∈ l, m = a ∨ m = b ∨ eNorm (x - m) ≠ 1
    else []

/-- An apex `x ∉ l` over two points `a ≠ b` of `l` less than `4` apart, touching no other point
of `l`, is an extension site of `l`. -/
theorem mem_extensionSites {l : List (ℤ × ℤ)} {a b x : ℤ × ℤ} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) (h4 : eNorm (a - b) < 4) (hx : x ∈ latticeApexes a b) (hxl : x ∉ l)
    (hm : ∀ m ∈ l, eNorm (x - m) = 1 → m = a ∨ m = b) : x ∈ extensionSites l := by
  simp only [extensionSites, List.mem_flatMap]
  refine ⟨a, ha, b, hb, ?_⟩
  rw [ite_eq_left ⟨hab, h4⟩, List.mem_filter, decide_eq_true_eq]
  refine ⟨hx, hxl, fun m hml => ?_⟩
  by_cases h1 : eNorm (x - m) = 1
  · exact (hm m hml h1).elim Or.inl (Or.inr ∘ Or.inl)
  · exact Or.inr (Or.inr h1)

namespace Arrangement

private theorem ofLattice_center (l : List (ℤ × ℤ)) (hl : l.Nodup) (i : Fin l.length) :
    (ofLattice l hl).center i = latticePoint (l.get i) :=
  rfl

/-- **Removing a removable circle keeps rigidity**: if `w` is removable in the rigid
arrangement `A`, the other circles, numbered in order, form a rigid arrangement. -/
theorem Removable.isRigid_comap_succAbove {n : ℕ} {A : Arrangement (Fin (n + 1))}
    {w : Fin (n + 1)} (hw : A.Removable w) (h : A.IsRigid) :
    (A.comap w.succAbove Fin.succAbove_right_injective).IsRigid := by
  obtain ⟨u, v, huv, hadj, h4⟩ := hw
  have hu := (hadj u).2 (Or.inl rfl)
  have hv := (hadj v).2 (Or.inr rfl)
  obtain ⟨u', rfl⟩ := Fin.exists_succAbove_eq hu.1.symm
  obtain ⟨v', rfl⟩ := Fin.exists_succAbove_eq hv.1.symm
  refine h.comap_succAbove hu.2 hv.2 (fun j hj => ?_) (fun e => huv (congrArg _ e)) h4
  rcases (hadj _).1 ⟨(Fin.succAbove_ne w j).symm, hj⟩ with e | e
  · exact Or.inl (Fin.succAbove_right_injective e)
  · exact Or.inr (Fin.succAbove_right_injective e)

/-- **One-step extension.** Let `w` be a removable circle of `A`. If the other circles of `A`
form an arrangement isomorphic to the lattice arrangement `l`, then `A` is isomorphic to the
lattice arrangement `x :: l` for some extension site `x` of `l`.

The isometry that carries the other circles onto `l` carries the center of `w` to a point at
distance `2` from two lattice points less than `4` apart, hence to a lattice point
(`exists_mem_latticeApexes`). Since `w` touches no other circle, that point is an extension
site. -/
theorem Removable.exists_iso_cons {n : ℕ} {A : Arrangement (Fin (n + 1))} {w : Fin (n + 1)}
    (hw : A.Removable w) {l : List (ℤ × ℤ)} {hl : l.Nodup}
    (hiso : (A.comap w.succAbove Fin.succAbove_right_injective).Iso (ofLattice l hl)) :
    ∃ x ∈ extensionSites l, ∃ hx : (x :: l).Nodup, A.Iso (ofLattice (x :: l) hx) := by
  obtain ⟨u, v, huv, hadj, h4⟩ := hw
  have hu := (hadj u).2 (Or.inl rfl)
  have hv := (hadj v).2 (Or.inr rfl)
  obtain ⟨u', rfl⟩ := Fin.exists_succAbove_eq hu.1.symm
  obtain ⟨v', rfl⟩ := Fin.exists_succAbove_eq hv.1.symm
  have huv' : u' ≠ v' := fun e => huv (congrArg _ e)
  -- the isometry `g` puts the circles other than `w` on the points of `l`
  obtain ⟨e, g, hg⟩ := iso_iff_exists_isometry.mp hiso
  have hg' : ∀ i, latticePoint (l.get (e i)) = g (A.center (w.succAbove i)) := hg
  have hdist : ∀ i, dist (g (A.center w)) (latticePoint (l.get (e i))) =
      dist (A.center w) (A.center (w.succAbove i)) := fun i => by
    rw [hg', g.dist_map]
  have hab : l.get (e u') ≠ l.get (e v') := fun h => huv' (e.injective (hl.get_inj_iff.mp h))
  have h4' : eNorm (l.get (e u') - l.get (e v')) < 4 := by
    have hsq := dist_latticePoint_sq (l.get (e u')) (l.get (e v'))
    rw [hg', hg', g.dist_map] at hsq
    have h0 := dist_nonneg (x := A.center (w.succAbove u')) (y := A.center (w.succAbove v'))
    have : (eNorm (l.get (e u') - l.get (e v')) : ℝ) < 4 := by nlinarith
    exact_mod_cast this
  -- so `g` puts `w` on an apex `x` over the images of its two neighbours
  obtain ⟨x, hxA, hcx⟩ :=
    exists_mem_latticeApexes hab h4' ((hdist u').trans hu.2) ((hdist v').trans hv.2)
  have hxl : x ∉ l := by
    intro hx
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
    have : g (A.center w) = g (A.center (w.succAbove (e.symm j))) := by
      rw [← hg', e.apply_symm_apply, hj, hcx]
    exact Fin.succAbove_ne w _ (A.center_injective (g.injective this)).symm
  have hm : ∀ m ∈ l, eNorm (x - m) = 1 → m = l.get (e u') ∨ m = l.get (e v') := by
    intro m hml h1
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hml
    obtain ⟨i, rfl⟩ := e.surjective j
    have ht : Tangent A.center w (w.succAbove i) := by
      change dist _ _ = 2
      rw [← hdist i, hcx]
      exact (tangent_latticePoint_iff _ _).2 h1
    rcases (hadj _).1 ⟨(Fin.succAbove_ne w i).symm, ht⟩ with h | h
    · exact Or.inl (by rw [Fin.succAbove_right_injective h])
    · exact Or.inr (by rw [Fin.succAbove_right_injective h])
  refine ⟨x, mem_extensionSites (List.get_mem _ _) (List.get_mem _ _) hab h4' hxA hxl hm,
    List.nodup_cons.2 ⟨hxl, hl⟩, ?_⟩
  -- relabel: `w ↦ 0`, `w.succAbove i ↦ (e i).succ`
  refine Iso.of_isometry g.isometry
    ((finSuccEquiv' w).trans (e.optionCongr.trans (finSuccEquiv l.length).symm)) fun i => ?_
  rcases Fin.eq_self_or_eq_succAbove w i with rfl | ⟨j, rfl⟩
  · simp only [Equiv.trans_apply, finSuccEquiv'_at, Equiv.optionCongr_apply, Option.map_none,
      finSuccEquiv_symm_none, ofLattice_center]
    exact hcx.symm
  · simp only [Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
      Option.map_some, finSuccEquiv_symm_some, ofLattice_center]
    exact hg' j

end Arrangement

/-! ### An isomorphism invariant -/

/-- A numerical isomorphism invariant of lattice arrangements, computed from the pairwise
`eNorm`s (that is, from the pairwise distances): `Σ_a (Σ_b eNorm (a - b) ^ 2) ^ 3`. -/
def latticeKey (l : List (ℤ × ℤ)) : ℤ :=
  (l.map fun a => (l.map fun b => eNorm (a - b) ^ 2).sum ^ 3).sum

private theorem latticeKey_eq_sum (l : List (ℤ × ℤ)) :
    latticeKey l =
      ∑ i : Fin l.length, (∑ j : Fin l.length, eNorm (l.get i - l.get j) ^ 2) ^ 3 := by
  simp only [latticeKey, List.get_eq_getElem, ← Fin.sum_univ_fun_getElem]

/-- Isomorphic lattice arrangements have the same `latticeKey`. -/
theorem Arrangement.latticeKey_eq_of_iso {l t : List (ℤ × ℤ)} {hl : l.Nodup} {ht : t.Nodup}
    (h : (ofLattice l hl).Iso (ofLattice t ht)) : latticeKey l = latticeKey t := by
  obtain ⟨e, he⟩ := h
  rw [congruent_iff_dist_eq] at he
  have hn : ∀ i j, eNorm (l.get i - l.get j) = eNorm (t.get (e i) - t.get (e j)) := fun i j =>
    eNorm_eq_of_dist_latticePoint_eq (he i j)
  rw [latticeKey_eq_sum, latticeKey_eq_sum]
  simp only [hn]
  rw [← e.sum_comp (fun i => (∑ j, eNorm (t.get i - t.get j) ^ 2) ^ 3)]
  congr 1
  ext i
  rw [e.sum_comp (fun j => eNorm (t.get (e i) - t.get j) ^ 2)]

/-! ### Recognising lattice arrangements up to isomorphism -/

namespace Arrangement

/-- **Isomorphism from a lattice map.** If a map `φ` of the lattice keeps the `eNorm` of every
difference (so it is an isometry of the lattice) and sends the points of `l` into `t`, and `l`
and `t` have the same length, then `ofLattice l` and `ofLattice t` are isomorphic. -/
theorem iso_ofLattice_of_map {l t : List (ℤ × ℤ)} (hl : l.Nodup) (φ : ℤ × ℤ → ℤ × ℤ)
    (hφ : ∀ v w, eNorm (φ v - φ w) = eNorm (v - w)) (hlen : l.length = t.length)
    (hmem : ∀ v ∈ l, φ v ∈ t) : ∃ ht : t.Nodup, (ofLattice l hl).Iso (ofLattice t ht) := by
  have hφi : Function.Injective φ := fun v w h => by
    have h0 : eNorm (v - w) = 0 := by rw [← hφ, h, sub_self]; rfl
    exact sub_eq_zero.mp ((eNorm_eq_zero_iff _).1 h0)
  -- the relabeling: circle `i` of `l` goes to the position of `φ (l.get i)` in `t`
  let f : Fin l.length → Fin t.length := fun i =>
    ⟨t.idxOf (φ (l.get i)), List.idxOf_lt_length_iff.2 (hmem _ (List.get_mem _ _))⟩
  have hf : ∀ i, t.get (f i) = φ (l.get i) := fun i => List.getElem_idxOf _
  have hfi : Function.Injective f := fun i j h => by
    have := congrArg t.get h
    rw [hf, hf] at this
    exact hl.get_inj_iff.mp (hφi this)
  have hfb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, by simp [hlen]⟩
  have ht : t.Nodup := List.nodup_iff_injective_get.2 fun a b hab => by
    obtain ⟨i, rfl⟩ := hfb.2 a
    obtain ⟨j, rfl⟩ := hfb.2 b
    rw [hf, hf] at hab
    rw [hl.get_inj_iff.mp (hφi hab)]
  refine ⟨ht, Equiv.ofBijective f hfb, ?_⟩
  rw [congruent_iff_dist_eq]
  intro i j
  simp only [Function.comp_apply, Equiv.ofBijective_apply, ofLattice_center, hf]
  exact dist_latticePoint_eq_of_eNorm_eq (hφ _ _).symm

end Arrangement

/-- The integer matrix `M = (a, b, c, d)` acting on lattice coordinates:
`(p, q) ↦ (a p + b q, c p + d q)`. -/
def latticeMatApply : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ → ℤ × ℤ
  | (a, b, c, d), (p, q) => (a * p + b * q, c * p + d * q)

/-- The twelve symmetries of the triangular lattice fixing the origin (six rotations, then the
six reflections), as integer matrices in lattice coordinates. The rotation by `60°` is
`(p, q) ↦ (-q, p + q)`. -/
def latticeSymmetries : List (ℤ × ℤ × ℤ × ℤ) :=
  [(1, 0, 0, 1), (0, -1, 1, 1), (-1, -1, 1, 0), (-1, 0, 0, -1), (0, 1, -1, -1), (1, 1, -1, 0),
    (0, 1, 1, 0), (1, 1, 0, -1), (1, 0, -1, -1), (0, -1, -1, 0), (-1, -1, 0, 1), (-1, 0, 1, 1)]

/-- Matrices act linearly. -/
theorem latticeMatApply_sub (M : ℤ × ℤ × ℤ × ℤ) (v w : ℤ × ℤ) :
    latticeMatApply M v - latticeMatApply M w = latticeMatApply M (v - w) := by
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨p, q⟩ := v
  obtain ⟨r, s⟩ := w
  simp only [latticeMatApply, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor <;> ring

/-- The lattice symmetries keep the Eisenstein norm. (The kernel checks that each matrix keeps
the three coefficients of the quadratic form `p² + pq + q²`.) -/
theorem eNorm_latticeMatApply {M : ℤ × ℤ × ℤ × ℤ} (hM : M ∈ latticeSymmetries) (v : ℤ × ℤ) :
    eNorm (latticeMatApply M v) = eNorm v := by
  have key : ∀ M ∈ latticeSymmetries, M.1 ^ 2 + M.1 * M.2.2.1 + M.2.2.1 ^ 2 = 1 ∧
      2 * M.1 * M.2.1 + M.1 * M.2.2.2 + M.2.1 * M.2.2.1 + 2 * M.2.2.1 * M.2.2.2 = 1 ∧
      M.2.1 ^ 2 + M.2.1 * M.2.2.2 + M.2.2.2 ^ 2 = 1 := by
    decide
  obtain ⟨h1, h2, h3⟩ := key M hM
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨p, q⟩ := v
  simp only at h1 h2 h3
  simp only [latticeMatApply, eNorm]
  linear_combination p ^ 2 * h1 + p * q * h2 + q ^ 2 * h3

/-- `latticeMatch l t`: `l` and `t` have the same length, and some symmetry of the lattice (a
rotation or reflection from `latticeSymmetries`, then a translation) carries every point of `l`
to a point of `t`. The translation is chosen to send the first point of `l` to some point of
`t`. The keys of `l` and `t` are compared first: this cheap filter is not needed for soundness,
but it makes the kernel checks several times faster. -/
def latticeMatch (l t : List (ℤ × ℤ)) : Bool :=
  l.length == t.length && latticeKey l == latticeKey t &&
    latticeSymmetries.any fun M => t.any fun s =>
      l.all fun u => latticeMatApply M u + (s - latticeMatApply M (l.headD 0)) ∈ t

/-- Soundness of `latticeMatch`: matching lattice arrangements are isomorphic. -/
theorem Arrangement.iso_ofLattice_of_latticeMatch {l t : List (ℤ × ℤ)} (hl : l.Nodup)
    (h : latticeMatch l t = true) : ∃ ht : t.Nodup, (ofLattice l hl).Iso (ofLattice t ht) := by
  simp only [latticeMatch, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hlen, -⟩, M, hM, s, -, hall⟩ := h
  refine iso_ofLattice_of_map hl
    (fun u => latticeMatApply M u + (s - latticeMatApply M (l.headD 0))) (fun v w => ?_) hlen hall
  rw [add_sub_add_right_eq_sub, latticeMatApply_sub, eNorm_latticeMatApply hM]

/-! ### Lattice covers: the induction step -/

/-- `LatticeCover n S`: every rigid arrangement of `n` circles is isomorphic to the lattice
arrangement of some list in `S`. -/
def LatticeCover (n : ℕ) (S : List (List (ℤ × ℤ))) : Prop :=
  ∀ A : Arrangement (Fin n), A.IsRigid →
    ∃ l ∈ S, ∃ hl : l.Nodup, A.Iso (Arrangement.ofLattice l hl)

/-- `coverStep S T`: every extension `x :: l` of a list `l` of `S` at one of its extension
sites `x` matches some list of `T` (`latticeMatch`). -/
def coverStep (S T : List (List (ℤ × ℤ))) : Bool :=
  S.all fun l => (extensionSites l).all fun x => T.any fun t => latticeMatch (x :: l) t

/-- `coverCores C T`: every list of `C` matches some list of `T`. -/
def coverCores (C T : List (List (ℤ × ℤ))) : Bool :=
  C.all fun c => T.any fun t => latticeMatch c t

/-- **The induction step of the classification, with cores.** Suppose that `S` covers the rigid
arrangements of `n` circles, and that every rigid arrangement of `n + 1` circles either has a
removable circle or is isomorphic to one of the lattice arrangements `C` (the cores). If every
extension of a list of `S` and every list of `C` matches a list of `T`, then `T` covers the
rigid arrangements of `n + 1` circles. -/
theorem LatticeCover.succ_of_cores {n : ℕ} {S C T : List (List (ℤ × ℤ))}
    (hS : LatticeCover n S)
    (hrem : ∀ A : Arrangement (Fin (n + 1)), A.IsRigid →
      (∃ w, A.Removable w) ∨ ∃ c ∈ C, ∃ hc : c.Nodup, A.Iso (Arrangement.ofLattice c hc))
    (hST : coverStep S T = true) (hCT : coverCores C T = true) : LatticeCover (n + 1) T := by
  intro A hA
  rcases hrem A hA with ⟨w, hw⟩ | ⟨c, hcC, hc, hiso⟩
  · obtain ⟨l, hlS, hl, hiso⟩ := hS _ (hw.isRigid_comap_succAbove hA)
    obtain ⟨x, hx, hxl, hiso'⟩ := hw.exists_iso_cons hiso
    simp only [coverStep, List.all_eq_true, List.any_eq_true] at hST
    obtain ⟨t, htT, hm⟩ := hST l hlS x hx
    obtain ⟨ht, hiso''⟩ := Arrangement.iso_ofLattice_of_latticeMatch _ hm
    exact ⟨t, htT, ht, hiso'.trans hiso''⟩
  · simp only [coverCores, List.all_eq_true, List.any_eq_true] at hCT
    obtain ⟨t, htT, hm⟩ := hCT c hcC
    obtain ⟨ht, hiso'⟩ := Arrangement.iso_ofLattice_of_latticeMatch hc hm
    exact ⟨t, htT, ht, hiso.trans hiso'⟩

/-- **The induction step of the classification.** If `S` covers the rigid arrangements of `n`
circles, every rigid arrangement of `n + 1` circles has a removable circle, and every extension
of a list of `S` matches a list of `T`, then `T` covers the rigid arrangements of `n + 1`
circles. -/
theorem LatticeCover.succ {n : ℕ} {S T : List (List (ℤ × ℤ))} (hS : LatticeCover n S)
    (hrem : ∀ A : Arrangement (Fin (n + 1)), A.IsRigid → ∃ w, A.Removable w)
    (hST : coverStep S T = true) : LatticeCover (n + 1) T :=
  hS.succ_of_cores (C := []) (fun A hA => Or.inl (hrem A hA)) hST rfl

/-- A rigid arrangement covered by a lattice cover lies on the triangular lattice. -/
theorem LatticeCover.isLattice {n : ℕ} {S : List (List (ℤ × ℤ))} (hS : LatticeCover n S)
    {A : Arrangement (Fin n)} (hA : A.IsRigid) : A.IsLattice := by
  obtain ⟨l, -, hl, hiso⟩ := hS A hA
  obtain ⟨e, g, hg⟩ := Arrangement.iso_iff_exists_isometry.mp hiso
  exact ⟨g, fun i => l.get (e i), fun i => (hg i).symm⟩

/-! ### Rigidity from a build order -/

/-- The build check, newest point first: `x :: L` passes when `L` passes and `x` touches two
distinct points of `L`. Lists of at most one point pass, and two points pass when they touch. -/
def latticeBuiltRev : List (ℤ × ℤ) → Bool
  | [] => true
  | [_] => true
  | [x, y] => eNorm (x - y) = 1
  | x :: y :: z :: T => latticeBuiltRev (y :: z :: T) &&
      (y :: z :: T).any fun u => (y :: z :: T).any fun v =>
        u ≠ v ∧ eNorm (x - u) = 1 ∧ eNorm (x - v) = 1

/-- **Build certificate.** `latticeBuilt l`: the first two points of `l` touch, and every later
point touches two distinct earlier points. Read in order, `l` then builds the arrangement by
Henneberg steps, so it is rigid (`Arrangement.isRigid_ofLattice_of_latticeBuilt`). -/
def latticeBuilt (l : List (ℤ × ℤ)) : Bool :=
  latticeBuiltRev l.reverse

namespace Arrangement

/-- Soundness of `latticeBuiltRev`, by Henneberg steps (`IsRigid.of_comap`). -/
theorem isRigid_ofLattice_of_latticeBuiltRev :
    ∀ (l : List (ℤ × ℤ)) (hl : l.Nodup), latticeBuiltRev l = true → (ofLattice l hl).IsRigid
  | [], _, _ => by
    have : Subsingleton (Fin ([] : List (ℤ × ℤ)).length) := Fin.subsingleton_zero
    exact isRigid_of_subsingleton _
  | [x], _, _ => by
    have : Subsingleton (Fin [x].length) := Fin.subsingleton_one
    exact isRigid_of_subsingleton _
  | [x, y], hl, h => by
    have hxy : eNorm (x - y) = 1 := by simpa [latticeBuiltRev] using h
    refine isRigid_of_forall_tangent _ fun i j hij => ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (tangent_latticePoint_iff _ _).2 hxy
    · exact (tangent_latticePoint_iff _ _).2 (by rwa [eNorm_sub_comm])
    · exact absurd rfl hij
  | x :: y :: z :: T, hl, h => by
    simp only [latticeBuiltRev, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨hrest, u, hu, v, hv, huv, hxu, hxv⟩ := h
    have ih := isRigid_ofLattice_of_latticeBuiltRev (y :: z :: T) (List.nodup_cons.1 hl).2 hrest
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hu
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hv
    exact IsRigid.of_comap (f := Fin.succ) (hf := Fin.succ_injective _) ih (i₀ := 0)
      (Fin.range_succ _).ge (u := i) (w := j) ((tangent_latticePoint_iff _ _).2 hxu)
      ((tangent_latticePoint_iff _ _).2 hxv) (fun e => huv (by rw [e]))

/-- **Soundness of build certificates**: a lattice arrangement with a build order is rigid. -/
theorem isRigid_ofLattice_of_latticeBuilt {l : List (ℤ × ℤ)} (hl : l.Nodup)
    (h : latticeBuilt l = true) : (ofLattice l hl).IsRigid := by
  have hr := isRigid_ofLattice_of_latticeBuiltRev l.reverse (List.nodup_reverse.2 hl) h
  obtain ⟨_, hiso⟩ := iso_ofLattice_of_map (List.nodup_reverse.2 hl) id (fun _ _ => rfl)
    List.length_reverse (t := l) (fun v hv => List.mem_reverse.1 hv)
  exact hiso.isRigid hr

end Arrangement

/-! ### Counting -/

/-- **Counting rigid classes.** If `T` covers the rigid arrangements of `n` circles, each list of
`T` has `n` distinct points and a build certificate, and the lists of `T` have pairwise
different keys, then there are exactly `T.length` rigid arrangements of `n` circles up to
isomorphism. -/
theorem card_rigidClasses_eq_of_latticeCover {n : ℕ} {T : List (List (ℤ × ℤ))}
    (hcov : LatticeCover n T) (hT : ∀ t ∈ T, t.length = n ∧ t.Nodup ∧ latticeBuilt t = true)
    (hkey : T.Pairwise fun s t => latticeKey s ≠ latticeKey t) :
    ENat.card (RigidClasses n) = T.length := by
  have hTi : ∀ i : Fin T.length, (T.get i).length = n ∧ (T.get i).Nodup ∧
      latticeBuilt (T.get i) = true := fun i => hT _ (List.get_mem _ _)
  -- the `i`-th shape, with its circles numbered by `Fin n`
  let B : Fin T.length → Arrangement (Fin n) := fun i =>
    (Arrangement.ofLattice (T.get i) (hTi i).2.1).comap (Fin.cast (hTi i).1.symm)
      (Fin.cast_injective _)
  have hBiso : ∀ i, (B i).Iso (Arrangement.ofLattice (T.get i) (hTi i).2.1) := fun i =>
    Arrangement.Iso.of_isometry isometry_id (finCongr (hTi i).1.symm) fun _ => rfl
  have hBrigid : ∀ i, (B i).IsRigid := fun i =>
    (hBiso i).symm.isRigid (Arrangement.isRigid_ofLattice_of_latticeBuilt _ (hTi i).2.2)
  let f : Fin T.length → RigidClasses n := fun i => Quotient.mk _ ⟨B i, hBrigid i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hiso : (B i).Iso (B j) := Quotient.exact hij
    have hk := Arrangement.latticeKey_eq_of_iso (((hBiso i).symm.trans hiso).trans (hBiso j))
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact List.pairwise_iff_get.1 hkey i j hlt hk
    · exact List.pairwise_iff_get.1 hkey j i hlt hk.symm
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨A, hA⟩⟩
    obtain ⟨t, htT, ht, hiso⟩ := hcov A hA
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 htT
    exact ⟨i, Quotient.sound ((hBiso i).trans hiso.symm)⟩
  rw [← ENat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), ENat.card_eq_coe_fintype_card,
    Fintype.card_fin]

/-! ### The shapes -/

namespace Arrangement

/-- The triangle on the lattice. Its centers are exactly those of `triangle`. -/
def triangleSites : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1)]

/-- The rhombus on the lattice. Its centers are exactly those of `rhombus`. -/
def rhombusSites : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, -1)]

/-- The trapezoid: three triangles in a row (half of a hexagon). -/
def trapezoidSites : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0)]

/-- The parallelogram: four triangles in a row, a patch of `2 × 3` circles. -/
def parallelogramSites : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, 1)]

/-- The chevron: a fan of four triangles around the circle at `(1, 0)`. -/
def chevronSites : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, -1)]

/-- The big triangle: an equilateral triangle of side `2` made of four triangles, with three
circles on each side. -/
def bigTriangleSites : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2)]

/-- The trapezoid: five circles, three triangles in a row. -/
noncomputable def trapezoid : Arrangement (Fin 5) := ofLattice trapezoidSites (by decide)

/-- The parallelogram: six circles, four triangles in a row. -/
noncomputable def parallelogram : Arrangement (Fin 6) := ofLattice parallelogramSites (by decide)

/-- The chevron: six circles, a fan of four triangles around one circle. -/
noncomputable def chevron : Arrangement (Fin 6) := ofLattice chevronSites (by decide)

/-- The big triangle: six circles, three on each side of an equilateral triangle. -/
noncomputable def bigTriangle : Arrangement (Fin 6) := ofLattice bigTriangleSites (by decide)

/-- The trapezoid is rigid. -/
theorem trapezoid_isRigid : trapezoid.IsRigid :=
  isRigid_ofLattice_of_latticeBuilt _ (by decide)

/-- The parallelogram is rigid. -/
theorem parallelogram_isRigid : parallelogram.IsRigid :=
  isRigid_ofLattice_of_latticeBuilt _ (by decide)

/-- The chevron is rigid. -/
theorem chevron_isRigid : chevron.IsRigid :=
  isRigid_ofLattice_of_latticeBuilt _ (by decide)

/-- The big triangle is rigid. -/
theorem bigTriangle_isRigid : bigTriangle.IsRigid :=
  isRigid_ofLattice_of_latticeBuilt _ (by decide)

private theorem iso_ofLattice_of_center_eq {k : ℕ} {A : Arrangement (Fin k)}
    {l : List (ℤ × ℤ)} {hl : l.Nodup} (e : Fin k ≃ Fin l.length)
    (h : ∀ i, latticePoint (l.get (e i)) = A.center i) : A.Iso (ofLattice l hl) :=
  Iso.of_isometry isometry_id e h

/-- The triangle is the lattice triangle. -/
theorem triangle_iso_ofLattice : triangle.Iso (ofLattice triangleSites (by decide)) :=
  iso_ofLattice_of_center_eq (Equiv.refl _) fun i => by
    change latticePoint (triangleSites.get i) = trianglePoint i
    fin_cases i <;> apply Complex.ext <;> simp [latticePoint, trianglePoint, triangleSites]

/-- The rhombus is the lattice rhombus. -/
theorem rhombus_iso_ofLattice : rhombus.Iso (ofLattice rhombusSites (by decide)) :=
  iso_ofLattice_of_center_eq (Equiv.refl _) fun i => by
    change latticePoint (rhombusSites.get i) = rhombusPoint i
    fin_cases i <;> apply Complex.ext <;> simp [latticePoint, rhombusPoint, rhombusSites]
    norm_num

end Arrangement

/-! ### Covers for at most six circles -/

open Arrangement

private theorem noCoresBetween_mono {a b a' b' : ℕ} (h : NoCoresBetween a b) (ha : a ≤ a')
    (hb : b' ≤ b) : NoCoresBetween a' b' :=
  fun n A h1 h2 hA => h n A (ha.trans h1) (h2.trans hb) hA

private theorem NoCoresBetween.exists_removable' {a b n : ℕ} (h : NoCoresBetween a b)
    (ha : a ≤ n + 1) (hb : n + 1 ≤ b) (A : Arrangement (Fin (n + 1))) (hA : A.IsRigid) :
    ∃ w, A.Removable w :=
  h (n + 1) A ha hb hA

/-- No circles: the empty arrangement. -/
theorem latticeCover_zero : LatticeCover 0 [[]] := fun _ _ =>
  ⟨[], List.mem_singleton_self _, List.nodup_nil,
    Iso.of_isometry isometry_id (Equiv.refl _) fun i => i.elim0⟩

/-- One circle. -/
theorem latticeCover_one : LatticeCover 1 [[(0, 0)]] := by
  intro A _
  refine ⟨_, List.mem_singleton_self _, by decide, Equiv.refl _, ?_⟩
  rw [congruent_iff_dist_eq]
  intro i j
  rw [Subsingleton.elim i j, dist_self, dist_self]

/-- Two circles: a rigid pair touches. -/
theorem latticeCover_two : LatticeCover 2 [[(0, 0), (1, 0)]] := by
  intro A hA
  have h01 : dist (A.center 0) (A.center 1) = 2 := (isRigid_two_iff A).1 hA
  have hl : dist (latticePoint (0, 0)) (latticePoint (1, 0)) = 2 :=
    (tangent_latticePoint_iff _ _).2 (by decide)
  refine ⟨_, List.mem_singleton_self _, by decide, Equiv.refl _, ?_⟩
  rw [congruent_iff_dist_eq]
  intro i j
  fin_cases i <;> fin_cases j
  · simp
  · exact h01.trans hl.symm
  · rw [dist_comm]; exact h01.trans (by rw [dist_comm]; exact hl.symm)
  · simp

/-- Three circles: the triangle. -/
theorem latticeCover_three : LatticeCover 3 [triangleSites] := fun _ hA =>
  ⟨_, List.mem_singleton_self _, by decide,
    (iso_triangle_of_isRigid hA).trans triangle_iso_ofLattice⟩

/-- Four circles: the rhombus, the only extension of the triangle. -/
theorem latticeCover_four (h : NoCoresBetween 4 4) : LatticeCover 4 [rhombusSites] :=
  latticeCover_three.succ (h.exists_removable' le_rfl le_rfl) (by decide +kernel)

/-- Five circles: the trapezoid, the only extension of the rhombus. -/
theorem latticeCover_five (h : NoCoresBetween 4 5) : LatticeCover 5 [trapezoidSites] :=
  (latticeCover_four (noCoresBetween_mono h le_rfl (by norm_num))).succ
    (h.exists_removable' (by norm_num) le_rfl) (by decide +kernel)

/-- Six circles: the parallelogram, the chevron and the big triangle, the extensions of the
trapezoid. -/
theorem latticeCover_six (h : NoCoresBetween 4 6) :
    LatticeCover 6 [parallelogramSites, chevronSites, bigTriangleSites] :=
  (latticeCover_five (noCoresBetween_mono h le_rfl (by norm_num))).succ
    (h.exists_removable' (by norm_num) le_rfl) (by decide +kernel)

/-! ### Explicit descriptions -/

namespace Arrangement

/-- **Rigid arrangements of four circles.** If no rigid arrangement of four circles is a core,
every rigid arrangement of four circles is the rhombus. -/
theorem iso_rhombus_of_isRigid (h : NoCoresBetween 4 4) {A : Arrangement (Fin 4)}
    (hA : A.IsRigid) : A.Iso rhombus := by
  obtain ⟨l, hl, hnd, hiso⟩ := latticeCover_four h A hA
  rw [List.mem_singleton] at hl
  subst hl
  exact hiso.trans rhombus_iso_ofLattice.symm

/-- Four circles are rigid exactly when they form the rhombus (if there are no cores of four
circles). -/
theorem isRigid_iff_iso_rhombus (h : NoCoresBetween 4 4) (A : Arrangement (Fin 4)) :
    A.IsRigid ↔ A.Iso rhombus :=
  ⟨iso_rhombus_of_isRigid h, fun hA => hA.symm.isRigid rhombus_isRigid⟩

/-- **Rigid arrangements of five circles.** If no rigid arrangement of four or five circles is
a core, every rigid arrangement of five circles is the trapezoid. -/
theorem iso_trapezoid_of_isRigid (h : NoCoresBetween 4 5) {A : Arrangement (Fin 5)}
    (hA : A.IsRigid) : A.Iso trapezoid := by
  obtain ⟨l, hl, hnd, hiso⟩ := latticeCover_five h A hA
  rw [List.mem_singleton] at hl
  subst hl
  exact hiso

/-- Five circles are rigid exactly when they form the trapezoid (if there are no cores of four
or five circles). -/
theorem isRigid_iff_iso_trapezoid (h : NoCoresBetween 4 5) (A : Arrangement (Fin 5)) :
    A.IsRigid ↔ A.Iso trapezoid :=
  ⟨iso_trapezoid_of_isRigid h, fun hA => hA.symm.isRigid trapezoid_isRigid⟩

/-- **Rigid arrangements of six circles.** If no rigid arrangement of four to six circles is a
core, every rigid arrangement of six circles is the parallelogram, the chevron or the big
triangle. -/
theorem iso_of_isRigid_six (h : NoCoresBetween 4 6) {A : Arrangement (Fin 6)}
    (hA : A.IsRigid) : A.Iso parallelogram ∨ A.Iso chevron ∨ A.Iso bigTriangle := by
  obtain ⟨l, hl, hnd, hiso⟩ := latticeCover_six h A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl hiso
  · exact Or.inr (Or.inl hiso)
  · exact Or.inr (Or.inr hiso)

/-- Six circles are rigid exactly when they form the parallelogram, the chevron or the big
triangle (if there are no cores of four to six circles). -/
theorem isRigid_iff_six (h : NoCoresBetween 4 6) (A : Arrangement (Fin 6)) :
    A.IsRigid ↔ A.Iso parallelogram ∨ A.Iso chevron ∨ A.Iso bigTriangle := by
  refine ⟨iso_of_isRigid_six h, ?_⟩
  rintro (hA | hA | hA)
  · exact hA.symm.isRigid parallelogram_isRigid
  · exact hA.symm.isRigid chevron_isRigid
  · exact hA.symm.isRigid bigTriangle_isRigid

/-- The parallelogram and the chevron are not isomorphic. -/
theorem not_iso_parallelogram_chevron : ¬ parallelogram.Iso chevron := fun h =>
  absurd (latticeKey_eq_of_iso h) (by decide)

/-- The parallelogram and the big triangle are not isomorphic. -/
theorem not_iso_parallelogram_bigTriangle : ¬ parallelogram.Iso bigTriangle := fun h =>
  absurd (latticeKey_eq_of_iso h) (by decide)

/-- The chevron and the big triangle are not isomorphic. -/
theorem not_iso_chevron_bigTriangle : ¬ chevron.Iso bigTriangle := fun h =>
  absurd (latticeKey_eq_of_iso h) (by decide)

/-- **Rigid arrangements of at most six circles lie on the triangular lattice** (if there are
no cores of four to six circles). -/
theorem IsRigid.isLattice_of_le_six (h : NoCoresBetween 4 6) {n : ℕ} (hn : n ≤ 6)
    {A : Arrangement (Fin n)} (hA : A.IsRigid) : A.IsLattice := by
  interval_cases n
  · exact latticeCover_zero.isLattice hA
  · exact latticeCover_one.isLattice hA
  · exact latticeCover_two.isLattice hA
  · exact latticeCover_three.isLattice hA
  · exact (latticeCover_four (noCoresBetween_mono h le_rfl (by norm_num))).isLattice hA
  · exact (latticeCover_five (noCoresBetween_mono h le_rfl (by norm_num))).isLattice hA
  · exact (latticeCover_six h).isLattice hA

end Arrangement

/-! ### Counts -/

/-- No circles: one (empty) arrangement, which is rigid. -/
theorem card_rigidClasses_zero : ENat.card (RigidClasses 0) = 1 :=
  card_rigidClasses_eq_of_latticeCover latticeCover_zero (by decide) (by decide)

/-- One circle: one rigid arrangement. -/
theorem card_rigidClasses_one : ENat.card (RigidClasses 1) = 1 :=
  card_rigidClasses_eq_of_latticeCover latticeCover_one (by decide) (by decide)

/-- Two circles: one rigid arrangement, two touching circles. -/
theorem card_rigidClasses_two : ENat.card (RigidClasses 2) = 1 :=
  card_rigidClasses_eq_of_latticeCover latticeCover_two (by decide) (by decide)

/-- Three circles: one rigid arrangement, the triangle. -/
theorem card_rigidClasses_three : ENat.card (RigidClasses 3) = 1 :=
  card_rigidClasses_eq_of_latticeCover latticeCover_three (by decide) (by decide)

/-- Four circles: one rigid arrangement, the rhombus (if there are no cores of four
circles). -/
theorem card_rigidClasses_four (h : NoCoresBetween 4 4) : ENat.card (RigidClasses 4) = 1 :=
  card_rigidClasses_eq_of_latticeCover (latticeCover_four h) (by decide) (by decide)

/-- Five circles: one rigid arrangement, the trapezoid (if there are no cores of four or five
circles). -/
theorem card_rigidClasses_five (h : NoCoresBetween 4 5) : ENat.card (RigidClasses 5) = 1 :=
  card_rigidClasses_eq_of_latticeCover (latticeCover_five h) (by decide) (by decide)

/-- Six circles: three rigid arrangements, the parallelogram, the chevron and the big triangle
(if there are no cores of four to six circles). -/
theorem card_rigidClasses_six (h : NoCoresBetween 4 6) : ENat.card (RigidClasses 6) = 3 :=
  card_rigidClasses_eq_of_latticeCover (latticeCover_six h) (by decide) (by decide +kernel)

/-- **Rigid arrangements of three to six circles.** If no rigid arrangement of four to six
circles is a core, there are `1, 1, 1, 3` rigid arrangements of `3, 4, 5, 6` circles up to
isomorphism: the triangle, the rhombus, the trapezoid, and the parallelogram, chevron and big
triangle. -/
theorem card_rigidClasses_le_six (h : NoCoresBetween 4 6) :
    ENat.card (RigidClasses 3) = 1 ∧ ENat.card (RigidClasses 4) = 1 ∧
      ENat.card (RigidClasses 5) = 1 ∧ ENat.card (RigidClasses 6) = 3 :=
  ⟨card_rigidClasses_three, card_rigidClasses_four (noCoresBetween_mono h le_rfl (by norm_num)),
    card_rigidClasses_five (noCoresBetween_mono h le_rfl (by norm_num)), card_rigidClasses_six h⟩

end RigidArrangements
