import RigidArrangements.CornerBasics

/-!
# Lemma E: one exceptional circle

This file proves **Lemma E** of `docs/cores.md` (Section 2). Let `A` be an arrangement in which
every circle touches at least two others and no circle is removable (a core). Suppose every
circle except one, `r`, is a corner (`Arrangement.IsCorner`: extreme in some direction). Then
every other circle touches `r`.

## The argument

Call a contact `ab` *admissible* if neither `a` nor `b` is `r`. For such a contact let
`f(x) = cross (p_b - p_a) (x - p_a)`, which vanishes exactly on the line `ℓ_ab` through the
centers `p_a` and `p_b`, and let `Σ(ab)` be the set of circles strictly on the far side of
`ℓ_ab` from `r`: those `c` with `f(p_c) f(p_r) < 0`. Using the product `f(p_c) f(p_r)` avoids
choosing an orientation of the line.

* **Claim 0.** `p_r` is not on `ℓ_ab`: the corners `a` and `b` would force `p_r` into the
  segment `[p_a, p_b]` (Lemma (4b)), which contains no other center (Lemma 1).
* **Claim 1.** If a circle `x ≠ r` does not touch `r`, its middle neighbour `y` (Lemma 5) gives
  an admissible contact `xy` with `Σ(xy) ≠ ∅`: the other two neighbours of `x` lie strictly on
  opposite sides of `ℓ_xy`, and `p_r` is not on `ℓ_xy` (Claim 0), so one of them is on the
  far side from `r`.
* **Claim 2.** If `x ∈ Σ(ab)`, every neighbour of `x` is in `Σ(ab)` or is `a` or `b`: a
  neighbour on the line is in `[p_a, p_b]` (Lemmas (4b) and 1), and a neighbour on the side of
  `r` would make the contact segments `[p_x, p_y]` and `[p_a, p_b]` cross (Lemmas (4b) and 2).
  In particular `x` does not touch `r`.
* **Claim 3.** For `x ∈ Σ(ab)` and a neighbour `y ≠ r` of `x` (so `y ∈ Σ(ab)` or `y` is `a`
  or `b`, by Claim 2), `Σ(xy) ⊆ Σ(ab)`. Since `x ∈ Σ(ab) \ Σ(xy)`, the set strictly shrinks.

Claims 1–3 show that a contact with `Σ(ab) ≠ ∅` gives another one with a strictly smaller
`Σ`, so by induction on `|Σ(ab)|` every admissible contact has `Σ(ab) = ∅`. If some `x ≠ r`
did not touch `r`, Claim 1 would contradict this.

## Main results

* `Arrangement.adj_of_forall_ne_isCorner` (**Lemma E**): in a core in which every circle
  touches two others, if every circle other than `r` is a corner, then every circle other than
  `r` touches `r`.
-/

namespace RigidArrangements

namespace Arrangement

variable {ι : Type*} {A : Arrangement ι}

/-- The circles strictly on the far side, from `r`, of the line through the centers of `a` and
`b`: those `c` with `f(p_c) f(p_r) < 0`, where `f(x) = cross (p_b - p_a) (x - p_a)`. This is the
set `Σ(ab)` of `docs/cores.md`, Lemma E. -/
private def farSide (A : Arrangement ι) (a b r : ι) : Set ι :=
  {c | cross (A.center b - A.center a) (A.center c - A.center a) *
    cross (A.center b - A.center a) (A.center r - A.center a) < 0}

private theorem mem_farSide {a b r c : ι} :
    c ∈ farSide A a b r ↔ cross (A.center b - A.center a) (A.center c - A.center a) *
      cross (A.center b - A.center a) (A.center r - A.center a) < 0 :=
  Iff.rfl

/-- The circle `r` itself is never on the far side from `r`. -/
private theorem not_mem_farSide_self {a b r : ι} : r ∉ farSide A a b r := fun h =>
  (mul_self_nonneg _).not_gt (mem_farSide.mp h)

/-- The circle `a` lies on the line through `a` and `b`, so it is not on the far side. -/
private theorem not_mem_farSide_left {a b r : ι} : a ∉ farSide A a b r := fun h => by
  rw [mem_farSide, sub_self, cross_zero_right, zero_mul] at h
  exact lt_irrefl _ h

/-- The circle `b` lies on the line through `a` and `b`, so it is not on the far side. -/
private theorem not_mem_farSide_right {a b r : ι} : b ∉ farSide A a b r := fun h => by
  rw [mem_farSide, cross_self, zero_mul] at h
  exact lt_irrefl _ h

/-- **Claim 0** of Lemma E. If every circle other than `r` is a corner, the center of `r` is not
on the line through two touching circles `a, b ≠ r`. -/
private theorem cross_ne_zero_of_forall_ne_isCorner {r : ι} (hr : ∀ i, i ≠ r → A.IsCorner i)
    {a b : ι} (hab : A.contactGraph.Adj a b) (ha : a ≠ r) (hb : b ≠ r) :
    cross (A.center b - A.center a) (A.center r - A.center a) ≠ 0 := fun h =>
  center_not_mem_segment hab (Ne.symm ha) (Ne.symm hb)
    ((hr a ha).mem_segment_of_cross_eq_zero (hr b hb) hab.1 (c := r) (c' := r)
      (left_mem_segment ℝ _ _) h)

/-- **Claim 1** of Lemma E. If every circle other than `r` is a corner and a circle `x ≠ r` does
not touch `r`, then `x` touches a circle `y ≠ r` such that some circle lies strictly on the far
side, from `r`, of the line through `x` and `y`. (Take for `y` the middle neighbour of `x`.) -/
private theorem exists_adj_farSide_nonempty (hT : A.TouchesTwo) (hc : A.IsCore) {r : ι}
    (hr : ∀ i, i ≠ r → A.IsCorner i) {x : ι} (hx : x ≠ r)
    (hxr : ¬ A.contactGraph.Adj x r) :
    ∃ y, A.contactGraph.Adj x y ∧ y ≠ r ∧ (farSide A x y r).Nonempty := by
  obtain ⟨y₁, y₂, y₃, -, -, -, hiff, hneg, hpos⟩ := (hr x hx).exists_middle hT hc
  have hxy₂ : A.contactGraph.Adj x y₂ := (hiff y₂).mpr (Or.inr (Or.inl rfl))
  have hy₂r : y₂ ≠ r := by
    rintro rfl
    exact hxr hxy₂
  refine ⟨y₂, hxy₂, hy₂r, ?_⟩
  rcases (cross_ne_zero_of_forall_ne_isCorner hr hxy₂ hx hy₂r).lt_or_gt with h | h
  · exact ⟨y₃, mem_farSide.mpr (mul_neg_of_pos_of_neg hpos h)⟩
  · exact ⟨y₁, mem_farSide.mpr (mul_neg_of_neg_of_pos hneg h)⟩

/-- **Claim 2** of Lemma E. Let `ab` be a contact with `a, b ≠ r`, where every circle other than
`r` is a corner. Every neighbour `y` of a circle `x` on the far side of the line through `a` and
`b` is itself on the far side, or is `a` or `b`. -/
private theorem adj_mem_farSide {r : ι} (hr : ∀ i, i ≠ r → A.IsCorner i) {a b x y : ι}
    (hab : A.contactGraph.Adj a b) (ha : a ≠ r) (hb : b ≠ r) (hx : x ∈ farSide A a b r)
    (hxy : A.contactGraph.Adj x y) : y ∈ farSide A a b r ∨ y = a ∨ y = b := by
  rw [mem_farSide] at hx
  set z := A.center b - A.center a
  set s := cross z (A.center r - A.center a)
  have hs : s ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hx
    exact lt_irrefl _ hx
  rcases lt_trichotomy (cross z (A.center y - A.center a) * s) 0 with h | h | h
  · exact Or.inl (mem_farSide.mpr h)
  · -- `y` is on the line, hence on the segment `[p_a, p_b]`, hence it is `a` or `b`
    right
    have hy0 : cross z (A.center y - A.center a) = 0 := (mul_eq_zero.mp h).resolve_right hs
    have hseg := (hr a ha).mem_segment_of_cross_eq_zero (hr b hb) hab.1 (c := y) (c' := y)
      (left_mem_segment ℝ _ _) hy0
    by_contra hne
    push Not at hne
    exact center_not_mem_segment hab hne.1 hne.2 hseg
  · -- `y` is on the side of `r`: the contact segments `[p_x, p_y]` and `[p_a, p_b]` cross
    exfalso
    have hxy' : cross z (A.center x - A.center a) * cross z (A.center y - A.center a) < 0 := by
      nlinarith [mul_neg_of_neg_of_pos hx h, mul_self_nonneg s]
    obtain ⟨q, hq, hq0⟩ := exists_mem_openSegment_cross_eq_zero_of_mul_neg hxy'
    have hqxy := openSegment_subset_segment ℝ _ _ hq
    have hqab := (hr a ha).mem_segment_of_cross_eq_zero (hr b hb) hab.1 hqxy hq0
    have hxa : a ≠ x := by
      rintro rfl
      exact not_mem_farSide_left (mem_farSide.mpr hx)
    have hxb : b ≠ x := by
      rintro rfl
      exact not_mem_farSide_right (mem_farSide.mpr hx)
    have hya : a ≠ y := by
      rintro rfl
      rw [sub_self, cross_zero_right, zero_mul] at h
      exact lt_irrefl _ h
    have hyb : b ≠ y := by
      rintro rfl
      rw [cross_self, zero_mul] at h
      exact lt_irrefl _ h
    exact Set.disjoint_left.mp (disjoint_segment_of_adj hab hxy hxa hya hxb hyb) hqab hqxy

/-- **Claim 3** of Lemma E. Let `ab` be a contact with `a, b ≠ r`, where every circle other than
`r` is a corner, let `x ≠ r` be on the far side of the line through `a` and `b`, and let `y ≠ r`
be a neighbour of `x` that is on that far side or is `a` or `b`. Then everything on the far side
of the line through `x` and `y` is on the far side of the line through `a` and `b`. -/
private theorem farSide_subset {r : ι} (hr : ∀ i, i ≠ r → A.IsCorner i) {a b x y : ι}
    (hx : x ∈ farSide A a b r) (hxr : x ≠ r) (hxy : A.contactGraph.Adj x y) (hyr : y ≠ r)
    (hy : y ∈ farSide A a b r ∨ y = a ∨ y = b) : farSide A x y r ⊆ farSide A a b r := by
  intro w hw
  rw [mem_farSide] at hx hw ⊢
  set z := A.center b - A.center a
  set s := cross z (A.center r - A.center a)
  have hs : s ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hx
    exact lt_irrefl _ hx
  have hy' : cross z (A.center y - A.center a) * s ≤ 0 := by
    rcases hy with hy | rfl | rfl
    · exact (mem_farSide.mp hy).le
    · rw [sub_self, cross_zero_right, zero_mul]
    · rw [cross_self, zero_mul]
  by_contra hwn
  push Not at hwn
  -- the line through `x` and `y` separates `w` from `r`: it meets the open segment between them
  obtain ⟨q, hq, hq0⟩ := exists_mem_openSegment_cross_eq_zero_of_mul_neg hw
  -- and the meeting point lies on the contact segment `[p_x, p_y]` (Lemma (4b))
  have hqxy := (hr x hxr).mem_segment_of_cross_eq_zero (hr y hyr) hxy.1
    (openSegment_subset_segment ℝ _ _ hq) hq0
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hq
  obtain ⟨γ, δ, hγ, hδ, hγδ, hq'⟩ := hqxy
  -- evaluate `f(q) f(p_r)` along both segments: it is positive on `(p_w, p_r)` but not
  -- positive on `[p_x, p_y]`
  have e1 := cross_add_smul_sub z (A.center w) (A.center r) (A.center a) hαβ
  have e2 := cross_add_smul_sub z (A.center x) (A.center y) (A.center a) hγδ
  rw [hq'] at e2
  have e3 : α * (cross z (A.center w - A.center a) * s) + β * (s * s) =
      γ * (cross z (A.center x - A.center a) * s) +
        δ * (cross z (A.center y - A.center a) * s) := by
    linear_combination s * (e2.symm.trans e1).symm
  have h1 := mul_nonneg hα.le hwn
  have h2 := mul_pos hβ (mul_self_pos.mpr hs)
  have h3 := mul_nonpos_of_nonneg_of_nonpos hγ hx.le
  have h4 := mul_nonpos_of_nonneg_of_nonpos hδ hy'
  linarith

/-- Lemma E, induction step on `|Σ(ab)|`: if every circle other than `r` is a corner, no circle
lies strictly on the far side, from `r`, of the line through two touching circles `a, b ≠ r`
with at most `n` circles on that far side. -/
private theorem farSide_eq_empty [Finite ι] (hT : A.TouchesTwo) (hc : A.IsCore) {r : ι}
    (hr : ∀ i, i ≠ r → A.IsCorner i) (n : ℕ) :
    ∀ a b, A.contactGraph.Adj a b → a ≠ r → b ≠ r → (farSide A a b r).ncard ≤ n →
      farSide A a b r = ∅ := by
  induction n with
  | zero =>
    intro a b _ _ _ h
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp h)
  | succ n ih =>
    intro a b hab ha hb hle
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hxr : x ≠ r := by
      rintro rfl
      exact not_mem_farSide_self hx
    -- Claim 2: `x` does not touch `r`
    have hxnr : ¬ A.contactGraph.Adj x r := fun h => by
      rcases adj_mem_farSide hr hab ha hb hx h with h | h | h
      · exact not_mem_farSide_self h
      · exact ha h.symm
      · exact hb h.symm
    -- Claim 1: the middle neighbour `y` of `x` gives a contact with a nonempty far side
    obtain ⟨y, hxy, hyr, hne'⟩ := exists_adj_farSide_nonempty hT hc hr hxr hxnr
    -- Claim 3: that far side is strictly smaller
    have hsub := farSide_subset hr hx hxr hxy hyr (adj_mem_farSide hr hab ha hb hx hxy)
    have hlt := Set.ncard_lt_ncard
      ((Set.ssubset_iff_of_subset hsub).mpr ⟨x, hx, not_mem_farSide_left⟩) (Set.toFinite _)
    exact hne'.ne_empty (ih x y hxy hxr hyr (by omega))

/-- **Lemma E.** Let `A` be a finite arrangement in which every circle touches at least two
others and no circle is removable. If every circle other than `r` is a corner, then every circle
other than `r` touches `r`. -/
theorem adj_of_forall_ne_isCorner [Finite ι] (hT : A.TouchesTwo) (hc : A.IsCore) {r : ι}
    (hr : ∀ i, i ≠ r → A.IsCorner i) {x : ι} (hx : x ≠ r) : A.contactGraph.Adj x r := by
  by_contra hxr
  obtain ⟨y, hxy, hyr, w, hw⟩ := exists_adj_farSide_nonempty hT hc hr hx hxr
  rw [farSide_eq_empty hT hc hr _ x y hxy hx hyr le_rfl] at hw
  exact hw

end Arrangement

end RigidArrangements
