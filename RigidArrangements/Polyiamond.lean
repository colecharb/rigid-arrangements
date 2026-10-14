import RigidArrangements.Flex
import RigidArrangements.Lattice
import RigidArrangements.Henneberg
import RigidArrangements.Isometry

/-!
# Polyiamonds, hexiamonds, and the square grid

The problem statement suggests comparing rigid arrangements with hexominoes. This file makes the
comparison precise and shows where it breaks down.

**Squares are the wrong cells.** Circles centered on a square grid can always be sheared: no
arrangement of at least three circles on a square grid of spacing `2` is rigid
(`Arrangement.not_isRigid_of_squareGrid`, `Arrangement.IsSquareGrid.not_isRigid`). So literal
polyominoes, hexominoes included, never give rigid arrangements of three or more circles,
whether the circles sit at the centers or at the corners of the squares.

**Triangles are the right cells, but the match is not exact.** The triangular lattice (see
`RigidArrangements.Lattice`) is tiled by equilateral triangles of side `2`, the *cells*. A
*polyiamond* is a finite edge-connected set of cells. Put a circle at each corner of each cell:
the result is always rigid (`IsPolyiamond.isRigid`), because the polyiamond can be grown one cell
at a time, and each new cell adds at most one circle, touching the two circles at the ends of
the shared edge (a Henneberg step). But different polyiamonds can have the same corners:

* the fan of five cells around a point and the hexagon of six cells have the same `7` corners
  (`cornerSet_fanPentiamond`), so even the number of cells is not determined by the circles;
* three different hexiamonds, each a fan plus one outer cell, have the same `8` corners
  (`hexiamondCorners_two`, `hexiamondCorners_three`).

So the twelve hexiamonds give only ten arrangements, nine of them with `8` circles
(`hexiamondCorners_classes`), and these nine are pairwise non-isomorphic rigid arrangements of
eight circles (`exists_injective_rigidClasses_eight`). This matches the exploratory census
(nine rigid arrangements of eight circles, against twelve hexiamonds). Two further breakdowns
were found by computer exploration and are recorded in `docs/problem.md` and
`docs/journal.md`, but are not proved here: a rigid lattice arrangement of `13` circles that is
not the corner set of any polyiamond, and a rigid arrangement of `11` circles that lies on no
triangular lattice.

## Main definitions

* `TriCell`: a cell `up p` or `down p` of the triangular lattice, with its three `corners`.
* `cornerSet P`: all corners of the cells of `P`; `IsPolyiamond P`: `P` is edge-connected.
* `IsGrowthList`: a list of cells, each but the last sharing an edge with a later one; a
  decidable certificate that the cells form a polyiamond (`IsGrowthList.isPolyiamond`).
* `latSym k`, `k : Fin 12`: the twelve symmetries of the lattice fixing the origin (rotations by
  multiples of `60°` and reflections). `SitesCongr S T`: some lattice symmetry followed by a
  translation carries the set of lattice points `S` onto `T`. `CellsCongr P Q`: the same for
  sets of cells. Both are decidable: the translation is determined by the sums of the points
  (`exists_image_add_smul_iff`).
* `pairNormSum F S`: the sum of `F (eNorm (v - w))` over pairs of points of `S`, an invariant of
  both congruence and isomorphism of arrangements.
* `Arrangement.ofSites S`: one circle at each point of a finite set `S` of lattice points.
* `fanPentiamond`, `hexagonHexiamond`, `hexiamond i` (`i : Fin 12`), `hexiamondCorners i`.

## Main results

* `IsPolyiamond.isRigid`: the corner set of a polyiamond is a rigid arrangement.
* `SitesCongr.iso`: congruent lattice sets give isomorphic arrangements.
* `cellsCongr_hexiamond_iff`: the twelve `hexiamond i` are pairwise non-congruent.
* `cornerSet_fanPentiamond`, `card_cornerSet_hexagonHexiamond`: fan and hexagon share 7 corners.
* `hexiamondCorners_two`, `hexiamondCorners_three`, `card_hexiamondCorners`: the hexiamonds
  `1, 2, 3` have one common 8-point corner set; all hexiamonds but the hexagon have 8 corners.
* `iso_ofSites_hexiamondCorners_iff`, `sitesCongr_hexiamondCorners_iff`: two hexiamonds give
  isomorphic (equivalently, congruent) corner arrangements exactly when they are equal or both
  among `1, 2, 3`.
* `hexiamondCorners_classes`: the hexiamonds have exactly `10` corner sets, pairwise
  non-isomorphic, one with `7` points and `9` with `8`.
* `exists_injective_rigidClasses_eight`: at least nine rigid arrangements of `8` circles, up to
  isomorphism, come from hexiamonds.
* `Arrangement.not_isRigid_of_squareGrid`, `Arrangement.IsSquareGrid.not_isRigid`: no rigid
  arrangement of three or more circles lies on a square grid of spacing `2`.

All finite checks are kernel computations (`decide`, `decide +kernel`); the slowest takes a few
seconds.
That the list `hexiamond` contains every hexiamond is the classical count (OEIS A000577), which
is not reproved here.
-/

namespace RigidArrangements

/-! ### Cells of the triangular lattice -/

/-- A *cell* of the triangular lattice: one of the equilateral triangles of side `2` that tile
the plane, with corners at lattice points. In lattice coordinates (see `latticePoint`), with
`e₁ = (1, 0)` and `e₂ = (0, 1)`, the cell `up p` has corners `p, p + e₁, p + e₂` (it points
up) and the cell `down p` has corners `p + e₁, p + e₂, p + e₁ + e₂` (it points down). -/
inductive TriCell
  | up (p : ℤ × ℤ)
  | down (p : ℤ × ℤ)
  deriving DecidableEq

namespace TriCell

/-- The three corners of a cell. -/
def corners : TriCell → Finset (ℤ × ℤ)
  | up p => {p, p + (1, 0), p + (0, 1)}
  | down p => {p + (1, 0), p + (0, 1), p + (1, 1)}

/-- Two distinct corners of a cell are neighbouring lattice points: circles centered there
touch. -/
theorem eNorm_sub_eq_one {c : TriCell} {v w : ℤ × ℤ} (hv : v ∈ c.corners) (hw : w ∈ c.corners)
    (hvw : v ≠ w) : eNorm (v - w) = 1 := by
  cases c with
  | up p =>
    simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hvw
      | (simp only [eNorm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring)
  | down p =>
    simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hvw
      | (simp only [eNorm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring)

/-- Three times the centroid of a cell, in lattice coordinates: the sum of its corners
(`TriCell.sum_corners`). A lattice symmetry moves cells as it moves their centroids, so we use
centroids to compare sets of cells up to symmetry. -/
def centroid3 : TriCell → ℤ × ℤ
  | up p => (3 * p.1 + 1, 3 * p.2 + 1)
  | down p => (3 * p.1 + 2, 3 * p.2 + 2)

theorem sum_corners (c : TriCell) : ∑ v ∈ c.corners, v = c.centroid3 := by
  cases c with
  | up p =>
    rw [corners, Finset.sum_insert (by simp [Prod.ext_iff]),
      Finset.sum_insert (by simp [Prod.ext_iff]), Finset.sum_singleton]
    exact Prod.ext (by simp only [Prod.fst_add, centroid3]; ring)
      (by simp only [Prod.snd_add, centroid3]; ring)
  | down p =>
    rw [corners, Finset.sum_insert (by simp [Prod.ext_iff]),
      Finset.sum_insert (by simp [Prod.ext_iff]), Finset.sum_singleton]
    exact Prod.ext (by simp only [Prod.fst_add, centroid3]; ring)
      (by simp only [Prod.snd_add, centroid3]; ring)

/-- A cell is determined by its centroid. -/
theorem centroid3_injective : Function.Injective centroid3 := by
  intro c d h
  cases c <;> cases d <;> simp only [centroid3, Prod.mk.injEq] at h <;>
    first
    | (congr 1; exact Prod.ext (by omega) (by omega))
    | omega

/-- The *cell graph*: two cells are adjacent when they share an edge, that is, two corners. -/
def graph : SimpleGraph TriCell where
  Adj c d := c ≠ d ∧ 2 ≤ (c.corners ∩ d.corners).card
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [Finset.inter_comm]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun c d =>
  inferInstanceAs (Decidable (c ≠ d ∧ 2 ≤ (c.corners ∩ d.corners).card))

end TriCell

/-- The *corner set* of a finite set of cells: all corners of all its cells. -/
def cornerSet (P : Finset TriCell) : Finset (ℤ × ℤ) :=
  P.biUnion TriCell.corners

/-- A *polyiamond*: a nonempty finite set of cells that is connected through shared edges. -/
def IsPolyiamond (P : Finset TriCell) : Prop :=
  (TriCell.graph.induce (P : Set TriCell)).Connected

/-! ### Growth lists: certificates of edge-connectedness -/

/-- A *growth list*: a nonempty list of cells in which every cell but the last shares an edge
with some cell further right. Read from right to left, it builds a polyiamond one cell at a
time, so it certifies that its cells are edge-connected (`IsGrowthList.isPolyiamond`). -/
def IsGrowthList : List TriCell → Prop
  | [] => False
  | c :: l => l = [] ∨ (IsGrowthList l ∧ ∃ d ∈ l, TriCell.graph.Adj c d)

instance decidableIsGrowthList : DecidablePred IsGrowthList
  | [] => isFalse fun h => h
  | c :: l =>
    have := decidableIsGrowthList l
    inferInstanceAs (Decidable (l = [] ∨ (IsGrowthList l ∧ ∃ d ∈ l, TriCell.graph.Adj c d)))

/-- The cells of a growth list form a polyiamond. -/
theorem IsGrowthList.isPolyiamond {l : List TriCell} (h : IsGrowthList l) :
    IsPolyiamond l.toFinset := by
  induction l with
  | nil => exact h.elim
  | cons c l ih =>
    rcases h with rfl | ⟨hl, d, hd, hcd⟩
    · have : ((([c] : List TriCell).toFinset : Finset TriCell) : Set TriCell) = {c} := by simp
      rw [IsPolyiamond, this, SimpleGraph.induce_singleton_eq_top]
      exact SimpleGraph.connected_top
    · have hset : (((c :: l).toFinset : Finset TriCell) : Set TriCell) =
          {c} ∪ ((l.toFinset : Finset TriCell) : Set TriCell) := by
        simp
      rw [IsPolyiamond, hset]
      exact SimpleGraph.connected_induce_union (v := c) (w := d)
        SimpleGraph.Preconnected.of_subsingleton (ih hl).preconnected rfl
        (by simpa using hd) hcd

/-! ### Symmetries of the triangular lattice -/

/-- Rotation of the lattice by `60°` about the origin, in lattice coordinates: `e₁ ↦ e₂` and
`e₂ ↦ e₂ - e₁`. -/
def latRot (v : ℤ × ℤ) : ℤ × ℤ :=
  (-v.2, v.1 + v.2)

/-- Reflection of the lattice in the line through `0` and `e₁ + e₂` (the line at `30°`). It
swaps `e₁` and `e₂`. -/
def latRefl (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.2, v.1)

/-- The twelve symmetries of the triangular lattice that fix the origin: the six rotations
`latRot^[k]` (`k < 6`) and the six reflections `latRot^[k - 6] ∘ latRefl` (`6 ≤ k < 12`). -/
def latSym (k : Fin 12) (v : ℤ × ℤ) : ℤ × ℤ :=
  latRot^[k.val % 6] (if k.val < 6 then v else latRefl v)

/-- The twelve symmetries are different maps. -/
theorem latSym_left_injective : Function.Injective latSym := by
  have key : ∀ k l : Fin 12, latSym k (1, 0) = latSym l (1, 0) →
      latSym k (0, 1) = latSym l (0, 1) → k = l := by
    decide +kernel
  exact fun k l h => key k l (congrFun h _) (congrFun h _)

theorem latRot_injective : Function.Injective latRot := by
  intro v w h
  simp only [latRot, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

theorem latRefl_injective : Function.Injective latRefl := by
  intro v w h
  simp only [latRefl, Prod.mk.injEq] at h
  exact Prod.ext h.2 h.1

theorem latSym_injective (k : Fin 12) : Function.Injective (latSym k) := by
  intro v w h
  have h' := (latRot_injective.iterate (k.val % 6)) h
  split_ifs at h' with hk
  · exact h'
  · exact latRefl_injective h'

theorem latRot_sub (v w : ℤ × ℤ) : latRot (v - w) = latRot v - latRot w := by
  simp only [latRot, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
  exact Prod.ext (by ring) (by ring)

theorem latRefl_sub (v w : ℤ × ℤ) : latRefl (v - w) = latRefl v - latRefl w :=
  rfl

/-- The lattice symmetries are additive. -/
theorem latSym_sub (k : Fin 12) (v w : ℤ × ℤ) :
    latSym k (v - w) = latSym k v - latSym k w := by
  have hit : ∀ (n : ℕ) (v w : ℤ × ℤ), latRot^[n] (v - w) = latRot^[n] v - latRot^[n] w := by
    intro n
    induction n with
    | zero => intro v w; rfl
    | succ n ih => intro v w; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, latRot_sub, ih]
  unfold latSym
  split_ifs
  · exact hit _ v w
  · rw [latRefl_sub, hit]

theorem eNorm_latRot (v : ℤ × ℤ) : eNorm (latRot v) = eNorm v := by
  simp only [eNorm, latRot]
  ring

theorem eNorm_latRefl (v : ℤ × ℤ) : eNorm (latRefl v) = eNorm v := by
  simp only [eNorm, latRefl]
  ring

/-- The lattice symmetries preserve the Eisenstein norm, hence all distances. -/
theorem eNorm_latSym (k : Fin 12) (v : ℤ × ℤ) : eNorm (latSym k v) = eNorm v := by
  have hit : ∀ (n : ℕ) (v : ℤ × ℤ), eNorm (latRot^[n] v) = eNorm v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih => intro v; rw [Function.iterate_succ_apply, ih, eNorm_latRot]
  unfold latSym
  split_ifs
  · exact hit _ v
  · rw [hit, eNorm_latRefl]

/-! ### Congruence of lattice sets and of cell sets -/

/-- Two finite sets of lattice points are *congruent under a lattice symmetry* when one is
carried onto the other by a symmetry of the triangular lattice: one of the twelve symmetries
`latSym k` fixing the origin, followed by a translation. -/
def SitesCongr (S T : Finset (ℤ × ℤ)) : Prop :=
  ∃ (k : Fin 12) (t : ℤ × ℤ), S.image (fun v => latSym k v + t) = T

/-- Two finite sets of cells are *congruent under a lattice symmetry* when some symmetry of the
lattice carries the cells of one onto the cells of the other. A symmetry `v ↦ latSym k v + t`
moves three times the centroid of a cell by `w ↦ latSym k w + 3 t`, and a cell is determined
by its centroid (`TriCell.centroid3_injective`), so we compare the centroids. -/
def CellsCongr (P Q : Finset TriCell) : Prop :=
  ∃ (k : Fin 12) (t : ℤ × ℤ),
    (P.image TriCell.centroid3).image (fun v => latSym k v + (3 : ℤ) • t) =
      Q.image TriCell.centroid3

/-- The only possible translation `t` with `S.image (g · + m • t) = T`, when `g` is injective,
`m ≠ 0` and `S` is nonempty: comparing the sums of the points of both sides gives
`card S * m * t = ∑ T - ∑ g S`. -/
def transCand (g : ℤ × ℤ → ℤ × ℤ) (m : ℤ) (S T : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  ((∑ v ∈ T, v - ∑ v ∈ S, g v).1 / (m * S.card), (∑ v ∈ T, v - ∑ v ∈ S, g v).2 / (m * S.card))

/-- Deciding congruence: the translation is determined by the sums of the points, so only one
candidate `transCand` needs to be checked. -/
theorem exists_image_add_smul_iff {g : ℤ × ℤ → ℤ × ℤ} (hg : Function.Injective g) (m : ℤ)
    (S T : Finset (ℤ × ℤ)) :
    (∃ t : ℤ × ℤ, S.image (fun v => g v + m • t) = T) ↔
      S.image (fun v => g v + m • transCand g m S T) = T := by
  refine ⟨fun ⟨t, ht⟩ => ?_, fun h => ⟨_, h⟩⟩
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa using ht
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using ht
  suffices transCand g m S T = t by rw [this]; exact ht
  have hinj : Set.InjOn (fun v => g v + m • t) S := fun x _ y _ h => hg (add_right_cancel h)
  have hsum : ∑ v ∈ T, v - ∑ v ∈ S, g v = S.card • (m • t) := by
    rw [← ht, Finset.sum_image hinj, Finset.sum_add_distrib, Finset.sum_const, add_sub_cancel_left]
  have hc : m * (S.card : ℤ) ≠ 0 := mul_ne_zero hm (by exact_mod_cast hS.card_pos.ne')
  have key : ∀ x : ℤ, (S.card : ℤ) * (m * x) / (m * S.card) = x := fun x => by
    rw [show (S.card : ℤ) * (m * x) = (m * S.card) * x by ring, Int.mul_ediv_cancel_left _ hc]
  rw [transCand, hsum, Prod.smul_fst, Prod.smul_snd, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, key, key]

instance : DecidableRel SitesCongr := fun S T =>
  decidable_of_iff
    (∃ k : Fin 12, S.image (fun v => latSym k v + (1 : ℤ) • transCand (latSym k) 1 S T) = T) <|
    exists_congr fun k => by
      rw [← exists_image_add_smul_iff (latSym_injective k)]
      simp only [one_smul]

instance : DecidableRel CellsCongr := fun P Q =>
  decidable_of_iff (∃ k : Fin 12, (P.image TriCell.centroid3).image (fun v => latSym k v +
      (3 : ℤ) • transCand (latSym k) 3 (P.image TriCell.centroid3) (Q.image TriCell.centroid3))
      =
      Q.image TriCell.centroid3) <|
    exists_congr fun k => (exists_image_add_smul_iff (latSym_injective k) 3 _ _).symm

theorem latSym_zero (v : ℤ × ℤ) : latSym 0 v = v :=
  rfl

theorem SitesCongr.refl (S : Finset (ℤ × ℤ)) : SitesCongr S S :=
  ⟨0, 0, by simp [latSym_zero]⟩

theorem CellsCongr.refl (P : Finset TriCell) : CellsCongr P P :=
  ⟨0, 0, by simp [latSym_zero]⟩

/-! ### A congruence invariant -/

/-- The sum of `F (eNorm (v - w))` over all ordered pairs `(v, w)` of points of `S`. For
`F = id` this is a quarter of the sum of all squared distances between the circles of
`Arrangement.ofSites S`. It is unchanged by lattice symmetries (`SitesCongr.pairNormSum_eq`)
and by isomorphisms of arrangements (`Arrangement.Iso.pairNormSum_eq`), so it can tell
non-congruent sets apart. -/
def pairNormSum (F : ℤ → ℤ) (S : Finset (ℤ × ℤ)) : ℤ :=
  ∑ v ∈ S, ∑ w ∈ S, F (eNorm (v - w))

theorem pairNormSum_image_latSym (F : ℤ → ℤ) (k : Fin 12) (t : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    pairNormSum F (S.image fun v => latSym k v + t) = pairNormSum F S := by
  have hinj : Set.InjOn (fun v => latSym k v + t) S := fun x _ y _ h =>
    latSym_injective k (add_right_cancel h)
  simp only [pairNormSum, Finset.sum_image hinj, add_sub_add_right_eq_sub, ← latSym_sub,
    eNorm_latSym]

theorem SitesCongr.pairNormSum_eq {S T : Finset (ℤ × ℤ)} (h : SitesCongr S T) (F : ℤ → ℤ) :
    pairNormSum F S = pairNormSum F T := by
  obtain ⟨k, t, rfl⟩ := h
  exact (pairNormSum_image_latSym F k t S).symm

theorem CellsCongr.pairNormSum_eq {P Q : Finset TriCell} (h : CellsCongr P Q) (F : ℤ → ℤ) :
    pairNormSum F (P.image TriCell.centroid3) = pairNormSum F (Q.image TriCell.centroid3) := by
  obtain ⟨k, t, h⟩ := h
  rw [← h, pairNormSum_image_latSym]

/-! ### Circles on lattice sites -/

namespace Arrangement

/-- The arrangement with one circle at each point of a finite set `S` of lattice points
(centered at `latticePoint v`), labeled by the points themselves. -/
noncomputable def ofSites (S : Finset (ℤ × ℤ)) : Arrangement S where
  center v := latticePoint v
  nonoverlap _ _ hvw := two_le_dist_latticePoint fun h => hvw (Subtype.ext h)

@[simp]
theorem ofSites_center (S : Finset (ℤ × ℤ)) (v : S) : (ofSites S).center v = latticePoint v :=
  rfl

/-- Circles at lattice points touch exactly when the points are neighbours in the lattice. -/
theorem tangent_ofSites_iff {S : Finset (ℤ × ℤ)} (v w : S) :
    Tangent (ofSites S).center v w ↔ eNorm (v.1 - w.1) = 1 :=
  tangent_latticePoint_iff _ _

/-- Lattice points with differences of the same `eNorm` are at the same distance. -/
theorem dist_latticePoint_eq_iff (v w v' w' : ℤ × ℤ) :
    dist (latticePoint v) (latticePoint w) = dist (latticePoint v') (latticePoint w') ↔
      eNorm (v - w) = eNorm (v' - w') := by
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_latticePoint_sq, dist_latticePoint_sq]
  constructor
  · intro h
    exact_mod_cast (mul_left_cancel₀ (by norm_num : (4 : ℝ) ≠ 0) h)
  · intro h
    rw [h]

/-- `pairNormSum` as a sum over the points of `S` viewed as a type. -/
private theorem pairNormSum_eq_sum_subtype (F : ℤ → ℤ) (S : Finset (ℤ × ℤ)) :
    pairNormSum F S = ∑ v : S, ∑ w : S, F (eNorm (v.1 - w.1)) := by
  rw [pairNormSum, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun v _ => (Finset.sum_coe_sort S _).symm

/-- **Isomorphic lattice arrangements have the same `pairNormSum`.** An isomorphism keeps all
distances, hence all values `eNorm (v - w)`, and only relabels the pairs. -/
theorem Iso.pairNormSum_eq {S T : Finset (ℤ × ℤ)} (h : (ofSites S).Iso (ofSites T))
    (F : ℤ → ℤ) : pairNormSum F S = pairNormSum F T := by
  obtain ⟨e, he⟩ := h
  rw [congruent_iff_dist_eq] at he
  have key : ∀ v w : S, eNorm ((e v).1 - (e w).1) = eNorm (v.1 - w.1) := fun v w =>
    ((dist_latticePoint_eq_iff _ _ _ _).mp (he v w)).symm
  rw [pairNormSum_eq_sum_subtype, pairNormSum_eq_sum_subtype, ← e.sum_comp]
  simp only [← e.sum_comp (fun w => F (eNorm (_ - w.1))), key]

/-- `ofSites S` with its circles relabeled by `Fin n`, where `n` is the number of points of `S`
(in some order), as needed for `RigidClasses n`. -/
noncomputable def ofSitesFin (S : Finset (ℤ × ℤ)) {n : ℕ} (hn : S.card = n) :
    Arrangement (Fin n) :=
  (ofSites S).comap (S.equivFinOfCardEq hn).symm (Equiv.injective _)

/-- Relabeling does not change the isomorphism class. -/
theorem iso_ofSitesFin (S : Finset (ℤ × ℤ)) {n : ℕ} (hn : S.card = n) :
    (ofSitesFin S hn).Iso (ofSites S) :=
  ⟨(S.equivFinOfCardEq hn).symm, Congruent.refl _⟩

theorem IsRigid.ofSitesFin {S : Finset (ℤ × ℤ)} (h : (ofSites S).IsRigid) {n : ℕ}
    (hn : S.card = n) : (Arrangement.ofSitesFin S hn).IsRigid :=
  Iso.isRigid (Iso.symm (iso_ofSitesFin S hn)) h

end Arrangement

/-- **Lattice symmetries are isometries**: sets of lattice points that are congruent under a
lattice symmetry give isomorphic arrangements. -/
theorem SitesCongr.iso {S T : Finset (ℤ × ℤ)} (h : SitesCongr S T) :
    (Arrangement.ofSites S).Iso (Arrangement.ofSites T) := by
  obtain ⟨k, t, h⟩ := h
  have hinj : Function.Injective fun v => latSym k v + t := fun x y hxy =>
    latSym_injective k (add_right_cancel hxy)
  have hmem : ∀ v ∈ S, latSym k v + t ∈ T := fun v hv => h ▸ Finset.mem_image_of_mem _ hv
  let e : S ≃ T := Equiv.ofBijective (fun v => ⟨latSym k v + t, hmem v v.2⟩) <| by
    refine ⟨fun v w hvw => Subtype.ext (hinj (congrArg Subtype.val hvw)), fun w => ?_⟩
    have hw : w.1 ∈ S.image fun v => latSym k v + t := by
      rw [h]
      exact w.2
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  refine ⟨e, ?_⟩
  rw [congruent_iff_dist_eq]
  intro v w
  change dist (latticePoint v) (latticePoint w) =
    dist (latticePoint (latSym k v + t)) (latticePoint (latSym k w + t))
  rw [Arrangement.dist_latticePoint_eq_iff, add_sub_add_right_eq_sub, ← latSym_sub, eNorm_latSym]

/-! ### Corner sets of polyiamonds are rigid -/

namespace Arrangement

/-- **Henneberg step on the lattice.** Adding to a rigid lattice arrangement a circle at a
lattice point `x` that touches two of its circles keeps it rigid. -/
theorem IsRigid.ofSites_insert {S : Finset (ℤ × ℤ)} (h : (ofSites S).IsRigid)
    {x u w : ℤ × ℤ} (hu : u ∈ S) (hw : w ∈ S) (huw : u ≠ w) (hxu : eNorm (x - u) = 1)
    (hxw : eNorm (x - w) = 1) : (ofSites (insert x S)).IsRigid := by
  let f : S → (insert x S : Finset (ℤ × ℤ)) := fun v => ⟨v, Finset.mem_insert_of_mem v.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (show (f a).1 = (f b).1 from congrArg Subtype.val hab)
  refine IsRigid.of_comap (f := f) (hf := hf) h (i₀ := ⟨x, Finset.mem_insert_self x S⟩)
    (fun v hv => ?_) (u := ⟨u, hu⟩) (w := ⟨w, hw⟩) ((tangent_ofSites_iff _ _).mpr hxu)
    ((tangent_ofSites_iff _ _).mpr hxw) fun h' => huw (congrArg Subtype.val h')
  have hvx : v.1 ≠ x := fun e => hv (Subtype.ext e)
  have hvS : v.1 ∈ S := (Finset.mem_insert.mp v.2).resolve_left hvx
  exact ⟨⟨v.1, hvS⟩, rfl⟩

/-- Adding several circles, each of which touches the same two circles `u ≠ w` of a rigid
lattice arrangement, keeps it rigid. -/
theorem IsRigid.ofSites_union {S C : Finset (ℤ × ℤ)} (h : (ofSites S).IsRigid) {u w : ℤ × ℤ}
    (hu : u ∈ S) (hw : w ∈ S) (huw : u ≠ w)
    (hC : ∀ x ∈ C, x ∉ S → eNorm (x - u) = 1 ∧ eNorm (x - w) = 1) :
    (ofSites (C ∪ S)).IsRigid := by
  induction C using Finset.induction_on with
  | empty =>
    rw [Finset.empty_union]
    exact h
  | insert x C _ ih =>
    rw [Finset.insert_union]
    have ih' := ih fun y hy hyS => hC y (Finset.mem_insert_of_mem hy) hyS
    by_cases hx : x ∈ S
    · rwa [Finset.insert_eq_of_mem (Finset.mem_union_right C hx)]
    · obtain ⟨h1, h2⟩ := hC x (Finset.mem_insert_self x C) hx
      exact ih'.ofSites_insert (Finset.mem_union_right C hu) (Finset.mem_union_right C hw) huw
        h1 h2

/-- The three circles at the corners of a cell touch pairwise, so they are rigid. -/
theorem isRigid_ofSites_corners (c : TriCell) : (ofSites c.corners).IsRigid :=
  isRigid_of_forall_tangent _ fun v w hvw => (tangent_ofSites_iff v w).mpr
    (TriCell.eNorm_sub_eq_one v.2 w.2 fun e => hvw (Subtype.ext e))

/-- Adding to a set of cells `Q` a cell `c` that shares an edge with a cell of `Q` keeps the
corner arrangement rigid: `c` adds at most one corner, which touches both ends of the shared
edge. -/
theorem IsRigid.ofSites_cornerSet_insert {Q : Finset TriCell}
    (h : (ofSites (cornerSet Q)).IsRigid) {c d : TriCell} (hd : d ∈ Q)
    (hcd : TriCell.graph.Adj c d) : (ofSites (cornerSet (insert c Q))).IsRigid := by
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hcd.2
  rw [Finset.mem_inter] at hu hw
  have hQ : ∀ y ∈ d.corners, y ∈ cornerSet Q := fun y hy => Finset.mem_biUnion.mpr ⟨d, hd, hy⟩
  rw [cornerSet, Finset.biUnion_insert]
  refine h.ofSites_union (hQ u hu.2) (hQ w hw.2) huw fun x hx hxQ => ⟨?_, ?_⟩
  · exact TriCell.eNorm_sub_eq_one hx hu.1 fun e => hxQ (e ▸ hQ u hu.2)
  · exact TriCell.eNorm_sub_eq_one hx hw.1 fun e => hxQ (e ▸ hQ w hw.2)

end Arrangement

/-- **The corner set of a polyiamond is rigid.** Grow the polyiamond one cell at a time, each new
cell sharing an edge with an earlier one: each step adds at most one circle, touching the two
circles at the ends of the shared edge (a Henneberg step), starting from the three mutually
touching circles at the corners of one cell. -/
theorem IsPolyiamond.isRigid {P : Finset TriCell} (hP : IsPolyiamond P) :
    (Arrangement.ofSites (cornerSet P)).IsRigid := by
  -- grow from any rigid nonempty `Q ⊆ P`, by induction on the number of missing cells
  have grow : ∀ (n : ℕ) (Q : Finset TriCell), Q ⊆ P → Q.Nonempty → (P \ Q).card = n →
      (Arrangement.ofSites (cornerSet Q)).IsRigid →
        (Arrangement.ofSites (cornerSet P)).IsRigid := by
    intro n
    induction n with
    | zero =>
      intro Q hQP _ hn hQ
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hn
      rwa [← Finset.Subset.antisymm hn hQP] at hQ
    | succ n ih =>
      intro Q hQP ⟨d₀, hd₀⟩ hn hQ
      obtain ⟨c₀, hc₀⟩ : (P \ Q).Nonempty := Finset.card_pos.mp (by omega)
      rw [Finset.mem_sdiff] at hc₀
      -- a cell `c ∈ P \ Q` sharing an edge with a cell `d ∈ Q`
      obtain ⟨p⟩ := hP.preconnected ⟨d₀, hQP hd₀⟩ ⟨c₀, hc₀.1⟩
      obtain ⟨D, -, hD1, hD2⟩ := p.exists_boundary_dart {x | x.1 ∈ Q} hd₀ hc₀.2
      have hd : D.fst.1 ∈ Q := hD1
      have hc : D.snd.1 ∈ P \ Q := Finset.mem_sdiff.mpr ⟨D.snd.2, hD2⟩
      refine ih (insert D.snd.1 Q) (Finset.insert_subset D.snd.2 hQP)
        (Finset.insert_nonempty _ _) ?_ (hQ.ofSites_cornerSet_insert hd D.adj.symm)
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hc, hn, Nat.add_sub_cancel]
  obtain ⟨⟨c, hc⟩⟩ := hP.nonempty
  refine grow _ {c} (Finset.singleton_subset_iff.mpr hc) (Finset.singleton_nonempty c) rfl ?_
  rw [cornerSet, Finset.singleton_biUnion]
  exact Arrangement.isRigid_ofSites_corners c

/-! ### The hexiamonds -/

section Hexiamonds

open TriCell

/-- The *fan pentiamond*: five of the six cells around the origin, all but `down (0, -1)`. -/
def fanPentiamond : List TriCell :=
  [up (0, -1), down (-1, -1), up (-1, 0), down (-1, 0), up (0, 0)]

/-- The *hexagon*: the six cells around the origin. -/
def hexagonHexiamond : List TriCell :=
  down (0, -1) :: fanPentiamond

/-- The twelve free hexiamonds, one representative of each, as growth lists.

* `hexiamond 0` is the hexagon.
* `hexiamond 1`, `hexiamond 2`, `hexiamond 3` are a fan pentiamond plus one cell outside the
  hexagon. We fix the outer cell `down (0, 0)`, across the outer edge of `up (0, 0)`, and remove
  from the hexagon the cell opposite `up (0, 0)` (`hexiamond 1`), a cell two steps away from
  `up (0, 0)` around the hexagon (`hexiamond 2`), or a neighbour of `up (0, 0)` (`hexiamond 3`):
  see `hexiamond_one`, `hexiamond_two`, `hexiamond_three`, and
  `cellsCongr_erase_hexagon_fanPentiamond`. With these representatives the three corner sets are
  literally equal (`hexiamondCorners_two`, `hexiamondCorners_three`).
* `hexiamond 4`, …, `hexiamond 11` are the other eight hexiamonds; `hexiamond 11` is the bar,
  six cells in a straight strip.

`cellsCongr_hexiamond_iff` checks that no two of them are congruent. That there are no other
hexiamonds is the classical count (OEIS A000577), which we do not reprove. -/
def hexiamond : Fin 12 → List TriCell :=
  ![hexagonHexiamond,
    [up (-1, 0), down (-1, 0), up (0, -1), down (0, -1), down (0, 0), up (0, 0)],
    [down (-1, -1), up (0, -1), down (0, -1), down (-1, 0), down (0, 0), up (0, 0)],
    [up (-1, 0), down (-1, -1), up (0, -1), down (0, -1), down (0, 0), up (0, 0)],
    [up (0, 1), up (1, 0), down (-1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [up (0, -1), up (1, 0), down (-1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [up (-1, 0), up (1, 0), down (-1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [down (1, 0), up (1, 0), down (-1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [down (1, 0), up (0, -1), up (1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [down (0, -2), up (0, -1), up (1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [down (-1, -1), up (0, -1), up (1, 0), down (0, -1), down (0, 0), up (0, 0)],
    [down (0, 1), up (0, -1), up (0, 1), down (0, -1), down (0, 0), up (0, 0)]]

/-- The corner set of `hexiamond i`. -/
def hexiamondCorners (i : Fin 12) : Finset (ℤ × ℤ) :=
  cornerSet (hexiamond i).toFinset

theorem isGrowthList_fanPentiamond : IsGrowthList fanPentiamond := by
  decide +kernel

theorem isGrowthList_hexiamond : ∀ i, IsGrowthList (hexiamond i) := by
  decide +kernel

theorem card_fanPentiamond : fanPentiamond.toFinset.card = 5 := by
  decide +kernel

theorem card_hexiamond : ∀ i, (hexiamond i).toFinset.card = 6 := by
  decide +kernel

/-- Each `hexiamond i` is a hexiamond: a polyiamond with six cells. -/
theorem isPolyiamond_hexiamond (i : Fin 12) : IsPolyiamond (hexiamond i).toFinset :=
  (isGrowthList_hexiamond i).isPolyiamond

theorem isPolyiamond_fanPentiamond : IsPolyiamond fanPentiamond.toFinset :=
  isGrowthList_fanPentiamond.isPolyiamond

/-- Removing any one cell from the hexagon leaves a fan pentiamond. -/
theorem cellsCongr_erase_hexagon_fanPentiamond : ∀ c ∈ hexagonHexiamond,
    CellsCongr (hexagonHexiamond.toFinset.erase c) fanPentiamond.toFinset := by
  decide +kernel

/-- `hexiamond 1`: the hexagon without the cell opposite `up (0, 0)`, plus the outer cell
`down (0, 0)`. -/
theorem hexiamond_one : (hexiamond 1).toFinset =
    insert (down (0, 0)) (hexagonHexiamond.toFinset.erase (down (-1, -1))) := by
  decide +kernel

/-- `hexiamond 2`: the hexagon without a cell two steps from `up (0, 0)`, plus the outer cell
`down (0, 0)`. -/
theorem hexiamond_two : (hexiamond 2).toFinset =
    insert (down (0, 0)) (hexagonHexiamond.toFinset.erase (up (-1, 0))) := by
  decide +kernel

/-- `hexiamond 3`: the hexagon without a neighbour of `up (0, 0)`, plus the outer cell
`down (0, 0)`. -/
theorem hexiamond_three : (hexiamond 3).toFinset =
    insert (down (0, 0)) (hexagonHexiamond.toFinset.erase (down (-1, 0))) := by
  decide +kernel

/-! #### The twelve hexiamonds are pairwise non-congruent -/

/-- `pairNormSum id` of the (tripled) centroids of the cells of `hexiamond i`. -/
private def centroidInv : Fin 12 → ℤ :=
  ![216, 270, 282, 306, 270, 306, 324, 354, 414, 414, 378, 486]

private theorem pairNormSum_centroid_hexiamond :
    ∀ i, pairNormSum id ((hexiamond i).toFinset.image centroid3) = centroidInv i := by
  decide +kernel

/-- The invariant separates all pairs except `1, 4`, `3, 5` and `8, 9`; for those the kernel
checks the twelve symmetries directly. (The pairs `1, 4` and `3, 5` even have the same sums of
squared distances between centroids.) -/
private theorem eq_or_not_cellsCongr_of_centroidInv_eq :
    ∀ i j, centroidInv i = centroidInv j →
      i = j ∨ ¬ CellsCongr (hexiamond i).toFinset (hexiamond j).toFinset := by
  decide +kernel

/-- **The twelve hexiamonds are pairwise distinct**: no symmetry of the lattice carries one onto
another. -/
theorem cellsCongr_hexiamond_iff (i j : Fin 12) :
    CellsCongr (hexiamond i).toFinset (hexiamond j).toFinset ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ CellsCongr.refl _⟩
  have hs := h.pairNormSum_eq id
  rw [pairNormSum_centroid_hexiamond, pairNormSum_centroid_hexiamond] at hs
  exact (eq_or_not_cellsCongr_of_centroidInv_eq i j hs).resolve_right (not_not.mpr h)

/-! #### Corner sets -/

/-- **The fan pentiamond and the hexagon have the same corners**: the missing cell of the fan
adds no corner. -/
theorem cornerSet_fanPentiamond :
    cornerSet fanPentiamond.toFinset = cornerSet hexagonHexiamond.toFinset := by
  decide +kernel

/-- The hexagon has `7` corners. -/
theorem card_cornerSet_hexagonHexiamond : (cornerSet hexagonHexiamond.toFinset).card = 7 := by
  decide +kernel

/-- The hexagon is `hexiamond 0`. -/
theorem hexiamondCorners_zero : hexiamondCorners 0 = cornerSet hexagonHexiamond.toFinset :=
  rfl

/-- The corners of `hexiamond 1` are the seven corners of the hexagon and the far corner `(1, 1)`
of the outer cell `down (0, 0)`. -/
theorem hexiamondCorners_one :
    hexiamondCorners 1 = insert (1, 1) (cornerSet hexagonHexiamond.toFinset) := by
  decide +kernel

/-- **Three hexiamonds share one corner set**, part 1. -/
theorem hexiamondCorners_two : hexiamondCorners 2 = hexiamondCorners 1 := by
  decide +kernel

/-- **Three hexiamonds share one corner set**, part 2. -/
theorem hexiamondCorners_three : hexiamondCorners 3 = hexiamondCorners 1 := by
  decide +kernel

/-- The hexagon has `7` corners, every other hexiamond has `8`. -/
theorem card_hexiamondCorners : ∀ i, (hexiamondCorners i).card = if i = 0 then 7 else 8 := by
  decide +kernel

/-- `pairNormSum id` of the corner set of `hexiamond i`. -/
private def cornerInv : Fin 12 → ℤ :=
  ![84, 138, 138, 138, 144, 150, 154, 162, 174, 168, 160, 192]

private theorem pairNormSum_hexiamondCorners :
    ∀ i, pairNormSum id (hexiamondCorners i) = cornerInv i := by
  decide +kernel

private theorem cornerInv_eq_iff : ∀ i j, cornerInv i = cornerInv j ↔
    i = j ∨ (i ∈ ({1, 2, 3} : Finset (Fin 12)) ∧ j ∈ ({1, 2, 3} : Finset (Fin 12))) := by
  decide

private theorem hexiamondCorners_eq_of_mem {i j : Fin 12} (hi : i ∈ ({1, 2, 3} : Finset (Fin 12)))
    (hj : j ∈ ({1, 2, 3} : Finset (Fin 12))) : hexiamondCorners i = hexiamondCorners j := by
  have h : ∀ k ∈ ({1, 2, 3} : Finset (Fin 12)), hexiamondCorners k = hexiamondCorners 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      hexiamondCorners_two, hexiamondCorners_three, and_self]
  rw [h i hi, h j hj]

/-- **Which hexiamonds give isomorphic arrangements.** The circles at the corners of `hexiamond i`
and of `hexiamond j` form isomorphic arrangements exactly when `i = j` or both are among the
three fans-plus-one-cell `1, 2, 3`. -/
theorem iso_ofSites_hexiamondCorners_iff (i j : Fin 12) :
    (Arrangement.ofSites (hexiamondCorners i)).Iso (Arrangement.ofSites (hexiamondCorners j)) ↔
      i = j ∨ (i ∈ ({1, 2, 3} : Finset (Fin 12)) ∧ j ∈ ({1, 2, 3} : Finset (Fin 12))) := by
  constructor
  · intro h
    have hs := h.pairNormSum_eq id
    rwa [pairNormSum_hexiamondCorners, pairNormSum_hexiamondCorners, cornerInv_eq_iff] at hs
  · rintro (rfl | ⟨hi, hj⟩)
    · exact Arrangement.Iso.refl _
    · rw [hexiamondCorners_eq_of_mem hi hj]
      exact Arrangement.Iso.refl _

/-- **Which hexiamonds have congruent corner sets.** The same answer as for isomorphism, now for
congruence under symmetries of the lattice. -/
theorem sitesCongr_hexiamondCorners_iff (i j : Fin 12) :
    SitesCongr (hexiamondCorners i) (hexiamondCorners j) ↔
      i = j ∨ (i ∈ ({1, 2, 3} : Finset (Fin 12)) ∧ j ∈ ({1, 2, 3} : Finset (Fin 12))) := by
  refine ⟨fun h => (iso_ofSites_hexiamondCorners_iff i j).mp h.iso, ?_⟩
  rintro (rfl | ⟨hi, hj⟩)
  · exact SitesCongr.refl _
  · rw [hexiamondCorners_eq_of_mem hi hj]
    exact SitesCongr.refl _

/-- **Twelve hexiamonds, ten corner sets.** The corner sets of the twelve hexiamonds form a
family of exactly `10` sets, no two of which give isomorphic arrangements (so, by
`SitesCongr.iso`, no two are congruent under a symmetry of the lattice either). One of them, the
hexagon's, has `7` points; the other `9` have `8`. -/
theorem hexiamondCorners_classes :
    (Finset.univ.image hexiamondCorners).card = 10 ∧
      ((Finset.univ.image hexiamondCorners).filter fun S => S.card = 7).card = 1 ∧
      ((Finset.univ.image hexiamondCorners).filter fun S => S.card = 8).card = 9 ∧
      ∀ S ∈ Finset.univ.image hexiamondCorners, ∀ T ∈ Finset.univ.image hexiamondCorners,
        (Arrangement.ofSites S).Iso (Arrangement.ofSites T) → S = T := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
  rcases (iso_ofSites_hexiamondCorners_iff i j).mp h with rfl | ⟨hi, hj⟩
  · rfl
  · exact hexiamondCorners_eq_of_mem hi hj

/-- The corner set of every hexiamond is a rigid arrangement. -/
theorem isRigid_ofSites_hexiamondCorners (i : Fin 12) :
    (Arrangement.ofSites (hexiamondCorners i)).IsRigid :=
  (isPolyiamond_hexiamond i).isRigid

/-- One hexiamond from each class of `iso_ofSites_hexiamondCorners_iff` with `8` corners: all
but the hexagon `0` and the duplicates `2, 3` of `1`. -/
private def eightIdx : Fin 9 → Fin 12 :=
  ![1, 4, 5, 6, 7, 8, 9, 10, 11]

private theorem card_hexiamondCorners_eightIdx :
    ∀ i, (hexiamondCorners (eightIdx i)).card = 8 := by
  decide +kernel

private theorem eightIdx_injective : ∀ i j, (eightIdx i = eightIdx j ∨
    (eightIdx i ∈ ({1, 2, 3} : Finset (Fin 12)) ∧ eightIdx j ∈ ({1, 2, 3} : Finset (Fin 12)))) →
      i = j := by
  decide

/-- **At least nine rigid arrangements of eight circles come from hexiamonds.** The corner sets
of the hexiamonds give nine pairwise non-isomorphic rigid arrangements of `8` circles. The
exploratory census found exactly nine rigid arrangements of eight circles, so these are probably
all of them; that upper bound is not proved here. -/
theorem exists_injective_rigidClasses_eight :
    ∃ f : Fin 9 → RigidClasses 8, Function.Injective f := by
  refine ⟨fun i => Quotient.mk _ ⟨Arrangement.ofSitesFin _ (card_hexiamondCorners_eightIdx i),
    (isRigid_ofSites_hexiamondCorners _).ofSitesFin _⟩, fun i j hij => ?_⟩
  have hiso := Arrangement.Iso.trans (Arrangement.Iso.symm (Arrangement.iso_ofSitesFin _ _))
    (Arrangement.Iso.trans (Quotient.exact hij) (Arrangement.iso_ofSitesFin _ _))
  exact eightIdx_injective i j ((iso_ofSites_hexiamondCorners_iff _ _).mp hiso)

end Hexiamonds

/-! ### The square grid -/

namespace Arrangement

variable {ι : Type*}

/-- Integers with `x² + y² = 1` and `y > 0`: `x = 0`, `y = 1`. -/
private theorem eq_zero_and_eq_one_of_sq_add_sq {x y : ℤ} (h : x ^ 2 + y ^ 2 = 1) (hy : 0 < y) :
    x = 0 ∧ y = 1 := by
  have hx : x ^ 2 = 0 := by nlinarith
  have hx0 : x = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  subst hx0
  exact ⟨rfl, by nlinarith⟩

/-- **No rigid arrangement on the square grid.** If the centers of at least three circles all lie
on the square grid of spacing `2` (the points `2a + 2bi` with `a, b` integers), the arrangement is
not rigid.

Two touching circles on the grid differ by `±2` or `±2i`. Pick two circles that differ in some
coordinate, say `b`, and let `S` be the circles whose `b`-coordinate is larger than the smaller of
the two. Every contact between `S` and the rest is then the same vertical vector `2i`, so the
shear flex (`not_isRigid_of_shear_of_three_le`) moves `S`. This includes the case of circles all
on one horizontal line, where `S` is the set of circles to the right of a point and the contacts
are horizontal. With only two circles the statement fails: two touching circles are rigid
(`isRigid_pair`). -/
theorem not_isRigid_of_squareGrid [Finite ι] (A : Arrangement ι) (hn : 3 ≤ Nat.card ι)
    (h : ∀ i, ∃ a b : ℤ, A.center i = 2 * (a : ℂ) + 2 * (b : ℂ) * Complex.I) :
    ¬ A.IsRigid := by
  choose a b hab using h
  -- touching circles on the grid differ by a unit vector of `ℤ²`
  have htan : ∀ i j, A.contactGraph.Adj i j → (a i - a j) ^ 2 + (b i - b j) ^ 2 = 1 := by
    intro i j hij
    have h2 : dist (A.center i) (A.center j) ^ 2 =
        4 * (((a i - a j) ^ 2 + (b i - b j) ^ 2 : ℤ) : ℝ) := by
      rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, hab i, hab j]
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.sub_im, Complex.add_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
        Complex.re_ofNat, Complex.im_ofNat]
      push_cast
      ring
    have hd : dist (A.center i) (A.center j) = 2 := hij.2
    rw [hd] at h2
    exact_mod_cast (by linarith : (((a i - a j) ^ 2 + (b i - b j) ^ 2 : ℤ) : ℝ) = 1)
  have : Nontrivial ι := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  have hne : a i ≠ a j ∨ b i ≠ b j := by
    by_contra hcon
    push Not at hcon
    exact hij (A.center_injective (by rw [hab, hab, hcon.1, hcon.2]))
  rcases hne with ha | hb
  · -- `S`: the circles to the right of circle `p`; all contacts leaving `S` are `2`
    obtain ⟨p, q, hpq⟩ : ∃ p q, a p < a q := by
      rcases lt_or_gt_of_ne ha with h | h
      · exact ⟨i, j, h⟩
      · exact ⟨j, i, h⟩
    refine A.not_isRigid_of_shear_of_three_le hn {k | a p < a k} 2 (fun k l hk hl hkl => ?_)
      (i := q) (k := p) hpq (lt_irrefl (a p))
    have hk : a p < a k := hk
    have hl : a l ≤ a p := not_lt.mp hl
    obtain ⟨h1, h2⟩ := eq_zero_and_eq_one_of_sq_add_sq (by linarith [htan k l hkl] :
      (b k - b l) ^ 2 + (a k - a l) ^ 2 = 1) (by omega)
    rw [hab k, hab l]
    have e1 : (b k : ℂ) = b l := by exact_mod_cast (sub_eq_zero.mp h1)
    have e2 : (a k : ℂ) = a l + 1 := by exact_mod_cast (by omega : a k = a l + 1)
    rw [e1, e2]
    ring
  · -- `S`: the circles above circle `p`; all contacts leaving `S` are `2i`
    obtain ⟨p, q, hpq⟩ : ∃ p q, b p < b q := by
      rcases lt_or_gt_of_ne hb with h | h
      · exact ⟨i, j, h⟩
      · exact ⟨j, i, h⟩
    refine A.not_isRigid_of_shear_of_three_le hn {k | b p < b k} (2 * Complex.I)
      (fun k l hk hl hkl => ?_) (i := q) (k := p) hpq (lt_irrefl (b p))
    have hk : b p < b k := hk
    have hl : b l ≤ b p := not_lt.mp hl
    obtain ⟨h1, h2⟩ := eq_zero_and_eq_one_of_sq_add_sq (htan k l hkl) (by omega)
    rw [hab k, hab l]
    have e1 : (a k : ℂ) = a l := by exact_mod_cast (sub_eq_zero.mp h1)
    have e2 : (b k : ℂ) = b l + 1 := by exact_mod_cast (by omega : b k = b l + 1)
    rw [e1, e2]
    ring

/-- `A` lies on a *square grid* of spacing `2`: some isometry of the plane carries every center
to a point `2a + 2bi` with `a, b` integers. -/
def IsSquareGrid (A : Arrangement ι) : Prop :=
  ∃ g : Plane ≃ᵃⁱ[ℝ] Plane,
    ∀ i, ∃ a b : ℤ, g (A.center i) = 2 * (a : ℂ) + 2 * (b : ℂ) * Complex.I

/-- **No rigid arrangement on any square grid** of spacing `2`, with at least three circles:
rigidity does not depend on the position of the grid (`isLocallyRigid_comp_isometryEquiv_iff`).
-/
theorem IsSquareGrid.not_isRigid [Finite ι] {A : Arrangement ι} (hA : A.IsSquareGrid)
    (hn : 3 ≤ Nat.card ι) : ¬ A.IsRigid := by
  obtain ⟨g, hg⟩ := hA
  let B : Arrangement ι :=
    ⟨fun i => g (A.center i), fun i j hij => by simpa only [g.dist_map] using A.nonoverlap hij⟩
  intro hAr
  have hB : B.IsRigid := (isLocallyRigid_comp_isometryEquiv_iff g.toIsometryEquiv).mpr hAr
  exact B.not_isRigid_of_squareGrid hn hg hB

end Arrangement

end RigidArrangements
