import Mathlib

/-!
# Arrangements of unit circles

A unit circle in the plane is determined by its center. Two unit circles are
*(externally) tangent* exactly when their centers are at distance `2`, and they
*overlap* when their centers are closer than `2`.

We model the plane as `ℂ` (distance `‖z - w‖`), so rotations are multiplications by unit
complex numbers. Circles are indexed by an arbitrary type `ι`, usually `Fin n`.

## Frameworks

The rigidity notions only depend on distances, so we state them for a placement
`p : ι → P` in any (pseudo)metric space `P`:

* `Tangent p i j`: the circles at `p i` and `p j` touch.
* `KeepsContacts p q`: the placement `q` keeps every tangency of `p` (new ones may appear).
* `IsLocallyRigid p`: every placement close enough to `p` that keeps every tangency of `p`
  has the same pairwise distances as `p` (Mathlib's `Congruent`). This is local rigidity
  of the bar framework (contact graph, all bars of length `2`) in the sense of
  Asimow–Roth.

`isLocallyRigid_iff_eps` restates `IsLocallyRigid` with an explicit `ε`.

## Arrangements

An `Arrangement ι` is a placement of non-overlapping unit circles in `Plane = ℂ`. Its
*contact graph* has an edge between each tangent pair.
-/

open Filter Topology

namespace RigidArrangements

section Framework

variable {ι κ P Q : Type*} [PseudoMetricSpace P] [PseudoMetricSpace Q]

/-- The unit circles centered at `p i` and `p j` touch: their centers are `2` apart. -/
def Tangent (p : ι → P) (i j : ι) : Prop :=
  dist (p i) (p j) = 2

theorem tangent_comm {p : ι → P} {i j : ι} : Tangent p i j ↔ Tangent p j i := by
  simp only [Tangent, dist_comm]

/-- The placement `q` keeps every tangency of `p`. New tangencies may appear. -/
def KeepsContacts (p q : ι → P) : Prop :=
  ∀ i j, Tangent p i j → Tangent q i j

/-- **Local rigidity** (Asimow–Roth). Every placement `q` close enough to `p` that keeps all
tangencies of `p` has exactly the same pairwise distances as `p`, i.e. `q` is congruent to
`p`. Equivalently (Asimow–Roth), no continuous motion that keeps the tangencies changes the
shape: there is no "wiggle room". -/
def IsLocallyRigid (p : ι → P) : Prop :=
  ∀ᶠ q in 𝓝 p, KeepsContacts p q → Congruent q p

/-- `IsLocallyRigid` with an explicit `ε`: every placement that moves each center by less
than `ε` and keeps every tangency has all pairwise distances unchanged. -/
theorem isLocallyRigid_iff_eps [Finite ι] {p : ι → P} :
    IsLocallyRigid p ↔ ∃ ε > 0, ∀ q : ι → P, (∀ i, dist (q i) (p i) < ε) →
      KeepsContacts p q → ∀ i j, dist (q i) (q j) = dist (p i) (p j) := by
  have := Fintype.ofFinite ι
  simp only [IsLocallyRigid, congruent_iff_dist_eq, Metric.eventually_nhds_iff]
  constructor
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, fun q hq hk => h ((dist_pi_lt_iff hε).2 hq) hk⟩
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, fun q hq hk => h q (fun i => (dist_le_pi_dist q p i).trans_lt hq) hk⟩

/-- Rigidity only sees distances, so it transfers along isometries of the ambient space. -/
theorem IsLocallyRigid.comp_isometryEquiv {p : ι → P} (h : IsLocallyRigid p) (e : P ≃ᵢ Q) :
    IsLocallyRigid (e ∘ p) := by
  have hc : Continuous fun q : ι → Q => (e.symm ∘ q : ι → P) :=
    continuous_pi fun i => e.symm.continuous.comp (continuous_apply i)
  have h' : ∀ᶠ q in 𝓝 (e ∘ p), KeepsContacts p (e.symm ∘ q) → Congruent (e.symm ∘ q) p := by
    have := hc.continuousAt (x := e ∘ p) |>.eventually (p := fun r => KeepsContacts p r →
      Congruent r p)
    simp only [Function.comp_def, IsometryEquiv.symm_apply_apply] at this
    exact this h
  filter_upwards [h'] with q hq hk
  have hk' : KeepsContacts p (e.symm ∘ q) := fun i j hij => by
    have := hk i j (by simpa [Tangent, IsometryEquiv.dist_eq] using hij)
    simpa [Tangent, IsometryEquiv.dist_eq] using this
  have := hq hk'
  rw [congruent_iff_dist_eq] at this ⊢
  intro i j
  simpa [IsometryEquiv.dist_eq] using this i j

theorem isLocallyRigid_comp_isometryEquiv_iff {p : ι → P} (e : P ≃ᵢ Q) :
    IsLocallyRigid (e ∘ p) ↔ IsLocallyRigid p :=
  ⟨fun h => by simpa [Function.comp_def] using h.comp_isometryEquiv e.symm,
    fun h => h.comp_isometryEquiv e⟩

/-- If every pair of distinct points is tangent, nothing can move without breaking a
tangency, so the placement is locally rigid. -/
theorem isLocallyRigid_of_forall_tangent {p : ι → P}
    (h : ∀ i j, i ≠ j → Tangent p i j) : IsLocallyRigid p := by
  refine Eventually.of_forall fun q hq => ?_
  rw [congruent_iff_dist_eq]
  intro i j
  by_cases hij : i = j
  · subst hij; simp
  · exact (hq i j (h i j hij)).trans (h i j hij).symm

end Framework

/-- The Euclidean plane, modelled as `ℂ`. -/
abbrev Plane := ℂ

/-- An arrangement of unit circles indexed by `ι`, recorded by their centers, such that no
two distinct circles overlap. -/
structure Arrangement (ι : Type*) where
  /-- The center of circle `i`. -/
  center : ι → Plane
  /-- Distinct circles have centers at distance at least `2`. -/
  nonoverlap : Pairwise fun i j => 2 ≤ dist (center i) (center j)

namespace Arrangement

variable {ι : Type*} (A : Arrangement ι)

/-- The contact graph of `A`: circles are adjacent when they are tangent. -/
def contactGraph : SimpleGraph ι where
  Adj i j := i ≠ j ∧ Tangent A.center i j
  symm := ⟨fun _ _ ⟨hne, ht⟩ => ⟨hne.symm, tangent_comm.mp ht⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- No two circles of an arrangement share a center. -/
theorem center_injective : Function.Injective A.center := by
  intro i j h
  by_contra hij
  have : 2 ≤ dist (A.center i) (A.center j) := A.nonoverlap hij
  rw [h, dist_self] at this
  norm_num at this

end Arrangement

end RigidArrangements
