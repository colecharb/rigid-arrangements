import RigidArrangements.Rigidity

/-!
# The triangular lattice

Unit circles packed as tightly as possible (like pennies on a table) have their centers on
the *triangular lattice* of spacing `2`. We parametrize it by `ℤ × ℤ`:
`latticePoint (a, b) = a • 2 + b • (1 + i√3)`.

The squared distance between two lattice points is `4` times the *Eisenstein norm*
`eNorm (a, b) = a² + ab + b²` of their difference (`dist_latticePoint_sq`). So two circles
at lattice points touch exactly when `eNorm` of the difference is `1`, and any two distinct
lattice points are at least `2` apart. This turns questions about lattice arrangements into
integer arithmetic that `decide` can check.

## Main definitions

* `eNorm`, `latticePoint`.
* `Arrangement.ofLattice`: the arrangement with one circle at each point of a list of
  distinct lattice points.
* `Arrangement.IsLattice`: an arrangement is *on the lattice* if some isometry of the plane
  carries all its centers to lattice points.
-/

namespace RigidArrangements

/-- The Eisenstein norm `a² + ab + b²`. The squared distance between lattice points
`v` and `w` is `4 * eNorm (v - w)`. -/
def eNorm (v : ℤ × ℤ) : ℤ :=
  v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2

/-- The triangular lattice of spacing `2`: `(a, b) ↦ 2a + b(1 + i√3)`. -/
noncomputable def latticePoint (v : ℤ × ℤ) : Plane :=
  ⟨2 * v.1 + v.2, Real.sqrt 3 * v.2⟩

theorem dist_latticePoint_sq (v w : ℤ × ℤ) :
    dist (latticePoint v) (latticePoint w) ^ 2 = 4 * (eNorm (v - w) : ℝ) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [latticePoint, latticePoint, Complex.dist_mk, Real.sq_sqrt (by positivity)]
  simp only [eNorm, Prod.fst_sub, Prod.snd_sub]
  push_cast
  linear_combination ((v.2 : ℝ) - w.2) ^ 2 * h3

theorem eNorm_nonneg (v : ℤ × ℤ) : 0 ≤ eNorm v := by
  unfold eNorm; nlinarith [sq_nonneg (v.1 + v.2), sq_nonneg v.1, sq_nonneg v.2]

theorem eNorm_eq_zero_iff (v : ℤ × ℤ) : eNorm v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, eNorm]⟩
  unfold eNorm at h
  have h1 : v.1 = 0 := by nlinarith [sq_nonneg (v.1 + 2 * v.2), sq_nonneg v.1]
  have h2 : v.2 = 0 := by rw [h1] at h; nlinarith
  exact Prod.ext h1 h2

/-- Circles at lattice points `v` and `w` touch iff `eNorm (v - w) = 1`. -/
theorem tangent_latticePoint_iff (v w : ℤ × ℤ) :
    dist (latticePoint v) (latticePoint w) = 2 ↔ eNorm (v - w) = 1 := by
  have hsq := dist_latticePoint_sq v w
  have h0 := dist_nonneg (x := latticePoint v) (y := latticePoint w)
  constructor
  · intro h; rw [h] at hsq; exact_mod_cast (by linarith : (eNorm (v - w) : ℝ) = 1)
  · intro h; rw [h, Int.cast_one, mul_one] at hsq; nlinarith

/-- Distinct lattice points are at least `2` apart, so circles there never overlap. -/
theorem two_le_dist_latticePoint {v w : ℤ × ℤ} (h : v ≠ w) :
    2 ≤ dist (latticePoint v) (latticePoint w) := by
  have hsq := dist_latticePoint_sq v w
  have h0 := dist_nonneg (x := latticePoint v) (y := latticePoint w)
  have hpos : 1 ≤ eNorm (v - w) := by
    rcases (eNorm_nonneg (v - w)).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (sub_eq_zero.mp ((eNorm_eq_zero_iff _).mp heq.symm)) h
  have : (1 : ℝ) ≤ eNorm (v - w) := by exact_mod_cast hpos
  nlinarith

theorem latticePoint_injective : Function.Injective latticePoint := by
  intro v w h
  by_contra hne
  have := two_le_dist_latticePoint hne
  rw [h, dist_self] at this
  norm_num at this

namespace Arrangement

/-- The arrangement with one circle at each lattice point of the list `l` (whose entries
must be distinct). Circle `i` sits at `latticePoint (l.get i)`. -/
noncomputable def ofLattice (l : List (ℤ × ℤ)) (hl : l.Nodup) : Arrangement (Fin l.length) where
  center i := latticePoint (l.get i)
  nonoverlap _ _ hij := two_le_dist_latticePoint fun h => hij (hl.get_inj_iff.mp h)

theorem tangent_ofLattice_iff {l : List (ℤ × ℤ)} (hl : l.Nodup) (i j : Fin l.length) :
    Tangent (ofLattice l hl).center i j ↔ eNorm (l.get i - l.get j) = 1 :=
  tangent_latticePoint_iff _ _

/-- `A` lies on the triangular lattice: some isometry of the plane carries every center of
`A` to a lattice point. -/
def IsLattice {ι : Type*} (A : Arrangement ι) : Prop :=
  ∃ (g : Plane ≃ᵃⁱ[ℝ] Plane) (f : ι → ℤ × ℤ), ∀ i, g (A.center i) = latticePoint (f i)

end Arrangement

end RigidArrangements
