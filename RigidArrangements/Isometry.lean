import RigidArrangements.Rigidity

/-!
# Congruence comes from an isometry; rigidity is an isomorphism invariant

Two arrangements are *isomorphic* (`Arrangement.Iso`) when, after relabeling the circles,
all pairwise distances between centers agree (Mathlib's `Congruent`). This file shows that
this is the right notion, in three ways.

* **Congruence is an ambient isometry.** If two finite families of points in the plane
  (more generally, in a finite-dimensional real inner product space) have the same pairwise
  distances, then an isometry of the whole plane (a rotation or a reflection, followed by
  a translation) carries one onto the other. This is the classical fact that a
  distance-preserving map on finitely many points extends to the whole space; we did not
  find it in Mathlib. The proof: fix a base point, so that distances determine all inner products of
  the difference vectors; the linear map sending one family of difference vectors to the
  other is then well defined and preserves lengths on their span, and Mathlib's
  `LinearIsometry.extend` extends it to an isometry of the whole space.
* **Isomorphism is relabeling plus isometry.** Hence `A.Iso B` holds exactly when some
  relabeling followed by some isometry of the plane carries `A` onto `B`. The direction
  "isometry ⇒ isomorphism" holds for any index type; the other uses finiteness.
* **Isomorphism preserves what we count.** Rigidity is unchanged by isomorphism: rigidity
  only depends on distances, so it is unchanged by an isometry of the plane, and it is
  clearly unchanged by relabeling. The contact graph is also preserved: the relabeling is
  an isomorphism of contact graphs. Consequently "rigid" is a property of an isomorphism
  class, and `RigidClasses n` is in bijection with the rigid classes among *all*
  isomorphism classes of arrangements of `n` circles. In other words, counting
  `RigidClasses n` means what it should.

## Main results

* `exists_affineIsometryEquiv_of_congruent`: congruent finite families in a
  finite-dimensional real inner product space (e.g. `Plane`) differ by an affine isometry.
* `isLocallyRigid_comp_equiv_iff`: local rigidity is unchanged by relabeling.
* `isLocallyRigid_iff_of_congruent`: congruent finite placements in a finite-dimensional real
  inner product space (e.g. `Plane`) are both rigid or both not.
* `Arrangement.Iso.of_isometry`: a relabeling plus an isometry of the plane gives an
  isomorphism (no finiteness needed).
* `Arrangement.iso_iff_exists_isometry`: isomorphism is relabeling plus an affine isometry.
* `Arrangement.Iso.isRigid_iff`: **rigidity is invariant under isomorphism**.
* `Arrangement.contactGraphIso`, `Arrangement.Iso.nonempty_contactGraph_iso`: isomorphic
  arrangements have isomorphic contact graphs, via the relabeling.
* `rigidClassesEquiv`: `RigidClasses n` is equivalent to the set of isomorphism classes of
  arrangements of `n` circles that are rigid (`ArrClasses.IsRigid`).
-/

open Filter Topology
open scoped RealInnerProductSpace

namespace RigidArrangements

/-! ### Congruent families differ by an ambient isometry -/

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pairwise distances determine the inner products of the difference vectors `v i - v i₀`
(polarization). -/
theorem inner_sub_eq_of_congruent {ι : Type*} {v w : ι → V} (h : Congruent v w)
    (i₀ i j : ι) : ⟪v i - v i₀, v j - v i₀⟫ = ⟪w i - w i₀, w j - w i₀⟫ := by
  have key : ∀ a b : V, ⟪a, b⟫ = (‖a‖ ^ 2 + ‖b‖ ^ 2 - ‖a - b‖ ^ 2) / 2 := by
    intro a b; rw [norm_sub_sq_real]; ring
  rw [key, key]
  simp only [← dist_eq_norm, sub_sub_sub_cancel_right, h.dist_eq]

/-- Pairwise distances determine the length of every linear combination of the difference
vectors `v i - v i₀`. -/
theorem norm_sum_smul_sub_eq_of_congruent {ι : Type*} [Fintype ι] {v w : ι → V}
    (h : Congruent v w) (i₀ : ι) (c : ι → ℝ) :
    ‖∑ i, c i • (v i - v i₀)‖ = ‖∑ i, c i • (w i - w i₀)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    inner_sub_eq_of_congruent h]

/-- **Congruent finite families differ by an ambient isometry.** If two finite families of
points in a finite-dimensional real inner product space have the same pairwise distances,
some affine isometric equivalence of the space carries one onto the other. For `V = Plane`
this says that two congruent placements of finitely many centers differ by a rotation or
reflection followed by a translation. -/
theorem exists_affineIsometryEquiv_of_congruent [FiniteDimensional ℝ V] {ι : Type*} [Finite ι]
    {v w : ι → V} (h : Congruent v w) : ∃ g : V ≃ᵃⁱ[ℝ] V, ∀ i, g (v i) = w i := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨AffineIsometryEquiv.refl ℝ V, fun i => hι.elim i⟩
  -- The linear maps `c ↦ ∑ c i • (v i - v i₀)` and `c ↦ ∑ c i • (w i - w i₀)`.
  let X := Fintype.linearCombination ℝ (fun i => v i - v i₀)
  let Y := Fintype.linearCombination ℝ (fun i => w i - w i₀)
  have hXY : ∀ c, ‖X c‖ = ‖Y c‖ := fun c => norm_sum_smul_sub_eq_of_congruent h i₀ c
  have hker : LinearMap.ker X ≤ LinearMap.ker Y := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, ← hXY, hc, norm_zero]
  -- The well-defined map `X c ↦ Y c` on the range of `X`; it preserves lengths.
  let L₀ : LinearMap.range X →ₗ[ℝ] V :=
    ((LinearMap.ker X).liftQ Y hker).comp X.quotKerEquivRange.symm.toLinearMap
  have hL₀ : ∀ c, L₀ ⟨X c, LinearMap.mem_range_self X c⟩ = Y c := by
    intro c
    simp only [L₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hnorm : ∀ z, ‖L₀ z‖ = ‖z‖ := by
    rintro ⟨z, c, rfl⟩
    rw [hL₀ c, ← Submodule.norm_coe]
    exact (hXY c).symm
  let L : LinearMap.range X →ₗᵢ[ℝ] V := { toLinearMap := L₀, norm_map' := hnorm }
  -- Extend it to a linear isometry of `V`, and conjugate by the translations.
  let E : V ≃ₗᵢ[ℝ] V := L.extend.toLinearIsometryEquiv rfl
  refine ⟨(AffineIsometryEquiv.vaddConst ℝ (v i₀)).symm.trans
    (E.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ (w i₀))), fun i => ?_⟩
  have hE : E (v i - v i₀) = w i - w i₀ := by
    have hx : X (Pi.single i 1) = v i - v i₀ := by simp [X]
    have hy : Y (Pi.single i 1) = w i - w i₀ := by simp [Y]
    have := L.extend_apply ⟨X (Pi.single i 1), LinearMap.mem_range_self X _⟩
    simp only [E, LinearIsometry.toLinearIsometryEquiv_apply]
    rw [← hx, ← hy, ← hL₀]
    exact this
  simp [hE]

end Euclidean

/-! ### Rigidity under relabeling and congruence -/

section Framework

variable {ι κ P Q : Type*} [PseudoMetricSpace P] [PseudoMetricSpace Q]

/-- Tangency only depends on distances, so congruent placements have the same tangencies. -/
theorem tangent_iff_of_congruent {p : ι → P} {q : ι → Q} (h : Congruent p q) (i j : ι) :
    Tangent p i j ↔ Tangent q i j := by
  rw [Tangent, Tangent, h.dist_eq]

/-- Relabeling the points of a locally rigid placement gives a locally rigid placement. -/
theorem IsLocallyRigid.comp_equiv {p : ι → P} (h : IsLocallyRigid p) (e : κ ≃ ι) :
    IsLocallyRigid (p ∘ e) := by
  have hc : Continuous fun q : κ → P => (q ∘ e.symm : ι → P) :=
    continuous_pi fun i => continuous_apply (e.symm i)
  have h' : ∀ᶠ q in 𝓝 (p ∘ e), KeepsContacts p (q ∘ e.symm) → Congruent (q ∘ e.symm) p := by
    have := hc.continuousAt (x := p ∘ e) |>.eventually (p := fun r => KeepsContacts p r →
      Congruent r p)
    simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at this
    exact this h
  filter_upwards [h'] with q hq hk
  have hk' : KeepsContacts p (q ∘ e.symm) := fun i j hij =>
    hk (e.symm i) (e.symm j) (by simpa [Tangent] using hij)
  have := hq hk'
  rw [← Congruent.index_equiv e] at this
  simpa [Function.comp_assoc] using this

/-- Local rigidity is unchanged by relabeling the points: `p ∘ e` is locally rigid exactly
when `p` is. -/
theorem isLocallyRigid_comp_equiv_iff {p : ι → P} (e : κ ≃ ι) :
    IsLocallyRigid (p ∘ e) ↔ IsLocallyRigid p :=
  ⟨fun h => by simpa [Function.comp_assoc] using h.comp_equiv e.symm, fun h => h.comp_equiv e⟩

/-- **Congruent finite placements are both rigid or both not**, in a finite-dimensional real
inner product space such as `Plane`: by `exists_affineIsometryEquiv_of_congruent` they differ
by an isometry of the space, and rigidity only depends on distances. -/
theorem isLocallyRigid_iff_of_congruent {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Finite ι] {p q : ι → V}
    (h : Congruent p q) : IsLocallyRigid p ↔ IsLocallyRigid q := by
  obtain ⟨g, hg⟩ := exists_affineIsometryEquiv_of_congruent h
  have hq : q = g.toIsometryEquiv ∘ p := funext fun i => (hg i).symm
  rw [hq, isLocallyRigid_comp_isometryEquiv_iff]

end Framework

/-! ### Isomorphism of arrangements -/

namespace Arrangement

variable {ι κ : Type*} {A : Arrangement ι} {B : Arrangement κ}

/-- A relabeling `e` followed by an isometry `g` of the plane that carries `A` onto `B` is an
isomorphism. No finiteness is needed in this direction. -/
theorem Iso.of_isometry {g : Plane → Plane} (hg : Isometry g) (e : ι ≃ κ)
    (h : ∀ i, B.center (e i) = g (A.center i)) : A.Iso B := by
  refine ⟨e, ?_⟩
  have hB : B.center ∘ e = g ∘ A.center := funext h
  rw [hB, Congruent.comp_right_iff hg]

/-- **Isomorphism is relabeling plus isometry.** Two arrangements of finitely many circles
are isomorphic exactly when a relabeling `e` followed by an isometry `g` of the plane
(rotation or reflection, then translation) carries one onto the other. -/
theorem iso_iff_exists_isometry [Finite ι] :
    A.Iso B ↔ ∃ (e : ι ≃ κ) (g : Plane ≃ᵃⁱ[ℝ] Plane), ∀ i, B.center (e i) = g (A.center i) := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨g, hg⟩ := exists_affineIsometryEquiv_of_congruent he
    exact ⟨e, g, fun i => (hg i).symm⟩
  · rintro ⟨e, g, hg⟩
    exact Iso.of_isometry g.isometry e hg

/-- **Rigidity is invariant under isomorphism.** So "rigid" is a property of an isomorphism
class, and counting `RigidClasses n` is meaningful. -/
theorem Iso.isRigid_iff [Finite ι] (h : A.Iso B) : A.IsRigid ↔ B.IsRigid := by
  obtain ⟨e, he⟩ := h
  exact (isLocallyRigid_iff_of_congruent he).trans (isLocallyRigid_comp_equiv_iff e)

/-- An arrangement isomorphic to a rigid one is rigid. -/
theorem Iso.isRigid [Finite ι] (h : A.Iso B) (hA : A.IsRigid) : B.IsRigid :=
  h.isRigid_iff.mp hA

/-- If a relabeling `e` makes all distances of `A` and `B` agree (the data of an `Iso`, not
an `Iso` hypothesis), then `e` maps tangent pairs of `A` exactly to tangent pairs of `B`. -/
theorem tangent_iff_of_iso {e : ι ≃ κ} (he : Congruent A.center (B.center ∘ e)) (i j : ι) :
    Tangent B.center (e i) (e j) ↔ Tangent A.center i j :=
  (tangent_iff_of_congruent he i j).symm

/-- A relabeling `e` that makes all distances of `A` and `B` agree is an isomorphism of
their contact graphs. -/
def contactGraphIso (e : ι ≃ κ) (he : Congruent A.center (B.center ∘ e)) :
    A.contactGraph ≃g B.contactGraph where
  toEquiv := e
  map_rel_iff' {i j} := by
    simp only [contactGraph, ne_eq, EmbeddingLike.apply_eq_iff_eq, tangent_iff_of_iso he]

/-- The contact graph isomorphism `contactGraphIso e he` acts on circles as `e`. -/
@[simp]
theorem coe_contactGraphIso (e : ι ≃ κ) (he : Congruent A.center (B.center ∘ e)) :
    ⇑(contactGraphIso e he) = e :=
  rfl

/-- **Isomorphic arrangements have isomorphic contact graphs.** -/
theorem Iso.nonempty_contactGraph_iso (h : A.Iso B) : Nonempty (A.contactGraph ≃g B.contactGraph) :=
  let ⟨e, he⟩ := h
  ⟨contactGraphIso e he⟩

/-- Isomorphism of arrangements indexed by `ι`, as a setoid. -/
def isoSetoid (ι : Type*) : Setoid (Arrangement ι) where
  r A B := A.Iso B
  iseqv := ⟨Iso.refl, Iso.symm, Iso.trans⟩

end Arrangement

/-! ### Rigidity is a property of isomorphism classes -/

/-- Arrangements of `n` circles, rigid or not, up to isomorphism. -/
def ArrClasses (n : ℕ) : Type :=
  Quotient (Arrangement.isoSetoid (Fin n))

/-- A class of arrangements is rigid when its members are. This is well defined by
`Arrangement.Iso.isRigid_iff`. -/
def ArrClasses.IsRigid {n : ℕ} : ArrClasses n → Prop :=
  Quotient.lift (fun A => A.IsRigid) fun _ _ h => propext h.isRigid_iff

/-- The class of `A` is rigid exactly when `A` is. -/
@[simp]
theorem ArrClasses.isRigid_mk {n : ℕ} (A : Arrangement (Fin n)) :
    ArrClasses.IsRigid (Quotient.mk (Arrangement.isoSetoid (Fin n)) A) ↔ A.IsRigid :=
  Iff.rfl

/-- The class of a rigid arrangement, among all classes. -/
def RigidClasses.toArrClasses {n : ℕ} : RigidClasses n → {c : ArrClasses n // c.IsRigid} :=
  Quotient.lift (fun A => ⟨Quotient.mk _ A.1, A.2⟩) fun _ _ h => Subtype.ext (Quotient.sound h)

/-- **Counting `RigidClasses n` is well defined.** The isomorphism classes of rigid
arrangements of `n` circles are exactly the rigid classes among all isomorphism classes of
arrangements of `n` circles. -/
noncomputable def rigidClassesEquiv (n : ℕ) : RigidClasses n ≃ {c : ArrClasses n // c.IsRigid} :=
  Equiv.ofBijective RigidClasses.toArrClasses <| by
    constructor
    · rintro ⟨A⟩ ⟨B⟩ h
      have h' : (Quotient.mk _ A.1 : ArrClasses n) = Quotient.mk _ B.1 := congrArg Subtype.val h
      have hiso : A.1.Iso B.1 := Quotient.exact h'
      exact Quotient.sound hiso
    · rintro ⟨⟨A⟩, hA⟩
      exact ⟨Quotient.mk _ ⟨A, hA⟩, rfl⟩

end RigidArrangements
