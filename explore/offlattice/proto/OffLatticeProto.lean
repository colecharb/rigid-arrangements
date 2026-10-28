import RigidArrangements

/-! ===================== Frame.lean ===================== -/

/-!
# Scratch prototype (not in the repo): lattice frames of contacts

The *frame invariant* of an ordered pair of centers `(z, w)` is `(w - z) ^ 6`. For a contact
(`|w - z| = 2`) it has modulus `64`; it does not change if the contact is reversed, and it is
unchanged by rotating the contact through a multiple of `60°`. So it records the direction of
the contact modulo `60°`, which is exactly "which rotated copy of the triangular lattice the
contact belongs to".

Main results (all proved below):

* `Arrangement.IsLattice.frameInv_eq`: on the lattice, all contacts have the same frame
  invariant.
* `Arrangement.not_isLattice_of_frameInv_ne`: two contacts with different frame invariants
  (i.e. directions that differ by a non-multiple of `60°`) rule out the lattice. This
  generalizes `Arrangement.o11_not_isLattice`.
* `Arrangement.isLattice_of_frameInv_eq`: a connected arrangement all of whose contacts have the
  same frame invariant lies on the lattice.
* `Arrangement.isLattice_iff_frameInv`: hence, for connected arrangements (in particular rigid
  ones), lying on the lattice is equivalent to all contacts being in one frame.
-/

open ComplexConjugate

namespace RigidArrangements

/-- `latticePoint` in terms of `ρ`. -/
theorem latticePoint_eq (v : ℤ × ℤ) : latticePoint v = 2 * ((v.1 : ℂ) + (v.2 : ℂ) * rho) := by
  apply Complex.ext <;> simp [latticePoint] <;> ring

/-- `latticePoint` is additive. -/
theorem latticePoint_sub (v w : ℤ × ℤ) : latticePoint (v - w) = latticePoint v - latticePoint w := by
  rw [latticePoint_eq, latticePoint_eq, latticePoint_eq]
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

theorem latticePoint_add (v w : ℤ × ℤ) : latticePoint (v + w) = latticePoint v + latticePoint w := by
  rw [latticePoint_eq, latticePoint_eq, latticePoint_eq]
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem latticePoint_zero : latticePoint 0 = 0 := by
  apply Complex.ext <;> simp [latticePoint]

/-- The lattice vectors of `eNorm` one are the six units. -/
theorem mem_latticeUnits_of_eNorm_eq_one {v : ℤ × ℤ} (h : eNorm v = 1) : v ∈ latticeUnits := by
  obtain ⟨a, b⟩ := v
  simp only [eNorm] at h
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a + 2 * b)]
  have ha2 : -1 ≤ a := by nlinarith [sq_nonneg (a + 2 * b)]
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg (2 * a + b)]
  have hb2 : -1 ≤ b := by nlinarith [sq_nonneg (2 * a + b)]
  revert h
  interval_cases a <;> interval_cases b <;> decide

/-- A unit lattice vector is `2 ρ^m` for some `m < 6`. -/
theorem latticePoint_unit {v : ℤ × ℤ} (h : eNorm v = 1) : ∃ m < 6, latticePoint v = 2 * rho ^ m := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  have hm := mem_latticeUnits_of_eNorm_eq_one h
  simp only [latticeUnits, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, by rw [latticePoint_eq]; simp⟩
  · exact ⟨1, by norm_num, by rw [latticePoint_eq]; simp⟩
  · exact ⟨2, by norm_num, by rw [latticePoint_eq, rho_sq]; push_cast; ring⟩
  · exact ⟨3, by norm_num, by rw [latticePoint_eq, rho_pow_three]; push_cast; ring⟩
  · exact ⟨4, by norm_num, by rw [latticePoint_eq, h4]; push_cast; ring⟩
  · exact ⟨5, by norm_num, by rw [latticePoint_eq, h5]; push_cast; ring⟩

/-- Conversely `2 ρ^m` is a unit lattice vector. -/
theorem exists_latticePoint_eq_two_mul_rho_pow (m : ℕ) :
    ∃ v : ℤ × ℤ, eNorm v = 1 ∧ latticePoint v = 2 * rho ^ m := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  rw [← rho_pow_mod_six]
  have : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 6)
  · exact ⟨(1, 0), by decide, by rw [latticePoint_eq]; simp⟩
  · exact ⟨(0, 1), by decide, by rw [latticePoint_eq]; simp⟩
  · exact ⟨(-1, 1), by decide, by rw [latticePoint_eq, rho_sq]; push_cast; ring⟩
  · exact ⟨(-1, 0), by decide, by rw [latticePoint_eq, rho_pow_three]; push_cast; ring⟩
  · exact ⟨(0, -1), by decide, by rw [latticePoint_eq, h4]; push_cast; ring⟩
  · exact ⟨(1, -1), by decide, by rw [latticePoint_eq, h5]; push_cast; ring⟩

/-- Unit lattice vectors have frame invariant `64`. -/
theorem latticePoint_unit_pow_six {v : ℤ × ℤ} (h : eNorm v = 1) : latticePoint v ^ 6 = 64 := by
  obtain ⟨m, -, hm⟩ := latticePoint_unit h
  rw [hm, mul_pow, ← pow_mul, mul_comm m 6, pow_mul, rho_pow_six, one_pow]
  norm_num

/-- `ρ` is a primitive sixth root of unity. -/
theorem rho_isPrimitiveRoot : IsPrimitiveRoot rho 6 := by
  have := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  have e : Complex.exp (2 * ↑Real.pi * Complex.I / ↑(6 : ℕ)) =
      Complex.exp (↑(Real.pi / 3) * Complex.I) := by
    congr 1; push_cast; ring
  rwa [e, exp_pi_div_three_mul_I] at this

namespace Arrangement

variable {ι : Type*}

/-- **On the lattice, all contacts are in one frame.** -/
theorem IsLattice.frameInv_eq {A : Arrangement ι} (h : A.IsLattice) {i j k l : ι}
    (hij : Tangent A.center i j) (hkl : Tangent A.center k l) :
    (A.center j - A.center i) ^ 6 = (A.center l - A.center k) ^ 6 := by
  obtain ⟨g, f, hf⟩ := h
  have hu : ∀ {i j}, Tangent A.center i j →
      g.linearIsometryEquiv (A.center j - A.center i) = latticePoint (f j - f i) ∧
        eNorm (f j - f i) = 1 := by
    intro i j hij
    refine ⟨?_, ?_⟩
    · have := g.map_vsub (A.center j) (A.center i)
      simp only [vsub_eq_sub] at this
      rw [this, hf, hf, latticePoint_sub]
    · have : dist (latticePoint (f j)) (latticePoint (f i)) = 2 := by
        rw [← hf, ← hf, g.dist_map]
        exact tangent_comm.mp hij
      exact (tangent_latticePoint_iff _ _).1 this
  obtain ⟨e1, n1⟩ := hu hij
  obtain ⟨e2, n2⟩ := hu hkl
  have p1 := latticePoint_unit_pow_six n1
  have p2 := latticePoint_unit_pow_six n2
  rw [← e1] at p1
  rw [← e2] at p2
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex g.linearIsometryEquiv
  · rw [ha, rotation_apply, mul_pow] at p1 p2
    have ha0 : (a : ℂ) ^ 6 ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero a)
    exact mul_left_cancel₀ ha0 (p1.trans p2.symm)
  · rw [ha, LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply,
      mul_pow, ← map_pow] at p1 p2
    have ha0 : (a : ℂ) ^ 6 ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero a)
    have := mul_left_cancel₀ ha0 (p1.trans p2.symm)
    exact (RingHom.injective (starRingEnd ℂ)) this

/-- **Two contacts in different frames rule out the lattice.** If the directions of two contacts
differ by an angle that is not a multiple of `60°`, the arrangement is on no triangular
lattice. -/
theorem not_isLattice_of_frameInv_ne {A : Arrangement ι} {i j k l : ι}
    (hij : Tangent A.center i j) (hkl : Tangent A.center k l)
    (hne : (A.center j - A.center i) ^ 6 ≠ (A.center l - A.center k) ^ 6) : ¬ A.IsLattice :=
  fun h => hne (h.frameInv_eq hij hkl)

/-- **Converse.** A connected arrangement in which every contact has the frame invariant of the
contact `a b` lies on the lattice. -/
theorem isLattice_of_frameInv_eq [Finite ι] {A : Arrangement ι}
    (hc : A.contactGraph.Preconnected) {a b : ι} (hab : Tangent A.center a b)
    (hφ : ∀ i j, A.contactGraph.Adj i j →
      (A.center j - A.center i) ^ 6 = (A.center b - A.center a) ^ 6) : A.IsLattice := by
  set α : ℂ := (A.center b - A.center a) / 2 with hα
  have hαn : ‖α‖ = 1 := by
    rw [hα, norm_div, ← dist_eq_norm, dist_comm, show dist (A.center a) (A.center b) = 2 from hab]
    norm_num
  have hα0 : α ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hαn; exact zero_ne_one hαn
  -- every contact vector is `α` times a unit lattice vector
  have hstep : ∀ i j, A.contactGraph.Adj i j →
      ∃ u : ℤ × ℤ, A.center j - A.center i = α * latticePoint u := by
    intro i j hij
    have h6 := hφ i j hij
    have hb : A.center b - A.center a = 2 * α := by rw [hα]; ring
    rw [hb] at h6
    have h2α : (2 * α) ^ 6 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hα0)
    have hq : ((A.center j - A.center i) / (2 * α)) ^ 6 = 1 := by
      rw [div_pow, h6, div_self h2α]
    obtain ⟨m, -, hm⟩ := rho_isPrimitiveRoot.eq_pow_of_pow_eq_one hq
    obtain ⟨u, -, hu⟩ := exists_latticePoint_eq_two_mul_rho_pow m
    refine ⟨u, ?_⟩
    rw [hu, hm]
    field_simp
  -- so every center is `p_a + α * latticePoint v`
  have hreach : ∀ k, ∃ v : ℤ × ℤ, A.center k = A.center a + α * latticePoint v := by
    intro k
    have key : ∀ (x y : ι) (w : A.contactGraph.Walk x y),
        (∃ v : ℤ × ℤ, A.center x = A.center a + α * latticePoint v) →
          ∃ v : ℤ × ℤ, A.center y = A.center a + α * latticePoint v := by
      intro x y w
      induction w with
      | nil => exact id
      | cons hadj _ ih =>
        rintro ⟨v, hv⟩
        apply ih
        obtain ⟨u, hu⟩ := hstep _ _ hadj
        refine ⟨v + u, ?_⟩
        rw [latticePoint_add]
        linear_combination hu + hv
    exact (hc a k).elim fun w => key a k w ⟨0, by rw [latticePoint_zero, mul_zero, add_zero]⟩
  choose f hf using hreach
  have hcong : Congruent A.center (latticePoint ∘ f) := by
    rw [congruent_iff_dist_eq]
    intro i j
    simp only [Function.comp_apply, dist_eq_norm]
    rw [hf i, hf j]
    rw [show A.center a + α * latticePoint (f i) - (A.center a + α * latticePoint (f j)) =
      α * (latticePoint (f i) - latticePoint (f j)) by ring, norm_mul, hαn, one_mul]
  obtain ⟨g, hg⟩ := exists_affineIsometryEquiv_of_congruent hcong
  exact ⟨g, f, hg⟩

/-- **Lattice criterion.** A connected arrangement with a contact `a b` lies on the triangular
lattice exactly when all its contacts have the frame invariant of `a b`. -/
theorem isLattice_iff_frameInv [Finite ι] {A : Arrangement ι}
    (hc : A.contactGraph.Preconnected) {a b : ι} (hab : Tangent A.center a b) :
    A.IsLattice ↔ ∀ i j, A.contactGraph.Adj i j →
      (A.center j - A.center i) ^ 6 = (A.center b - A.center a) ^ 6 :=
  ⟨fun h i j hij => h.frameInv_eq hij.2 hab, isLattice_of_frameInv_eq hc hab⟩

/-- **For rigid arrangements**: off the lattice exactly when two contacts are in different
frames. -/
theorem IsRigid.not_isLattice_iff [Finite ι] {A : Arrangement ι} (hA : A.IsRigid)
    {a b : ι} (hab : A.contactGraph.Adj a b) :
    ¬ A.IsLattice ↔ ∃ i j, A.contactGraph.Adj i j ∧
      (A.center j - A.center i) ^ 6 ≠ (A.center b - A.center a) ^ 6 := by
  have : Nonempty ι := ⟨a⟩
  rw [isLattice_iff_frameInv hA.connected.preconnected hab.2]
  push Not
  rfl

end Arrangement

end RigidArrangements

/-! ### `O11` again, via frame invariants -/

namespace RigidArrangements

/-- The real parts of the sixth roots of unity are `±1` or `±1/2`. -/
theorem rho_pow_re_sq (m : ℕ) : (rho ^ m).re ^ 2 = 1 ∨ (rho ^ m).re ^ 2 = 1 / 4 := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  rw [← rho_pow_mod_six]
  have : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 6) <;> simp [rho_sq, rho_pow_three, h4, h5] <;> norm_num

/-- `ω = (-√33 + i√3)/6` is not a sixth root of unity. -/
theorem o11Turn_pow_six_ne_one : o11Turn ^ 6 ≠ 1 := by
  intro h
  obtain ⟨m, -, hm⟩ := rho_isPrimitiveRoot.eq_pow_of_pow_eq_one h
  have hre : o11Turn.re ^ 2 = 33 / 36 := by
    simp only [o11Turn]
    rw [div_pow, neg_sq, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
    norm_num
  rw [← hm] at hre
  rcases rho_pow_re_sq m with h1 | h1 <;> rw [h1] at hre <;> norm_num at hre

/-- **`O11` is off the lattice, by frames**: the bar `X Y` is horizontal (frame invariant `64`),
while the contact between circles `0` and `1` of the left chevron has frame invariant `64 ω⁶`. -/
theorem Arrangement.o11_not_isLattice' : ¬ Arrangement.o11.IsLattice := by
  have t01 : Tangent Arrangement.o11.center 0 1 := (Arrangement.o11_tangent_iff 0 1).2 (by decide)
  refine Arrangement.not_isLattice_of_frameInv_ne t01 Arrangement.o11_tangent_zero_six ?_
  have c0 : Arrangement.o11.center 0 = 0 := o11Left_zero
  have c6 : Arrangement.o11.center 6 = 2 := o11Right_zero
  have c1 : Arrangement.o11.center 1 = 2 * o11Turn := by
    change o11Left 1 = _
    simp only [o11Left, o11Place, o11Sites]
    rw [show latticePoint ((![(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (-1, 2)] : Fin 6 → ℤ × ℤ) 1)
      = 2 by apply Complex.ext <;> simp [latticePoint]]
    rw [map_ofNat, mul_comm]
  rw [c0, c1, c6, sub_zero, sub_zero, mul_pow]
  intro h
  apply o11Turn_pow_six_ne_one
  have : (2 : ℂ) ^ 6 * o11Turn ^ 6 = 2 ^ 6 * 1 := by rw [h]; ring
  exact mul_left_cancel₀ (by norm_num) this

end RigidArrangements


/-! ===================== Grow.lean ===================== -/

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


/-! ===================== Compat.lean ===================== -/

/-!
# Scratch prototype (not in the repo): decidable off-lattice tests on `ℤ × ℤ` data

Two tests, both generalizing `Arrangement.o11_not_isLattice`.

* **T1, the hinge-triangle test** `normTriangle N₁ N₂`: is there a lattice triangle with side
  norms `N₁`, `N₂`, `1`? If not, any arrangement with circles `h, x, y`, `|hx|² = 4N₁`,
  `|hy|² = 4N₂` and `x, y` touching is off the lattice
  (`Arrangement.not_isLattice_of_normTriangle_eq_false`). O11 is `N₁ = N₂ = 3`.
* **T2, the frame-compatibility test** `frameCompatible u v`: some lattice symmetry `M` has
  `eNorm (u - M v) = 1`. If it fails for the bar vectors `u = x - h`, `v = y - h` of two lattice
  bodies (each placed by a plane isometry and each containing one contact), the union is off
  the lattice (`Arrangement.not_isLattice_of_frameCompatible_eq_false`).
-/

open ComplexConjugate

namespace RigidArrangements

theorem latticePoint_eq' (v : ℤ × ℤ) : latticePoint v = 2 * ((v.1 : ℂ) + (v.2 : ℂ) * rho) := by
  apply Complex.ext <;> simp [latticePoint] <;> ring

theorem latticePoint_sub' (v w : ℤ × ℤ) :
    latticePoint (v - w) = latticePoint v - latticePoint w := by
  rw [latticePoint_eq', latticePoint_eq', latticePoint_eq']
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-! ### T1: the hinge triangle -/

/-- All lattice vectors of `eNorm` `N` (they lie in the box `[-N, N]²`). -/
def vecsOfNorm (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N).filter fun v => eNorm v = N

theorem mem_vecsOfNorm {N : ℕ} {v : ℤ × ℤ} (h : eNorm v = N) : v ∈ vecsOfNorm N := by
  obtain ⟨a, b⟩ := v
  simp only [eNorm] at h
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, h⟩
  all_goals rcases Nat.eq_zero_or_pos N with hN | hN
  all_goals first
    | (subst hN; push_cast at h; nlinarith [sq_nonneg (a + 2 * b), sq_nonneg (2 * a + b)])
    | (have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
       nlinarith [sq_nonneg (a + 2 * b), sq_nonneg (2 * a + b), sq_nonneg (a - N),
         sq_nonneg (b - N), sq_nonneg (a + N), sq_nonneg (b + N)])

/-- **T1.** Is there a lattice triangle with side norms `N₁`, `N₂`, `1`? (The third vertex is
the first plus a unit vector.) -/
def normTriangle (N₁ N₂ : ℕ) : Bool :=
  decide (∃ a ∈ vecsOfNorm N₁, ∃ e ∈ latticeUnits, eNorm (a + e) = N₂)

theorem eNorm_neg' (v : ℤ × ℤ) : eNorm (-v) = eNorm v := by
  simp only [eNorm, Prod.fst_neg, Prod.snd_neg]; ring

theorem normTriangle_of_exists {N₁ N₂ : ℕ} {a b : ℤ × ℤ} (ha : eNorm a = N₁) (hb : eNorm b = N₂)
    (hab : eNorm (a - b) = 1) : normTriangle N₁ N₂ = true := by
  have he : eNorm (b - a) = 1 := by rw [← neg_sub, eNorm_neg', hab]
  have hmem : ∀ e : ℤ × ℤ, eNorm e = 1 → e ∈ latticeUnits := by
    intro e h
    obtain ⟨p, q⟩ := e
    simp only [eNorm] at h
    have h1 : p ≤ 1 := by nlinarith [sq_nonneg (p + 2 * q)]
    have h2 : -1 ≤ p := by nlinarith [sq_nonneg (p + 2 * q)]
    have h3 : q ≤ 1 := by nlinarith [sq_nonneg (2 * p + q)]
    have h4 : -1 ≤ q := by nlinarith [sq_nonneg (2 * p + q)]
    revert h
    interval_cases p <;> interval_cases q <;> decide
  simp only [normTriangle, decide_eq_true_eq]
  exact ⟨a, mem_vecsOfNorm ha, b - a, hmem _ he, by rw [add_sub_cancel, hb]⟩

namespace Arrangement

variable {ι : Type*}

/-- **T1 rules out the lattice.** Circles `h, x, y` with `|hx|² = 4N₁`, `|hy|² = 4N₂`, `x` and `y`
touching, and no lattice triangle with side norms `N₁, N₂, 1`: then `A` is off the lattice. -/
theorem not_isLattice_of_normTriangle_eq_false {A : Arrangement ι} {h x y : ι} {N₁ N₂ : ℕ}
    (hx : dist (A.center h) (A.center x) ^ 2 = 4 * N₁)
    (hy : dist (A.center h) (A.center y) ^ 2 = 4 * N₂)
    (hxy : Tangent A.center x y) (hT : normTriangle N₁ N₂ = false) : ¬ A.IsLattice := by
  rintro ⟨g, f, hf⟩
  have hd : ∀ i j, dist (latticePoint (f i)) (latticePoint (f j)) =
      dist (A.center i) (A.center j) := fun i j => by rw [← hf, ← hf, g.dist_map]
  have en : ∀ j (N : ℕ), dist (A.center h) (A.center j) ^ 2 = 4 * N →
      eNorm (f h - f j) = N := by
    intro j N hj
    have := dist_latticePoint_sq (f h) (f j)
    rw [hd, hj] at this
    exact_mod_cast (by linarith : ((eNorm (f h - f j) : ℤ) : ℝ) = (N : ℝ))
  have e1 : eNorm (f x - f y) = 1 := (tangent_latticePoint_iff _ _).1 ((hd x y).trans hxy)
  have := normTriangle_of_exists (en x N₁ hx) (en y N₂ hy)
    (by rw [show f h - f x - (f h - f y) = -(f x - f y) by abel, eNorm_neg', e1])
  rw [this] at hT
  exact Bool.noConfusion hT

/-- `O11` once more: `normTriangle 3 3 = false` by the kernel. -/
theorem o11_not_isLattice'' : ¬ o11.IsLattice :=
  not_isLattice_of_normTriangle_eq_false (N₁ := 3) (N₂ := 3)
    (by rw [o11_dist_sq_five_zero]; norm_num) (by rw [o11_dist_sq_five_six]; norm_num)
    o11_tangent_zero_six (by decide)

end Arrangement

/-! ### T2: frame compatibility -/

/-- **T2.** Some lattice symmetry `M` puts `M v` at distance one from `u`. -/
def frameCompatible (u v : ℤ × ℤ) : Bool :=
  latticeSymmetries.any fun M => eNorm (u - latticeMatApply M v) == 1

/-- Composition of integer matrices `(a, b, c, d)`. -/
def matMul : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ
  | (a, b, c, d), (a', b', c', d') => (a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d')

theorem latticeMatApply_matMul (M N : ℤ × ℤ × ℤ × ℤ) (v : ℤ × ℤ) :
    latticeMatApply (matMul M N) v = latticeMatApply M (latticeMatApply N v) := by
  obtain ⟨a, b, c, d⟩ := M
  obtain ⟨a', b', c', d'⟩ := N
  obtain ⟨p, q⟩ := v
  simp only [latticeMatApply, matMul, Prod.mk.injEq]
  constructor <;> ring

/-- The twelve symmetries form a group: `M₁⁻¹ M₂` is again a symmetry. -/
theorem exists_latticeSymmetry_div : ∀ M₁ ∈ latticeSymmetries, ∀ M₂ ∈ latticeSymmetries,
    ∃ M ∈ latticeSymmetries, matMul M₁ M = M₂ := by
  decide

/-- Rotations by `ρ^k` act on the lattice by symmetries. -/
theorem exists_latticeSymmetry_rho_pow (k : ℕ) :
    ∃ M ∈ latticeSymmetries, ∀ v, rho ^ k * latticePoint v = latticePoint (latticeMatApply M v) := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  rw [← rho_pow_mod_six]
  have : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 6)
  · exact ⟨(1, 0, 0, 1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq']; simp [latticeMatApply]⟩
  · exact ⟨(0, -1, 1, 1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq']; simp only [latticeMatApply]; push_cast
      linear_combination 2 * (v.2 : ℂ) * rho_sq⟩
  · exact ⟨(-1, -1, 1, 0), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', rho_sq]; simp only [latticeMatApply]; push_cast
      linear_combination 2 * (v.2 : ℂ) * rho_sq⟩
  · exact ⟨(-1, 0, 0, -1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', rho_pow_three]; simp only [latticeMatApply]
      push_cast; ring⟩
  · exact ⟨(0, 1, -1, -1), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', h4]; simp only [latticeMatApply]; push_cast
      linear_combination -2 * (v.2 : ℂ) * rho_sq⟩
  · exact ⟨(1, 1, -1, 0), by decide, fun v => by
      rw [latticePoint_eq', latticePoint_eq', h5]; simp only [latticeMatApply]; push_cast
      linear_combination -2 * (v.2 : ℂ) * rho_sq⟩

/-- Complex conjugation acts on the lattice by the reflection `(p, q) ↦ (p + q, -q)`. -/
theorem conj_latticePoint (v : ℤ × ℤ) :
    conj (latticePoint v) = latticePoint (latticeMatApply (1, 1, 0, -1) v) := by
  apply Complex.ext <;> simp [latticePoint, latticeMatApply] <;> ring

/-- `ρ^k ∘ conj` acts on the lattice by symmetries. -/
theorem exists_latticeSymmetry_rho_pow_conj (k : ℕ) :
    ∃ M ∈ latticeSymmetries, ∀ v, rho ^ k * conj (latticePoint v) =
      latticePoint (latticeMatApply M v) := by
  obtain ⟨M, hM, h⟩ := exists_latticeSymmetry_rho_pow k
  refine ⟨matMul M (1, 1, 0, -1), ?_, fun v => by rw [conj_latticePoint, h, latticeMatApply_matMul]⟩
  have key : ∀ M ∈ latticeSymmetries, matMul M (1, 1, 0, -1) ∈ latticeSymmetries := by decide
  exact key M hM

/-- **Lattice-preserving linear isometries.** If the linear isometry `L` of the plane maps one
unit lattice vector to a unit lattice vector, it acts on the whole lattice as one of the twelve
symmetries. -/
theorem exists_latticeSymmetry_of_linearIsometry (L : ℂ ≃ₗᵢ[ℝ] ℂ) {e e' : ℤ × ℤ}
    (he : eNorm e = 1) (he' : eNorm e' = 1) (hL : L (latticePoint e) = latticePoint e') :
    ∃ M ∈ latticeSymmetries, ∀ v, L (latticePoint v) = latticePoint (latticeMatApply M v) := by
  have unit : ∀ {w : ℤ × ℤ}, eNorm w = 1 → ∃ m : ℕ, latticePoint w = 2 * rho ^ m := by
    intro w hw
    obtain ⟨M, hM, h⟩ := (⟨(1, 0, 0, 1), by decide, fun _ => rfl⟩ :
      ∃ M ∈ latticeSymmetries, ∀ v : ℤ × ℤ, latticeMatApply M v = latticeMatApply M v)
    clear h hM M
    have hm : w ∈ latticeUnits := by
      obtain ⟨p, q⟩ := w
      simp only [eNorm] at hw
      have h1 : p ≤ 1 := by nlinarith [sq_nonneg (p + 2 * q)]
      have h2 : -1 ≤ p := by nlinarith [sq_nonneg (p + 2 * q)]
      have h3 : q ≤ 1 := by nlinarith [sq_nonneg (2 * p + q)]
      have h4 : -1 ≤ q := by nlinarith [sq_nonneg (2 * p + q)]
      revert hw
      interval_cases p <;> interval_cases q <;> decide
    have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
    have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
    simp only [latticeUnits, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by rw [latticePoint_eq']; simp⟩
    · exact ⟨1, by rw [latticePoint_eq']; simp⟩
    · exact ⟨2, by rw [latticePoint_eq', rho_sq]; push_cast; ring⟩
    · exact ⟨3, by rw [latticePoint_eq', rho_pow_three]; push_cast; ring⟩
    · exact ⟨4, by rw [latticePoint_eq', h4]; push_cast; ring⟩
    · exact ⟨5, by rw [latticePoint_eq', h5]; push_cast; ring⟩
  obtain ⟨m, hm⟩ := unit he
  obtain ⟨m', hm'⟩ := unit he'
  have hρ0 : rho ≠ 0 := rho_ne_zero
  -- ρ^(6 m) = 1
  have hinv : rho ^ (5 * m) * rho ^ m = 1 := by
    rw [← pow_add, show 5 * m + m = 6 * m by ring, pow_mul, rho_pow_six, one_pow]
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex L
  · -- rotation: a = ρ^(m' + 5m)
    rw [ha, rotation_apply, hm, hm'] at hL
    have haρ : (a : ℂ) = rho ^ (m' + 5 * m) := by
      have : (a : ℂ) * rho ^ m = rho ^ m' := by
        linear_combination hL / 2
      calc (a : ℂ) = (a : ℂ) * (rho ^ (5 * m) * rho ^ m) := by rw [hinv, mul_one]
        _ = rho ^ (m' + 5 * m) := by rw [pow_add]; linear_combination rho ^ (5 * m) * this
    obtain ⟨M, hM, h⟩ := exists_latticeSymmetry_rho_pow (m' + 5 * m)
    exact ⟨M, hM, fun v => by rw [ha, rotation_apply, haρ, h]⟩
  · -- reflection: a = ρ^(m' + m)
    rw [ha, LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply, hm, hm',
      map_mul, map_pow, conj_rho, map_ofNat] at hL
    have h56 : (rho ^ 5) ^ m * rho ^ m = 1 := by
      rw [← pow_mul, ← pow_add, show 5 * m + m = 6 * m by ring, pow_mul, rho_pow_six, one_pow]
    have haρ : (a : ℂ) = rho ^ (m' + m) := by
      have : (a : ℂ) * (rho ^ 5) ^ m = rho ^ m' := by linear_combination hL / 2
      calc (a : ℂ) = (a : ℂ) * ((rho ^ 5) ^ m * rho ^ m) := by rw [h56, mul_one]
        _ = rho ^ (m' + m) := by rw [pow_add]; linear_combination rho ^ m * this
    obtain ⟨M, hM, h⟩ := exists_latticeSymmetry_rho_pow_conj (m' + m)
    exact ⟨M, hM, fun v => by
      rw [ha, LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply, haρ, h]⟩

namespace Arrangement

variable {ι : Type*}

/-- An isometry of the plane that puts a body (placed on lattice sites by `T`) with one contact
`p p'` onto the lattice moves the body's lattice vectors by a lattice symmetry. -/
theorem body_symm {A : Arrangement ι} (T g : Plane ≃ᵃⁱ[ℝ] Plane) (f : ι → ℤ × ℤ)
    (hf : ∀ i, g (A.center i) = latticePoint (f i)) {p p' : ι} {p₁ p₁' : ℤ × ℤ}
    (ep : A.center p = T (latticePoint p₁)) (ep' : A.center p' = T (latticePoint p₁'))
    (hp : eNorm (p₁ - p₁') = 1) :
    ∃ M ∈ latticeSymmetries, ∀ {i j : ι} {i₁ j₁ : ℤ × ℤ}, A.center i = T (latticePoint i₁) →
      A.center j = T (latticePoint j₁) → f i - f j = latticeMatApply M (i₁ - j₁) := by
  let G := T.trans g
  have hG : ∀ {i : ι} {i₁ : ℤ × ℤ}, A.center i = T (latticePoint i₁) →
      G (latticePoint i₁) = latticePoint (f i) := by
    intro i i₁ hi
    simp only [G, AffineIsometryEquiv.coe_trans, Function.comp_apply, ← hi, hf]
  have hL : ∀ {i j : ι} {i₁ j₁ : ℤ × ℤ}, A.center i = T (latticePoint i₁) →
      A.center j = T (latticePoint j₁) →
      G.linearIsometryEquiv (latticePoint (i₁ - j₁)) = latticePoint (f i - f j) := by
    intro i j i₁ j₁ hi hj
    have := G.map_vsub (latticePoint i₁) (latticePoint j₁)
    simp only [vsub_eq_sub] at this
    rw [latticePoint_sub', this, hG hi, hG hj, latticePoint_sub']
  have hpp : eNorm (f p - f p') = 1 := by
    rw [← tangent_latticePoint_iff, ← hf, ← hf, g.dist_map, ep, ep', T.dist_map,
      tangent_latticePoint_iff, hp]
  obtain ⟨M, hM, hMv⟩ := exists_latticeSymmetry_of_linearIsometry G.linearIsometryEquiv hp hpp
    (hL ep ep')
  exact ⟨M, hM, fun hi hj => latticePoint_injective (by rw [← hMv, hL hi hj])⟩

/-- **T2 rules out the lattice.** Two bodies, placed on lattice sites by plane isometries `T₁`
and `T₂`, each containing a contact (`p p'`, `q q'`), share the hinge `h` and are joined by a
bar `x y`. If no lattice symmetry brings `y₂ - h₂` to distance one from `x₁ - h₁`, the
arrangement is off the lattice. -/
theorem not_isLattice_of_frameCompatible_eq_false {A : Arrangement ι}
    (T₁ T₂ : Plane ≃ᵃⁱ[ℝ] Plane) {h x p p' y q q' : ι}
    {h₁ x₁ p₁ p₁' h₂ y₂ q₂ q₂' : ℤ × ℤ}
    (eh₁ : A.center h = T₁ (latticePoint h₁)) (ex : A.center x = T₁ (latticePoint x₁))
    (ep : A.center p = T₁ (latticePoint p₁)) (ep' : A.center p' = T₁ (latticePoint p₁'))
    (eh₂ : A.center h = T₂ (latticePoint h₂)) (ey : A.center y = T₂ (latticePoint y₂))
    (eq : A.center q = T₂ (latticePoint q₂)) (eq' : A.center q' = T₂ (latticePoint q₂'))
    (hp : eNorm (p₁ - p₁') = 1) (hq : eNorm (q₂ - q₂') = 1) (hxy : Tangent A.center x y)
    (hfc : frameCompatible (x₁ - h₁) (y₂ - h₂) = false) : ¬ A.IsLattice := by
  rintro ⟨g, f, hf⟩
  obtain ⟨M₁, hM₁, hb₁⟩ := body_symm T₁ g f hf ep ep' hp
  obtain ⟨M₂, hM₂, hb₂⟩ := body_symm T₂ g f hf eq eq' hq
  have hx := hb₁ ex eh₁
  have hy := hb₂ ey eh₂
  have e1 : eNorm (f x - f y) = 1 := by
    rw [← tangent_latticePoint_iff, ← hf, ← hf, g.dist_map]; exact hxy
  obtain ⟨M, hM, hMM⟩ := exists_latticeSymmetry_div M₁ hM₁ M₂ hM₂
  have : eNorm ((x₁ - h₁) - latticeMatApply M (y₂ - h₂)) = 1 := by
    rw [← eNorm_latticeMatApply hM₁, ← latticeMatApply_sub, ← latticeMatApply_matMul, hMM, ← hx,
      ← hy, show f x - f h - (f y - f h) = f x - f y by abel, e1]
  have ht : frameCompatible (x₁ - h₁) (y₂ - h₂) = true := by
    simp only [frameCompatible, List.any_eq_true, beq_iff_eq]
    exact ⟨M, hM, this⟩
  rw [ht] at hfc
  exact Bool.noConfusion hfc

end Arrangement

end RigidArrangements


/-! ===================== HBLean.lean ===================== -/

/-!
# Scratch prototype (not in the repo): the general hinge-and-bar constructor

Two lattice bodies, given as lists of lattice sites, are glued at a hinge and locked by a bar at
the exact angle. Normalization: both bodies have their hinge at the lattice origin `0`; body 1 is
the list `l₁` (which contains `0`), body 2 is `0 :: l₂`. The bar runs from `u ∈ l₁` to `v ∈ l₂`.
Body 2 is turned about the hinge by the unit complex number `hbAlpha u v σ` (`σ = ±1` picks one
of the two positions; to reflect body 2, pass its mirror image `l₂.map econj`).

* `eis`, `eis_mul`, `eis_econj`: lattice sites are Eisenstein integers (`latticePoint v = 2 eis v`).
* `norm_hbAlpha`, `dist_bar`: the turn is a unit and the bar has length `2`.
* `dist_sq_cross`: every squared distance between the bodies is `A + B √(3D)` with `A, B`
  rational and computable (`crossAB`).
* `nonnegSqrt_sound`: the decidable sign test for `p + q √M`.
* `hbCenter`, `isLocallyRigid_hbCenter`: the placement is rigid (hinge-and-bar lemma).
* `hbCheck`, `hbArr`, `hbArr_isRigid`: if the decidable test `hbCheck` passes, the placement is an
  arrangement (no overlaps), and it is rigid.
-/

open ComplexConjugate

namespace RigidArrangements

/-! ### Eisenstein integers -/

/-- Product in `ℤ[ρ]`, `ρ² = ρ - 1`, on coordinates `a + bρ ↦ (a, b)`. -/
def emul (x y : ℤ × ℤ) : ℤ × ℤ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

/-- Conjugation in `ℤ[ρ]`: `conj ρ = 1 - ρ`. -/
def econj (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + x.2, -x.2)

/-- The Eisenstein integer `a + bρ` as a complex number. -/
noncomputable def eis (a : ℤ × ℤ) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * rho

theorem latticePoint_eq_eis (v : ℤ × ℤ) : latticePoint v = 2 * eis v := by
  apply Complex.ext <;> simp [latticePoint, eis] <;> ring

theorem eis_mul (a b : ℤ × ℤ) : eis (emul a b) = eis a * eis b := by
  simp only [eis, emul]
  push_cast
  linear_combination (-(a.2 : ℂ) * b.2) * rho_sq

theorem conj_rho' : conj rho = 1 - rho := by
  apply Complex.ext <;> simp [rho_re, rho_im] <;> norm_num

theorem eis_econj (a : ℤ × ℤ) : eis (econj a) = conj (eis a) := by
  simp only [eis, econj, map_add, map_mul, map_intCast, conj_rho']
  push_cast
  ring

theorem eis_re (a : ℤ × ℤ) : (eis a).re = a.1 + a.2 / 2 := by
  simp [eis, rho_re]; ring

theorem eis_im (a : ℤ × ℤ) : (eis a).im = a.2 * Real.sqrt 3 / 2 := by
  simp [eis, rho_im]; ring

theorem normSq_eis (a : ℤ × ℤ) : Complex.normSq (eis a) = eNorm a := by
  rw [Complex.normSq_apply, eis_re, eis_im]
  have h3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [eNorm]
  push_cast
  linear_combination ((a.2 : ℝ) ^ 2 / 4) * h3

theorem eis_zero : eis 0 = 0 := by simp [eis]

theorem latticePoint_zero' : latticePoint 0 = 0 := by
  apply Complex.ext <;> simp [latticePoint]

theorem eis_ne_zero {a : ℤ × ℤ} (h : a ≠ 0) : eis a ≠ 0 := by
  intro h0
  have := normSq_eis a
  rw [h0, map_zero] at this
  have h' : eNorm a = 0 := by exact_mod_cast this.symm
  exact h ((eNorm_eq_zero_iff a).1 h')

/-! ### The turn of body 2 -/

/-- `D = 4 N₁ N₂ - (N₁ + N₂ - 1)²`: the triangle hinge–bar has sides `2√N₁, 2√N₂, 2`, and its
area is `√D` (so `D ≥ 0` is needed for the bar to close, `D = 0` when it is flat). -/
def hbD (u v : ℤ × ℤ) : ℤ := 4 * eNorm u * eNorm v - (eNorm u + eNorm v - 1) ^ 2

/-- `w = (c + σ i √D) / (2 N₁)`, `c = N₁ + N₂ - 1`: the bar end `Y` of body 2 is at `w · X`. -/
noncomputable def hbW (u v : ℤ × ℤ) (σ : ℝ) : ℂ :=
  ⟨((eNorm u + eNorm v - 1 : ℤ) : ℝ) / (2 * eNorm u), σ * Real.sqrt (hbD u v) / (2 * eNorm u)⟩

/-- The turn `α = w U / V = w · eis u · conj (eis v) / N₂`. -/
noncomputable def hbAlpha (u v : ℤ × ℤ) (σ : ℝ) : ℂ :=
  hbW u v σ * eis u * conj (eis v) / (eNorm v : ℂ)

section Turn

variable {u v : ℤ × ℤ} {σ : ℝ}

theorem eNorm_pos' {a : ℤ × ℤ} (h : a ≠ 0) : (0 : ℝ) < eNorm a := by
  have := (eNorm_eq_zero_iff a).not.2 h
  have h0 := eNorm_nonneg a
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm this)

/-- `c² + (σ √D)² = 4 N₁ N₂`. -/
theorem hb_key (hD : 0 ≤ hbD u v) (hσ : σ ^ 2 = 1) :
    ((eNorm u + eNorm v - 1 : ℤ) : ℝ) ^ 2 + (σ * Real.sqrt (hbD u v)) ^ 2 =
      4 * eNorm u * eNorm v := by
  rw [mul_pow, hσ, one_mul, Real.sq_sqrt (by exact_mod_cast hD)]
  simp only [hbD]
  push_cast
  ring

theorem normSq_hbW (hu : u ≠ 0) (hD : 0 ≤ hbD u v) (hσ : σ ^ 2 = 1) :
    Complex.normSq (hbW u v σ) = eNorm v / eNorm u := by
  have hN := eNorm_pos' hu
  have key := hb_key hD hσ
  rw [Complex.normSq_apply]
  simp only [hbW]
  rw [show ((eNorm u + eNorm v - 1 : ℤ) : ℝ) / (2 * eNorm u) * (((eNorm u + eNorm v - 1 : ℤ) : ℝ) /
      (2 * eNorm u)) + σ * Real.sqrt (hbD u v) / (2 * eNorm u) *
      (σ * Real.sqrt (hbD u v) / (2 * eNorm u)) = (((eNorm u + eNorm v - 1 : ℤ) : ℝ) ^ 2 +
      (σ * Real.sqrt (hbD u v)) ^ 2) / (4 * (eNorm u) ^ 2) by ring, key]
  field_simp
  try ring

theorem normSq_one_sub_hbW (hu : u ≠ 0) (hD : 0 ≤ hbD u v) (hσ : σ ^ 2 = 1) :
    Complex.normSq (1 - hbW u v σ) = 1 / eNorm u := by
  have hN := eNorm_pos' hu
  have key := hb_key hD hσ
  rw [Complex.normSq_apply]
  simp only [hbW, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  have e : (1 - ((eNorm u + eNorm v - 1 : ℤ) : ℝ) / (2 * eNorm u)) *
      (1 - ((eNorm u + eNorm v - 1 : ℤ) : ℝ) / (2 * eNorm u)) +
      (0 - σ * Real.sqrt (hbD u v) / (2 * eNorm u)) * (0 - σ * Real.sqrt (hbD u v) / (2 * eNorm u)) =
      ((2 * eNorm u - ((eNorm u + eNorm v - 1 : ℤ) : ℝ)) ^ 2 + (σ * Real.sqrt (hbD u v)) ^ 2) /
        (4 * (eNorm u) ^ 2) := by
    field_simp; ring
  rw [e]
  have key' : (2 * (eNorm u : ℝ) - ((eNorm u + eNorm v - 1 : ℤ) : ℝ)) ^ 2 +
      (σ * Real.sqrt (hbD u v)) ^ 2 = 4 * eNorm u := by
    have : (2 * (eNorm u : ℝ) - ((eNorm u + eNorm v - 1 : ℤ) : ℝ)) ^ 2 =
        ((eNorm u + eNorm v - 1 : ℤ) : ℝ) ^ 2 - 4 * eNorm u * eNorm v + 4 * eNorm u := by
      push_cast; ring
    rw [this]; linarith
  rw [key']
  field_simp
  try ring

theorem eNorm_pos {a : ℤ × ℤ} (h : a ≠ 0) : (0 : ℝ) < eNorm a := by
  have := (eNorm_eq_zero_iff a).not.2 h
  have h0 := eNorm_nonneg a
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm this)

/-- **The turn is a rotation**: `‖α‖ = 1`. -/
theorem norm_hbAlpha (hu : u ≠ 0) (hv : v ≠ 0) (hD : 0 ≤ hbD u v) (hσ : σ ^ 2 = 1) :
    ‖hbAlpha u v σ‖ = 1 := by
  have hNu := eNorm_pos hu
  have hNv := eNorm_pos hv
  have h2 : Complex.normSq (hbAlpha u v σ) = 1 := by
    simp only [hbAlpha, map_div₀, map_mul, Complex.normSq_conj, normSq_eis, normSq_hbW hu hD hσ,
      Complex.normSq_intCast]
    field_simp
  rw [Complex.norm_def, h2, Real.sqrt_one]

/-- `α · eis v = w · eis u`. -/
theorem hbAlpha_mul_eis (hv : v ≠ 0) : hbAlpha u v σ * eis v = hbW u v σ * eis u := by
  have hNv : (eNorm v : ℂ) ≠ 0 := by exact_mod_cast (eNorm_pos hv).ne'
  have : conj (eis v) * eis v = (eNorm v : ℂ) := by
    rw [mul_comm, Complex.mul_conj, normSq_eis]; push_cast; rfl
  simp only [hbAlpha]
  field_simp
  linear_combination (hbW u v σ * eis u) * this

/-- **The bar closes**: the bar ends `X = latticePoint u` and `Y = α · latticePoint v` are `2`
apart. -/
theorem dist_bar (hu : u ≠ 0) (hv : v ≠ 0) (hD : 0 ≤ hbD u v) (hσ : σ ^ 2 = 1) :
    dist (latticePoint u) (hbAlpha u v σ * latticePoint v) = 2 := by
  rw [dist_eq_norm, latticePoint_eq_eis, latticePoint_eq_eis,
    show 2 * eis u - hbAlpha u v σ * (2 * eis v) = 2 * (eis u * (1 - hbW u v σ)) by
      linear_combination (-2) * hbAlpha_mul_eis (u := u) (σ := σ) hv]
  have hNu := eNorm_pos hu
  have : Complex.normSq (eis u * (1 - hbW u v σ)) = 1 := by
    rw [map_mul, normSq_eis, normSq_one_sub_hbW hu hD hσ]; field_simp
  rw [norm_mul, Complex.norm_def (eis u * _), this, Real.sqrt_one]
  norm_num

end Turn

/-! ### Exact squared distances across the hinge -/

/-- The rational pair `(A, B)` with `dist² = A + B √(3D)` between the circle of body 1 at `s` and
the circle of body 2 at `t`. -/
def crossAB (u v : ℤ × ℤ) (σ : ℤ) (s t : ℤ × ℤ) : ℚ × ℚ :=
  let N₁ := eNorm u
  let N₂ := eNorm v
  let c := N₁ + N₂ - 1
  let z := emul (emul (econj s) u) (emul t (econj v))
  ((4 * eNorm s + 4 * eNorm t : ℚ) - (2 * c * (2 * z.1 + z.2) : ℚ) / (N₁ * N₂ : ℚ),
    (2 * σ * z.2 : ℚ) / (N₁ * N₂ : ℚ))

theorem norm_sub_sq_eq (a b : ℂ) : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (conj a * b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  simp [Complex.mul_re]

/-- **The distance formula.** -/
theorem dist_sq_cross {u v : ℤ × ℤ} {σ : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hD : 0 ≤ hbD u v)
    (hσ : σ ^ 2 = 1) (s t : ℤ × ℤ) :
    dist (latticePoint s) (hbAlpha u v σ * latticePoint t) ^ 2 =
      ((crossAB u v σ s t).1 : ℝ) + ((crossAB u v σ s t).2 : ℝ) * Real.sqrt (3 * hbD u v) := by
  have hσ' : (σ : ℝ) ^ 2 = 1 := by exact_mod_cast hσ
  have hNu := eNorm_pos hu
  have hNv := eNorm_pos hv
  rw [dist_eq_norm, norm_sub_sq_eq, norm_mul, norm_hbAlpha hu hv hD hσ', one_mul,
    latticePoint_eq_eis, latticePoint_eq_eis]
  have hns : ‖2 * eis s‖ ^ 2 = 4 * eNorm s := by
    rw [Complex.sq_norm, map_mul, normSq_eis, show Complex.normSq 2 = 4 by simp [Complex.normSq_apply]; norm_num]
  have hnt : ‖2 * eis t‖ ^ 2 = 4 * eNorm t := by
    rw [Complex.sq_norm, map_mul, normSq_eis, show Complex.normSq 2 = 4 by simp [Complex.normSq_apply]; norm_num]
  rw [hns, hnt]
  -- the cross term
  set z := emul (emul (econj s) u) (emul t (econj v)) with hz
  have hez : eis z = conj (eis s) * eis u * (eis t * conj (eis v)) := by
    rw [hz, eis_mul, eis_mul, eis_mul, eis_econj, eis_econj]
  have hcross : conj (2 * eis s) * (hbAlpha u v σ * (2 * eis t)) =
      4 * hbW u v σ * eis z / (eNorm v : ℂ) := by
    rw [hez]; simp only [hbAlpha, map_mul, map_ofNat]; ring
  rw [hcross]
  have hre : (4 * hbW u v σ * eis z / (eNorm v : ℂ)).re =
      4 * ((hbW u v σ).re * (eis z).re - (hbW u v σ).im * (eis z).im) / eNorm v := by
    rw [show (eNorm v : ℂ) = ((eNorm v : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
    simp [Complex.mul_re]
    ring
  rw [hre, eis_re, eis_im]
  simp only [hbW, crossAB]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  field_simp
  ring

/-! ### Deciding the sign of `p + q √M` -/

/-- `p + q √M ≥ 0`, decided exactly. -/
def nonnegSqrt (p q : ℚ) (M : ℤ) : Bool :=
  (0 ≤ p && 0 ≤ q) || (0 ≤ p && q < 0 && q * q * M ≤ p * p) ||
    (p < 0 && 0 < q && p * p ≤ q * q * M)

theorem nonnegSqrt_sound {p q : ℚ} {M : ℤ} (hM : 0 ≤ M) (h : nonnegSqrt p q M = true) :
    (0 : ℝ) ≤ (p : ℝ) + (q : ℝ) * Real.sqrt M := by
  have hs := Real.sqrt_nonneg (M : ℝ)
  have hss := Real.sq_sqrt (show (0 : ℝ) ≤ M by exact_mod_cast hM)
  simp only [nonnegSqrt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hp, hq⟩ | ⟨⟨hp, hq⟩, hpq⟩⟩ | ⟨⟨hp, hq⟩, hpq⟩
  · have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
    have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  · have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
    have hq' : (q : ℝ) < 0 := by exact_mod_cast hq
    have hpq' : (q : ℝ) * q * M ≤ p * p := by exact_mod_cast hpq
    -- (q √M)² ≤ p², q √M ≤ 0 ≤ p
    nlinarith [sq_nonneg ((p : ℝ) + q * Real.sqrt M), mul_nonneg hp' hs]
  · have hp' : (p : ℝ) < 0 := by exact_mod_cast hp
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hpq' : (p : ℝ) * p ≤ q * q * M := by exact_mod_cast hpq
    nlinarith [sq_nonneg ((p : ℝ) + q * Real.sqrt M), mul_nonneg hq'.le hs]

/-! ### The arrangement -/

/-- Centers: body 1 at `latticePoint (l₁.get i)`, body 2 (without its hinge) at
`α · latticePoint (l₂.get j)`. -/
noncomputable def hbCenter (l₁ l₂ : List (ℤ × ℤ)) (u v : ℤ × ℤ) (σ : ℤ) :
    Fin l₁.length ⊕ Fin l₂.length → Plane
  | .inl i => latticePoint (l₁.get i)
  | .inr j => hbAlpha u v σ * latticePoint (l₂.get j)

/-- **The decidable validity test.** Distinct sites in each body, the hinge `0` in body 1 and not
listed in body 2, bar ends present and nonzero, the bar closes (`D ≥ 0`), `σ = ±1`, build
certificates for both bodies, and every pair across the hinge at least `2` apart. -/
def hbCheck (l₁ l₂ : List (ℤ × ℤ)) (u v : ℤ × ℤ) (σ : ℤ) : Bool :=
  l₁.Nodup && (0 :: l₂).Nodup && (0 : ℤ × ℤ) ∈ l₁ && u ∈ l₁ && v ∈ l₂ && u ≠ 0 &&
    0 ≤ hbD u v && σ ^ 2 = 1 && latticeBuilt l₁ && latticeBuilt (0 :: l₂) &&
    (l₁.filter (· ≠ 0)).all fun s => l₂.all fun t =>
      nonnegSqrt ((crossAB u v σ s t).1 - 4) (crossAB u v σ s t).2 (3 * hbD u v)

section Construction

variable {l₁ l₂ : List (ℤ × ℤ)} {u v : ℤ × ℤ} {σ : ℤ}

/-- Unpacking `hbCheck`. -/
structure HBOk (l₁ l₂ : List (ℤ × ℤ)) (u v : ℤ × ℤ) (σ : ℤ) : Prop where
  nd₁ : l₁.Nodup
  nd₂ : (0 :: l₂).Nodup
  h0 : (0 : ℤ × ℤ) ∈ l₁
  hu : u ∈ l₁
  hv : v ∈ l₂
  hu0 : u ≠ 0
  hD : 0 ≤ hbD u v
  hσ : σ ^ 2 = 1
  b₁ : latticeBuilt l₁ = true
  b₂ : latticeBuilt (0 :: l₂) = true
  sep : ∀ s ∈ l₁, s ≠ 0 → ∀ t ∈ l₂,
    nonnegSqrt ((crossAB u v σ s t).1 - 4) (crossAB u v σ s t).2 (3 * hbD u v) = true

theorem HBOk.of_check (h : hbCheck l₁ l₂ u v σ = true) : HBOk l₁ l₂ u v σ := by
  simp only [hbCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filter,
    ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun s hs hs0 t ht => h11 s ⟨hs, hs0⟩ t ht⟩

theorem HBOk.v0 (h : HBOk l₁ l₂ u v σ) : v ≠ 0 := by
  rintro rfl
  exact (List.nodup_cons.1 h.nd₂).1 h.hv

theorem HBOk.normα (h : HBOk l₁ l₂ u v σ) : ‖hbAlpha u v σ‖ = 1 :=
  norm_hbAlpha h.hu0 h.v0 h.hD (by exact_mod_cast h.hσ)

/-- No two circles overlap. -/
theorem HBOk.two_le_dist (h : HBOk l₁ l₂ u v σ) :
    Pairwise fun i j => 2 ≤ dist (hbCenter l₁ l₂ u v σ i) (hbCenter l₁ l₂ u v σ j) := by
  have hα := h.normα
  have hl₂0 : ∀ t ∈ l₂, t ≠ 0 := fun t ht e => (List.nodup_cons.1 h.nd₂).1 (e ▸ ht)
  have nd₂' := (List.nodup_cons.1 h.nd₂).2
  have cross : ∀ (i : Fin l₁.length) (j : Fin l₂.length),
      2 ≤ dist (latticePoint (l₁.get i)) (hbAlpha u v σ * latticePoint (l₂.get j)) := by
    intro i j
    by_cases hs : l₁.get i = 0
    · rw [hs, latticePoint_zero', dist_comm, dist_zero_right,
        norm_mul, hα, one_mul, ← dist_zero_right,
        latticePoint_zero'.symm, dist_comm]
      exact two_le_dist_latticePoint (hl₂0 _ (List.get_mem _ _)).symm
    · have hsep := h.sep _ (List.get_mem _ _) hs _ (List.get_mem l₂ j)
      have key := nonnegSqrt_sound (by nlinarith [h.hD]) hsep
      have hf := dist_sq_cross (σ := σ) h.hu0 h.v0 h.hD h.hσ (l₁.get i) (l₂.get j)
      push_cast at key
      have h4 : (4 : ℝ) ≤ dist (latticePoint (l₁.get i)) (hbAlpha u v σ * latticePoint (l₂.get j)) ^ 2 := by
        rw [hf]; push_cast; linarith
      nlinarith [dist_nonneg (x := latticePoint (l₁.get i))
        (y := hbAlpha u v σ * latticePoint (l₂.get j))]
  rintro (i | j) (i' | j') hne
  · exact two_le_dist_latticePoint fun e => hne (congrArg _ (h.nd₁.get_inj_iff.mp e))
  · exact cross i j'
  · rw [dist_comm]; exact cross i' j
  · simp only [hbCenter, dist_eq_norm]
    rw [← mul_sub, norm_mul, hα, one_mul, ← dist_eq_norm]
    exact two_le_dist_latticePoint fun e => hne (congrArg _ (nd₂'.get_inj_iff.mp e))

/-- **The arrangement** of two lattice bodies, hinge and bar, when `hbCheck` passes. -/
noncomputable def hbArr (h : hbCheck l₁ l₂ u v σ = true) :
    Arrangement (Fin l₁.length ⊕ Fin l₂.length) where
  center := hbCenter l₁ l₂ u v σ
  nonoverlap := (HBOk.of_check h).two_le_dist

/-- **It is rigid**, by the hinge-and-bar lemma. -/
theorem hbArr_isRigid (h : hbCheck l₁ l₂ u v σ = true) : (hbArr h).IsRigid := by
  have ok := HBOk.of_check h
  have hα := ok.normα
  obtain ⟨a, ha⟩ := List.mem_iff_get.1 ok.h0
  obtain ⟨x, hx⟩ := List.mem_iff_get.1 ok.hu
  obtain ⟨y, hy⟩ := List.mem_iff_get.1 ok.hv
  -- body 1
  have r₁ : IsLocallyRigid (hbCenter l₁ l₂ u v σ ∘ Sum.inl) :=
    Arrangement.isRigid_ofLattice_of_latticeBuilt ok.nd₁ ok.b₁
  -- body 2, with its hinge
  let f₂ : Fin (0 :: l₂).length → Fin l₁.length ⊕ Fin l₂.length :=
    Fin.cases (Sum.inl a) Sum.inr
  have hf₂ : hbCenter l₁ l₂ u v σ ∘ f₂ = fun k => hbAlpha u v σ * latticePoint ((0 :: l₂).get k) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · show latticePoint (l₁.get a) = hbAlpha u v σ * latticePoint ((0 :: l₂).get 0)
      rw [ha]; simp [latticePoint_zero']
    · simp [f₂, hbCenter]
  have r₂ : IsLocallyRigid (hbCenter l₁ l₂ u v σ ∘ f₂) := by
    rw [hf₂]
    have hc : Congruent (fun k => hbAlpha u v σ * latticePoint ((0 :: l₂).get k))
        (latticePoint ∘ (0 :: l₂).get) := by
      rw [congruent_iff_dist_eq]
      intro i j
      simp only [dist_eq_norm, Function.comp_apply]
      rw [← mul_sub, norm_mul, hα, one_mul]
    exact (isLocallyRigid_iff_of_congruent hc).2
      (Arrangement.isRigid_ofLattice_of_latticeBuilt ok.nd₂ ok.b₂)
  have hcover : ∀ i, (∃ j, Sum.inl j = i) ∨ ∃ j, f₂ j = i := by
    rintro (i | j)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨j.succ, rfl⟩
  have hbar : Tangent (hbCenter l₁ l₂ u v σ) (Sum.inl x) (f₂ y.succ) := by
    show dist (latticePoint (l₁.get x)) (hbAlpha u v σ * latticePoint (l₂.get y)) = 2
    rw [hx, hy]
    exact dist_bar ok.hu0 ok.v0 ok.hD (by exact_mod_cast ok.hσ)
  refine IsLocallyRigid.of_hinge (f₁ := Sum.inl) (f₂ := f₂) hcover r₁ r₂ (a₁ := a) (a₂ := 0)
    rfl hbar ?_ ?_
  · show latticePoint (l₁.get a) ≠ latticePoint (l₁.get x)
    rw [ha, hx]
    exact latticePoint_injective.ne (Ne.symm ok.hu0)
  · show hbCenter l₁ l₂ u v σ (Sum.inl a) ≠ hbAlpha u v σ * latticePoint (l₂.get y)
    simp only [hbCenter, ha, hy, latticePoint_zero']
    intro e
    have : ‖hbAlpha u v σ * latticePoint v‖ = 0 := by rw [← e, norm_zero]
    rw [norm_mul, hα, one_mul, norm_eq_zero] at this
    exact latticePoint_injective.ne ok.v0 (this.trans latticePoint_zero'.symm)

end Construction

/-! ### O11 through the constructor -/

/-- The left chevron of `O11` with its hinge at `0`, and the mirror image of the right one. -/
def o11L₁ : List (ℤ × ℤ) := [(0, 0), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2)]
def o11L₂ : List (ℤ × ℤ) := ((o11L₁.filter (· ≠ 0)).map econj)


end RigidArrangements

namespace RigidArrangements

theorem o11Check : hbCheck o11L₁ o11L₂ (1, -2) (econj (1, -2)) (-1) = true := by decide +kernel

/-- `O11`, rebuilt by the general constructor: two chevrons, hinge at `0`, bar from `(1, -2)` to
the mirror image of `(1, -2)` in body 2, `σ = -1`. All side conditions are kernel computations. -/
noncomputable def o11' := hbArr o11Check

theorem o11'_isRigid : o11'.IsRigid := hbArr_isRigid o11Check

end RigidArrangements


/-! ===================== C5.lean ===================== -/

/-!
# Scratch prototype (not in the repo): reducing C5 to cores

`C5` (every rigid arrangement of at most `10` circles is on the lattice) is equivalent to: no rigid
core with `9` or `10` circles is off the lattice. The reduction is proved here.
-/

namespace RigidArrangements

namespace Arrangement

variable {ι : Type*}

/-- **Adding a removable circle keeps the lattice.** If `A` without its removable circle `w` is on
the lattice, so is `A`: the circle `w` touches two circles less than `4` apart, so it sits at an
apex over two lattice points, which is a lattice point. -/
theorem isLattice_of_removable {n : ℕ} {A : Arrangement (Fin (n + 1))} {w : Fin (n + 1)}
    (hw : A.Removable w) (h : (A.comap w.succAbove Fin.succAbove_right_injective).IsLattice) :
    A.IsLattice := by
  obtain ⟨g, f, hf⟩ := h
  obtain ⟨u, v, huv, hadj, h4⟩ := hw
  have hu := (hadj u).2 (Or.inl rfl)
  have hv := (hadj v).2 (Or.inr rfl)
  -- every circle other than `w` is on a lattice point
  have hbase : ∀ k, k ≠ w → ∃ x, g (A.center k) = latticePoint x := by
    intro k hk
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    exact ⟨f j, hf j⟩
  obtain ⟨a, ha⟩ := hbase u hu.1.symm
  obtain ⟨b, hb⟩ := hbase v hv.1.symm
  have hab : a ≠ b := by
    intro e
    apply huv
    apply A.center_injective
    apply g.injective
    rw [ha, hb, e]
  have h4' : eNorm (a - b) < 4 := by
    have hsq := dist_latticePoint_sq a b
    rw [← ha, ← hb, g.dist_map] at hsq
    have h0 := dist_nonneg (x := A.center u) (y := A.center v)
    have : (eNorm (a - b) : ℝ) < 4 := by nlinarith
    exact_mod_cast this
  obtain ⟨x, -, hx⟩ := exists_mem_latticeApexes hab h4'
    (by rw [← ha, g.dist_map]; exact hu.2) (by rw [← hb, g.dist_map]; exact hv.2)
  have hall : ∀ k, ∃ x, g (A.center k) = latticePoint x := by
    intro k
    by_cases hk : k = w
    · subst hk; exact ⟨x, hx⟩
    · exact hbase k hk
  choose F hF using hall
  exact ⟨g, F, hF⟩

/-- **C5 reduces to cores.** If every rigid core with `9` or `10` circles lies on the lattice, then
every rigid arrangement of at most `10` circles does. -/
theorem isLattice_of_card_le_ten_of_cores
    (hcore : ∀ n, 9 ≤ n → n ≤ 10 → ∀ A : Arrangement (Fin n), A.IsRigid → A.IsCore →
      A.IsLattice) :
    ∀ n, n ≤ 10 → ∀ A : Arrangement (Fin n), A.IsRigid → A.IsLattice := by
  intro n
  induction n with
  | zero => intro _ A hA; exact hA.isLattice_of_card_le_eight (by omega)
  | succ n ih =>
    intro hn A hA
    by_cases h8 : n + 1 ≤ 8
    · exact hA.isLattice_of_card_le_eight h8
    by_cases hc : A.IsCore
    · exact hcore (n + 1) (by omega) hn A hA hc
    · simp only [IsCore, not_forall, not_not] at hc
      obtain ⟨w, hw⟩ := hc
      exact isLattice_of_removable hw (ih (by omega) _ (hw.isRigid_comap_succAbove hA))

end Arrangement

end RigidArrangements


#print axioms RigidArrangements.Arrangement.isLattice_iff_frameInv
#print axioms RigidArrangements.Arrangement.isLattice_of_triGrown
#print axioms RigidArrangements.Arrangement.isRigid_of_grown_pair
#print axioms RigidArrangements.Arrangement.not_isLattice_of_normTriangle_eq_false
#print axioms RigidArrangements.Arrangement.not_isLattice_of_frameCompatible_eq_false
#print axioms RigidArrangements.hbArr_isRigid
#print axioms RigidArrangements.o11'_isRigid
#print axioms RigidArrangements.Arrangement.isLattice_of_card_le_ten_of_cores
#print axioms RigidArrangements.Arrangement.o11_not_isLattice'

/-! ===================== constructor + T1 ===================== -/

namespace RigidArrangements

/-- **Certified off-lattice two-body arrangements.** If `hbCheck` passes and there is no lattice
triangle with side norms `N₁ = eNorm u`, `N₂ = eNorm v`, `1`, then the hinge-and-bar arrangement
is rigid (`hbArr_isRigid`) and off the lattice. -/
theorem hbArr_not_isLattice {l₁ l₂ : List (ℤ × ℤ)} {u v : ℤ × ℤ} {σ : ℤ}
    (h : hbCheck l₁ l₂ u v σ = true)
    (hT : normTriangle (eNorm u).toNat (eNorm v).toNat = false) : ¬ (hbArr h).IsLattice := by
  have ok := HBOk.of_check h
  obtain ⟨a, ha⟩ := List.mem_iff_get.1 ok.h0
  obtain ⟨x, hx⟩ := List.mem_iff_get.1 ok.hu
  obtain ⟨y, hy⟩ := List.mem_iff_get.1 ok.hv
  have cu : ((eNorm u).toNat : ℝ) = eNorm u := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (eNorm_nonneg u)]
  have cv : ((eNorm v).toNat : ℝ) = eNorm v := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (eNorm_nonneg v)]
  refine Arrangement.not_isLattice_of_normTriangle_eq_false (h := Sum.inl a) (x := Sum.inl x)
    (y := Sum.inr y) ?_ ?_ ?_ hT
  · show dist (latticePoint (l₁.get a)) (latticePoint (l₁.get x)) ^ 2 = _
    rw [ha, hx, dist_latticePoint_sq, zero_sub, eNorm_neg', cu]
  · show dist (latticePoint (l₁.get a)) (hbAlpha u v σ * latticePoint (l₂.get y)) ^ 2 = _
    rw [ha, hy, latticePoint_zero', dist_comm, dist_zero_right, norm_mul, ok.normα, one_mul,
      ← dist_zero_right, ← latticePoint_zero', dist_comm, dist_latticePoint_sq, zero_sub,
      eNorm_neg', cv]
  · show dist (latticePoint (l₁.get x)) (hbAlpha u v σ * latticePoint (l₂.get y)) = 2
    rw [hx, hy]
    exact dist_bar ok.hu0 ok.v0 ok.hD (by exact_mod_cast ok.hσ)

/-- `O11` through the constructor is off the lattice (`D = 11`, `normTriangle 3 3 = false`). -/
theorem o11'_not_isLattice : ¬ o11'.IsLattice :=
  hbArr_not_isLattice o11Check (by decide)

/-- **A second certified example**, `n = 13`, `N₁ = N₂ = 4`, `D = 15`: a 5-circle trapezoid and a
9-circle body glued at a hinge, the bar joining the far ends of two straight rows of three circles
(hinge angle `arccos (7/8)`). Coordinates lie in `ℚ(√3, √5)`. -/
def ex13L₁ : List (ℤ × ℤ) := [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2)]
def ex13L₂ : List (ℤ × ℤ) := [(-1, 1), (-1, 0), (-2, 1), (-2, 2), (-1, 2), (-2, 3), (-1, 3), (0, 2)]

theorem ex13Check : hbCheck ex13L₁ ex13L₂ (0, 2) (0, 2) 1 = true := by decide +kernel

noncomputable def ex13 := hbArr ex13Check

theorem ex13_isRigid : ex13.IsRigid := hbArr_isRigid ex13Check

theorem ex13_not_isLattice : ¬ ex13.IsLattice := hbArr_not_isLattice ex13Check (by decide)

end RigidArrangements

#print axioms RigidArrangements.o11'_not_isLattice
#print axioms RigidArrangements.ex13_not_isLattice
#print axioms RigidArrangements.ex13_isRigid

/-! ===================== off-lattice by the turn (D = 3k²) ===================== -/

namespace RigidArrangements

/-- When `D = 3k²`, the turn lies in `ℚ(ρ)`: `α = eis (hbNum) / hbDen`. -/
def hbNum (u v : ℤ × ℤ) (σ k : ℤ) : ℤ × ℤ :=
  emul (eNorm u + eNorm v - 1 - σ * k, 2 * σ * k) (emul u (econj v))

def hbDen (u v : ℤ × ℤ) : ℤ := 2 * eNorm u * eNorm v

theorem eis_sub (a b : ℤ × ℤ) : eis (a - b) = eis a - eis b := by
  simp only [eis, Prod.fst_sub, Prod.snd_sub]; push_cast; ring

theorem eis_injective : Function.Injective eis := by
  intro a b h
  by_contra hab
  exact eis_ne_zero (sub_ne_zero.2 hab) (by rw [eis_sub, h, sub_self])

theorem hbAlpha_eq_of_sq {u v : ℤ × ℤ} {σ k : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hk : 0 ≤ k)
    (hDk : hbD u v = 3 * k ^ 2) :
    hbAlpha u v σ = eis (hbNum u v σ k) / (hbDen u v : ℂ) := by
  have hNu := eNorm_pos hu
  have hNv := eNorm_pos hv
  have hsq : Real.sqrt (hbD u v) = k * Real.sqrt 3 := by
    rw [hDk]; push_cast
    rw [show (3 : ℝ) * k ^ 2 = k ^ 2 * 3 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by exact_mod_cast hk)]
  have hW : hbW u v σ = eis (eNorm u + eNorm v - 1 - σ * k, 2 * σ * k) / (2 * eNorm u : ℂ) := by
    apply Complex.ext
    · simp only [hbW, Complex.div_re, eis_re]
      simp [Complex.normSq_apply]
      field_simp
      try ring
    · simp only [hbW, hsq, Complex.div_im, eis_im]
      simp [Complex.normSq_apply]
      field_simp
      try ring
  simp only [hbAlpha, hW, hbNum, hbDen, eis_mul, eis_econj]
  push_cast
  field_simp

/-- `eis` of a unit is a power of `ρ`, and conversely. -/
theorem exists_unit_eis_eq_rho_pow (m : ℕ) : ∃ r ∈ latticeUnits, eis r = rho ^ m := by
  have h4 : rho ^ 4 = -rho := by rw [pow_succ, rho_pow_three]; ring
  have h5 : rho ^ 5 = 1 - rho := by rw [pow_succ, h4, neg_mul, ← sq, rho_sq]; ring
  rw [← rho_pow_mod_six]
  have : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 6)
  · exact ⟨(1, 0), by decide, by simp [eis]⟩
  · exact ⟨(0, 1), by decide, by simp [eis]⟩
  · exact ⟨(-1, 1), by decide, by simp [eis, rho_sq]; ring⟩
  · exact ⟨(-1, 0), by decide, by simp [eis, rho_pow_three]⟩
  · exact ⟨(0, -1), by decide, by simp [eis, h4]⟩
  · exact ⟨(1, -1), by decide, by simp [eis, h5]; ring⟩

/-- **The turn is not a lattice rotation** when its `ℚ(ρ)` form misses the six units. -/
theorem hbAlpha_pow_six_ne_one {u v : ℤ × ℤ} {σ k : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hk : 0 ≤ k)
    (hDk : hbD u v = 3 * k ^ 2)
    (hnum : ∀ r ∈ latticeUnits, hbNum u v σ k ≠ (hbDen u v * r.1, hbDen u v * r.2)) :
    hbAlpha u v σ ^ 6 ≠ 1 := by
  intro h6
  obtain ⟨m, -, hm⟩ := rho_isPrimitiveRoot.eq_pow_of_pow_eq_one h6
  obtain ⟨r, hr, hre⟩ := exists_unit_eis_eq_rho_pow m
  have hz : hbDen u v ≠ 0 := by
    have a := eNorm_pos hu
    have b := eNorm_pos hv
    have : (0 : ℝ) < ((hbDen u v : ℤ) : ℝ) := by simp only [hbDen]; push_cast; positivity
    exact_mod_cast this.ne'
  have hden : (hbDen u v : ℂ) ≠ 0 := Int.cast_ne_zero.2 hz
  rw [hbAlpha_eq_of_sq hu hv hk hDk, ← hre] at hm
  have : eis (hbNum u v σ k) = eis (hbDen u v * r.1, hbDen u v * r.2) := by
    rw [show eis (hbDen u v * r.1, hbDen u v * r.2) = (hbDen u v : ℂ) * eis r by
      simp only [eis]; push_cast; ring, hm]
    field_simp
  exact hnum r hr (eis_injective this)

/-- **Off the lattice by the turn.** If `hbCheck` passes, `D = 3k²`, the turn is not a lattice
rotation, and each body has a contact (body 2's away from the hinge), the arrangement is off the
lattice: a contact of body 1 and a contact of body 2 are in different frames. Here the hinge and
both bar ends may all be lattice points. -/
theorem hbArr_not_isLattice_of_turn {l₁ l₂ : List (ℤ × ℤ)} {u v : ℤ × ℤ} {σ : ℤ}
    (h : hbCheck l₁ l₂ u v σ = true) {k : ℤ} (hk : 0 ≤ k) (hDk : hbD u v = 3 * k ^ 2)
    (hnum : ∀ r ∈ latticeUnits, hbNum u v σ k ≠ (hbDen u v * r.1, hbDen u v * r.2))
    {p p' q q' : ℤ × ℤ} (hp : p ∈ l₁) (hp' : p' ∈ l₁) (hpp : eNorm (p' - p) = 1)
    (hq : q ∈ l₂) (hq' : q' ∈ l₂) (hqq : eNorm (q' - q) = 1) : ¬ (hbArr h).IsLattice := by
  have ok := HBOk.of_check h
  obtain ⟨ip, hip⟩ := List.mem_iff_get.1 hp
  obtain ⟨ip', hip'⟩ := List.mem_iff_get.1 hp'
  obtain ⟨iq, hiq⟩ := List.mem_iff_get.1 hq
  obtain ⟨iq', hiq'⟩ := List.mem_iff_get.1 hq'
  have t₁ : Tangent (hbArr h).center (Sum.inl ip) (Sum.inl ip') := by
    show dist (latticePoint (l₁.get ip)) (latticePoint (l₁.get ip')) = 2
    rw [hip, hip', tangent_latticePoint_iff, ← eNorm_neg', neg_sub, hpp]
  have t₂ : Tangent (hbArr h).center (Sum.inr iq) (Sum.inr iq') := by
    show dist (hbAlpha u v σ * latticePoint (l₂.get iq)) (hbAlpha u v σ * latticePoint (l₂.get iq')) = 2
    rw [hiq, hiq', dist_eq_norm, ← mul_sub, norm_mul, ok.normα, one_mul, ← dist_eq_norm,
      tangent_latticePoint_iff, ← eNorm_neg', neg_sub, hqq]
  refine Arrangement.not_isLattice_of_frameInv_ne t₁ t₂ ?_
  show (latticePoint (l₁.get ip') - latticePoint (l₁.get ip)) ^ 6 ≠
    (hbAlpha u v σ * latticePoint (l₂.get iq') - hbAlpha u v σ * latticePoint (l₂.get iq)) ^ 6
  rw [hip, hip', hiq, hiq', ← mul_sub, ← latticePoint_sub, ← latticePoint_sub, mul_pow,
    latticePoint_unit_pow_six hpp, latticePoint_unit_pow_six hqq]
  intro e
  apply hbAlpha_pow_six_ne_one ok.hu0 ok.v0 hk hDk hnum
  linear_combination (-1 / 64 : ℂ) * e

/-- **An off-lattice arrangement whose hinge triangle is a lattice triangle** (`n = 15`). The
hinge `0`, the bar ends `X = latticePoint (0, 2) = 2 + 2√3 i` and `Y = 1 + 3√3 i` are lattice
points (`|HX|² = 16`, `|HY|² = 28`, `|XY| = 2`, so the hinge angle `arccos (5/(2√7))` occurs
between lattice vectors), yet body 2 (11 circles) is turned by `α ∈ ℚ(ρ)` with `α⁶ ≠ 1`. -/
def ex15L₂ : List (ℤ × ℤ) :=
  [(-1, 0), (0, -1), (-1, -1), (-2, 0), (-2, 1), (-3, 1), (-3, 2), (-2, 2), (-3, 3), (-2, 3)]

theorem ex15Check : hbCheck ex13L₁ ex15L₂ (0, 2) (-2, 3) 1 = true := by decide +kernel

noncomputable def ex15 := hbArr ex15Check

theorem ex15_isRigid : ex15.IsRigid := hbArr_isRigid ex15Check

theorem ex15_not_isLattice : ¬ ex15.IsLattice :=
  hbArr_not_isLattice_of_turn ex15Check (k := 2) (by norm_num) (by decide) (by decide)
    (p := (0, 1)) (p' := (1, 0)) (by decide) (by decide) (by decide)
    (q := (-1, 0)) (q' := (0, -1)) (by decide) (by decide) (by decide)

/-- The hinge triangle of `ex15` passes both `ℤ × ℤ` tests: T1 and T2 cannot see that it is off
the lattice. -/
example : normTriangle 4 7 = true ∧ frameCompatible (0, 2) (-2, 3) = true := by decide

end RigidArrangements

#print axioms RigidArrangements.ex15_not_isLattice
#print axioms RigidArrangements.ex15_isRigid

/-! ===================== two bodies sharing two circles (Σ7) ===================== -/

namespace RigidArrangements

/-- **Two lattice bodies sharing two circles** (`n = 17`), rebuilt as hinge + bar: body 1 (8
circles) contains the hinge `0` and `u = (1, -3)` (`|u|² = 4·7`); body 2 (11 circles, the body of
`ex15`, mirrored) contains the hinge and a circle that lands exactly on `u`; here it is entered
without that circle, and the bar runs from `u` to its neighbour `v = (-3, 3)` (`N₂ = 9`,
`D = 27 = 3·3²`). The turn is the `Σ7` coincidence rotation; all coordinates lie in `ℚ(√3)`. -/
def ex17L₁ : List (ℤ × ℤ) := [(0, 0), (0, -1), (-1, 0), (-1, -1), (0, -2), (-1, -2), (0, -3), (1, -3)]
def ex17L₂ : List (ℤ × ℤ) :=
  [(-1, 0), (0, -1), (-1, -1), (-2, 0), (-2, 1), (-3, 1), (-3, 2), (-2, 2), (-3, 3)]

theorem ex17Check : hbCheck ex17L₁ ex17L₂ (1, -3) (-3, 3) 1 = true := by decide +kernel

noncomputable def ex17 := hbArr ex17Check

theorem ex17_isRigid : ex17.IsRigid := hbArr_isRigid ex17Check

theorem ex17_not_isLattice : ¬ ex17.IsLattice :=
  hbArr_not_isLattice_of_turn ex17Check (k := 3) (by norm_num) (by decide) (by decide)
    (p := (0, 0)) (p' := (0, -1)) (by decide) (by decide) (by decide)
    (q := (-1, 0)) (q' := (0, -1)) (by decide) (by decide) (by decide)

end RigidArrangements

#print axioms RigidArrangements.ex17_not_isLattice
#print axioms RigidArrangements.ex17_isRigid
