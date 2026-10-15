import RigidArrangements

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

#print axioms RigidArrangements.Arrangement.isLattice_iff_frameInv
#print axioms RigidArrangements.Arrangement.IsRigid.not_isLattice_iff
#print axioms RigidArrangements.Arrangement.o11_not_isLattice'
