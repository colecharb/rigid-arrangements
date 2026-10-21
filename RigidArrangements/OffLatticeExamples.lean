import RigidArrangements.Frame

/-!
# Certified off-lattice arrangements: the hinge-and-bar constructor

`RigidArrangements/OffLattice.lean` builds one off-lattice arrangement, `O11`, by hand. This
file turns that construction into a general one driven by a single decidable check, and uses it
for three further certified examples.

## The construction

Two lattice bodies, given as lists of lattice sites, are glued at a hinge and locked by a bar at
the exact angle the bar forces. Normalization: both bodies have their hinge at the lattice
origin `0`; body 1 is the list `l₁` (which contains `0`), body 2 is `0 :: l₂`. The bar runs from
`u ∈ l₁` to `v ∈ l₂`. Body 2 is turned about the hinge by the unit complex number
`hbAlpha u v σ`, where `σ = ±1` picks one of the two positions; to reflect body 2, pass its
mirror image `l₂.map econj`.

* `eis`, `eis_mul`, `eis_econj`: lattice sites are Eisenstein integers, with
  `latticePoint v = 2 * eis v`.
* `hbD`, `hbW`, `hbAlpha`: the discriminant `D = 4 N₁ N₂ - (N₁ + N₂ - 1)²` of the hinge triangle,
  the position of the far bar end, and the turn of body 2.
* `norm_hbAlpha`, `dist_bar`: the turn is a unit, and the bar has length exactly `2`.
* `dist_sq_cross`: every squared distance between the two bodies has the form `A + B √(3D)` with
  `A`, `B` rational and computable (`crossAB`), so
* `nonnegSqrt_sound`: a decidable sign test for `p + q √M` decides the no-overlap conditions.
* `hbCheck`, `hbArr`, `hbArr_isRigid`: if the decidable check passes, the placement really is an
  arrangement (no two circles overlap) and it is rigid, by the hinge-and-bar lemma
  (`Arrangement.IsRigid.of_hinge_of_union`).

## Showing that the result is off the lattice

Two criteria, both from `RigidArrangements/Frame.lean`:

* `hbArr_not_isLattice` uses T1: if no lattice triangle has side norms `eNorm u`, `eNorm v`, `1`,
  the hinge triangle itself is not a lattice triangle.
* `hbArr_not_isLattice_of_turn` uses the frame invariant directly: when `D = 3k²` the turn lies
  in `ℚ(ρ)`, where `α⁶ ≠ 1` becomes a decidable statement about Eisenstein integers. This covers
  the examples whose hinge triangle *is* a lattice triangle, which T1 cannot see.

## The examples

| name | `n` | bodies | status |
|---|---|---|---|
| `o11'` | 11 | two chevrons, hinge + bar, `D = 11` | `O11` rebuilt by the constructor |
| `ex13` | 13 | trapezoid + 9-circle body, `D = 15` | the core `Q13`; coordinates in `ℚ(√3, √5)` |
| `ex15` | 15 | trapezoid + 11-circle body, `D = 12 = 3·2²` | hinge triangle *is* a lattice triangle |
| `ex17` | 17 | 8- and 11-circle bodies, `D = 27 = 3·3²` | the double hinge `DH17`; the `Σ7` rotation |

Each comes with `_isRigid` and `_not_isLattice`. See `docs/offlattice.md` for the geometry and
for the names used there (`Q13`, `DH17`).
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

theorem conj_rho_eq_one_sub : conj rho = 1 - rho := by
  refine Complex.ext ?_ ?_
  · simp [rho_re]
    norm_num
  · simp [rho_im]

theorem eis_econj (a : ℤ × ℤ) : eis (econj a) = conj (eis a) := by
  simp only [eis, econj, map_add, map_mul, map_intCast, conj_rho_eq_one_sub]
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

theorem eNorm_pos {a : ℤ × ℤ} (h : a ≠ 0) : (0 : ℝ) < eNorm a := by
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
  have hN := eNorm_pos hu
  have key := hb_key hD hσ
  rw [Complex.normSq_apply]
  simp only [hbW]
  rw [show ((eNorm u + eNorm v - 1 : ℤ) : ℝ) / (2 * eNorm u) * (((eNorm u + eNorm v - 1 : ℤ) : ℝ) /
      (2 * eNorm u)) + σ * Real.sqrt (hbD u v) / (2 * eNorm u) *
      (σ * Real.sqrt (hbD u v) / (2 * eNorm u)) = (((eNorm u + eNorm v - 1 : ℤ) : ℝ) ^ 2 +
      (σ * Real.sqrt (hbD u v)) ^ 2) / (4 * (eNorm u) ^ 2) by ring, key]
  field_simp

theorem normSq_one_sub_hbW (hu : u ≠ 0) (hD : 0 ≤ hbD u v) (hσ : σ ^ 2 = 1) :
    Complex.normSq (1 - hbW u v σ) = 1 / eNorm u := by
  have hN := eNorm_pos hu
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
    rw [Complex.sq_norm, map_mul, normSq_eis, show Complex.normSq 2 = 4 by simp; norm_num]
  have hnt : ‖2 * eis t‖ ^ 2 = 4 * eNorm t := by
    rw [Complex.sq_norm, map_mul, normSq_eis, show Complex.normSq 2 = 4 by simp; norm_num]
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
    · rw [hs, latticePoint_zero, dist_comm, dist_zero_right,
        norm_mul, hα, one_mul, ← dist_zero_right,
        latticePoint_zero.symm, dist_comm]
      exact two_le_dist_latticePoint (hl₂0 _ (List.get_mem _ _)).symm
    · have hsep := h.sep _ (List.get_mem _ _) hs _ (List.get_mem l₂ j)
      have key := nonnegSqrt_sound (by nlinarith [h.hD]) hsep
      have hf := dist_sq_cross (σ := σ) h.hu0 h.v0 h.hD h.hσ (l₁.get i) (l₂.get j)
      push_cast at key
      have h4 : (4 : ℝ) ≤ dist (latticePoint (l₁.get i)) (hbAlpha u v σ * latticePoint (l₂.get j)) ^ 2 := by
        rw [hf]; linarith
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
    · change latticePoint (l₁.get a) = hbAlpha u v σ * latticePoint ((0 :: l₂).get 0)
      rw [ha]; simp [latticePoint_zero]
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
    change dist (latticePoint (l₁.get x)) (hbAlpha u v σ * latticePoint (l₂.get y)) = 2
    rw [hx, hy]
    exact dist_bar ok.hu0 ok.v0 ok.hD (by exact_mod_cast ok.hσ)
  refine IsLocallyRigid.of_hinge (f₁ := Sum.inl) (f₂ := f₂) hcover r₁ r₂ (a₁ := a) (a₂ := 0)
    rfl hbar ?_ ?_
  · change latticePoint (l₁.get a) ≠ latticePoint (l₁.get x)
    rw [ha, hx]
    exact latticePoint_injective.ne (Ne.symm ok.hu0)
  · change hbCenter l₁ l₂ u v σ (Sum.inl a) ≠ hbAlpha u v σ * latticePoint (l₂.get y)
    simp only [hbCenter, ha, hy, latticePoint_zero]
    intro e
    have : ‖hbAlpha u v σ * latticePoint v‖ = 0 := by rw [← e, norm_zero]
    rw [norm_mul, hα, one_mul, norm_eq_zero] at this
    exact latticePoint_injective.ne ok.v0 (this.trans latticePoint_zero.symm)

end Construction

/-! ## `O11` through the constructor -/

/-- The left chevron of `O11` with its hinge at `0`, and the mirror image of the right one. -/
def o11L₁ : List (ℤ × ℤ) := [(0, 0), (1, 0), (1, -1), (2, -1), (2, -2), (1, -2)]
def o11L₂ : List (ℤ × ℤ) := ((o11L₁.filter (· ≠ 0)).map econj)

theorem o11Check : hbCheck o11L₁ o11L₂ (1, -2) (econj (1, -2)) (-1) = true := by decide +kernel

/-- `O11`, rebuilt by the general constructor: two chevrons, hinge at `0`, bar from `(1, -2)` to
the mirror image of `(1, -2)` in body 2, `σ = -1`. All side conditions are kernel computations. -/
noncomputable def o11' := hbArr o11Check

theorem o11'_isRigid : o11'.IsRigid := hbArr_isRigid o11Check

/-! ## Off the lattice by the hinge triangle (T1) -/

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
  · change dist (latticePoint (l₁.get a)) (latticePoint (l₁.get x)) ^ 2 = _
    rw [ha, hx, dist_latticePoint_sq, zero_sub, eNorm_neg, cu]
  · change dist (latticePoint (l₁.get a)) (hbAlpha u v σ * latticePoint (l₂.get y)) ^ 2 = _
    rw [ha, hy, latticePoint_zero, dist_comm, dist_zero_right, norm_mul, ok.normα, one_mul,
      ← dist_zero_right, ← latticePoint_zero, dist_comm, dist_latticePoint_sq, zero_sub,
      eNorm_neg, cv]
  · change dist (latticePoint (l₁.get x)) (hbAlpha u v σ * latticePoint (l₂.get y)) = 2
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

/-! ## Off the lattice by the turn (`D = 3k²`) -/

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
    change dist (latticePoint (l₁.get ip)) (latticePoint (l₁.get ip')) = 2
    rw [hip, hip', tangent_latticePoint_iff, ← eNorm_neg, neg_sub, hpp]
  have t₂ : Tangent (hbArr h).center (Sum.inr iq) (Sum.inr iq') := by
    change dist (hbAlpha u v σ * latticePoint (l₂.get iq)) (hbAlpha u v σ * latticePoint (l₂.get iq')) = 2
    rw [hiq, hiq', dist_eq_norm, ← mul_sub, norm_mul, ok.normα, one_mul, ← dist_eq_norm,
      tangent_latticePoint_iff, ← eNorm_neg, neg_sub, hqq]
  refine Arrangement.not_isLattice_of_frameInv_ne t₁ t₂ ?_
  change (latticePoint (l₁.get ip') - latticePoint (l₁.get ip)) ^ 6 ≠
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

/-! ## Two bodies sharing two circles (the `Σ7` rotation) -/

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
