import RigidArrangements.Ring

/-!
# The three-body ring constructor, and `T14`

`RigidArrangements/OffLatticeExamples.lean` glues *two* lattice bodies at a hinge and locks them
with a bar; `RigidArrangements/Ring.lean` settles the arithmetic of a *ring*, three lattice
bodies pairwise sharing a hinge and locked by nothing else. This file builds the ring
constructor that arithmetic was for, and uses it for `T14`, the `14`-circle ring of
`docs/offlattice.md` §5 — the one headline off-lattice core that had never been in Lean.

## The construction

Normalization. Body `1` lives in the lattice frame; its hinge with body `2` is at the origin
`0` and its hinge with body `3` is at the lattice site `al`. Body `2` lives in its own lattice
frame with its hinge with body `1` at `0` and its hinge with body `3` at the site `p`. Body `3`
likewise has its hinge with body `1` at `0` and its hinge with body `2` at `q`. So the three
hinge norms of `Ring.lean` are read off the data:

`a = eNorm al`, `b = eNorm p`, `c = eNorm q`, and `D = ringD a b c`.

Body `2` is turned about the origin by `ringTurn₂` and body `3` is turned about `latticePoint al`
by `ringTurn₃`; both are units (`norm_ringTurn₂`, `norm_ringTurn₃`), and both carry the hinge
`H₂₃` to the *same* point, the apex `ringApex a b c σ al` of `Ring.lean`
(`ringTurn₂_mul_eis`, `ringTurn₃_hinge`). That single coincidence is the whole geometric content
of the ring: `normSq_ringApex` and `normSq_ringApex_sub` then say the hinge triangle has the
prescribed squared sides `4a`, `4b`, `4c` (`ringArr_hinge_dist₁₂`, `ringArr_hinge_dist₁₃`).

## One radical, by one decidable test

`Ring.lean` proves (`ringTau_mul_eis_re`, `conj_ringApex_mul`) that every squared distance in a
ring is `A + B √(3D)` with `A`, `B` rational. This file realizes that bound as an *exact
coordinate algebra* rather than one distance formula per pair of bodies. `RingNum` is the
`4`-dimensional `ℚ`-algebra

`base + sq3 · i√3 + sqD · i√D + sq3D · √(3D)`,

which is closed under multiplication (`RingNum.toC_mul`) and contains every centre of a ring:
lattice sites (`RingNum.eis`), the hinge parameter `τ` (`RingNum.tau`), hence the two turns.
Complex conjugation negates the two imaginary generators and fixes `√(3D)`, so

`normSq x = (base² + 3 sq3² + D sqD² + 3D sq3D²) + 2 (base · sq3D + sq3 · sqD) √(3D)`

(`RingNum.normSq_toC`) is automatically of the promised shape — for *every* pair of circles at once,
within a body or across any two bodies. A single `nonnegSqrt _ _ (3 * ringD a b c)` therefore
decides the whole no-overlap condition, exactly as `hbCheck` does for a hinge and a bar, and
`RingData.sepCheck` is that test over all pairs.

## The certificate

`RingData` carries the sites `al`, `p`, `q`, the three bodies' remaining sites `r₁`, `r₂`, `r₃`,
a build order `m₁`, `m₂`, `m₃` for each body and the branch `σ = ±1`. `RingData.Check` is
decidable: the hinge norms are positive, `D ≥ 0`, `σ² = 1`, each `m` is a `Nodup` permutation of
its body with a build certificate (`latticeBuilt`), and no two circles overlap. The build order
is given separately because the two hinges of a body are in general *not* tangent, so a body's
canonical listing — hinges first — is never itself a build order.

`ringArr` is the arrangement, `ringArr_isRigid` its rigidity: three clusters, each a rigid
lattice body fed in by `Arrangement.rigidIn_of_comap`, pairwise sharing the three distinct
hinges, merged by a single application of **R2**
(`Arrangement.RigidIn.union_of_ring`) and cashed in by `Arrangement.rigidIn_univ_iff`. No
non-degeneracy of the hinge triangle is used anywhere, in line with R2.

`ringArr_not_isLattice` is the frame-invariant test: body `1` and body `2` each contain a
contact, and if `turn₂ ^ 6 ≠ 1` those two contacts point in directions differing by a
non-multiple of `60°`. Here `turn₂ ^ 6` is computed *exactly* in `RingNum`, so the test is the
decidable pair of conditions "the `√(3D)` part of `turn₂ ^ 6` vanishes and its rational part is
not `1`" — which is a statement about the real part alone, and so needs no irrationality
argument.

## `T14`

`t14Data` is `T14`: hinge norms `(a, b, c) = (3, 4, 3)`, `D = 32`, `σ = 1`, bodies a `6`-circle
chevron, a `5`-circle trapezoid and a `6`-circle chevron, `6 + 5 + 6 - 3 = 14` circles. The
turn of body `2` is `(√6 - i√3)/3`, whose sixth power is `(-69 + 30 i√2)/81`: its real part is
`-23/27`, so `T14` is off the lattice (`t14_not_isLattice`). Every one of the `91` squared
distances lies in `ℚ(√96) = ℚ(√6)` and is at least `4`, which `t14Check` decides in the kernel.

`T14` is the first certified example here for which the hinge-triangle route of
`hbArr_not_isLattice` is simply unavailable. That lemma reads the test T1 off the triangle
hinge–bar, one of whose sides is the *bar*, a contact; a ring has no bar, and `T14`'s hinge
triangle has squared sides `12`, `16`, `12` (`t14_hinge_dists`), no side of length `2`. Its
three bodies are isostatic, with `9 + 7 + 9 = 18/2 + 14/2 + 18/2` contacts
(`t14_body_contacts`), already the `25 = 2 · 14 - 3` contacts `docs/offlattice.md` records, so
no contact joins two bodies [computed-exact, not in Lean: ruling out a *cross-body* contact at
squared distance `4 + B √96` with `B ≠ 0` needs the irrationality of `√96`, which this file
does not prove]. What betrays `T14` is the relative turn of two bodies alone.

## Main results

* `RingNum`, `RingNum.mul`, `RingNum.normSq`, `RingNum.toC`, `RingNum.toC_mul`,
  `RingNum.normSq_toC`, `RingNum.two_le_dist_toC`.
* `ringTurn₂`, `ringTurn₃`, `norm_ringTurn₂`, `norm_ringTurn₃`, `ringTurn₂_mul_eis`,
  `ringTurn₃_hinge`.
* `RingData`, `RingData.Check`, `RingOk`, `ringArr`, `ringArr_isRigid`,
  `ringArr_hinge_dist₁₂`, `ringArr_hinge_dist₁₃`, `ringArr_not_isLattice`.
* `t14Data`, `t14Check`, `t14`, `t14_isRigid`, `t14_card`, `t14_body_contacts`,
  `t14_hinge_dists`, `t14_not_isLattice`, `t14Data_ringD`.
-/

open ComplexConjugate

namespace RigidArrangements

/-! ## Eisenstein norms are multiplicative -/

/-- Conjugation in `ℤ[ρ]` preserves the norm. -/
theorem eNorm_econj (x : ℤ × ℤ) : eNorm (econj x) = eNorm x := by
  simp only [eNorm, econj]; ring

/-- The Eisenstein norm is multiplicative, since it is `|·|²` of a product
(`eis_mul`, `normSq_eis`). -/
theorem eNorm_emul (x y : ℤ × ℤ) : eNorm (emul x y) = eNorm x * eNorm y := by
  simp only [eNorm, emul]; ring

/-! ## The coordinate algebra of a ring -/

/-- **A ring coordinate.** The number `base + sq3 · i√3 + sqD · i√D + sq3D · √(3D)`, where `D`
is the ring discriminant `ringD a b c`. Lattice sites (`RingNum.eis`), the hinge parameter `ringTau`
(`RingNum.tau`) and both turns of a ring live here, and the algebra is closed under multiplication
(`RingNum.mul`, `RingNum.toC_mul`): the only products that could leave it, `i√3 · i√D` and
`(√(3D))²`, land on `√(3D)` and on the rationals.

Nothing is claimed about the four generators being independent over `ℚ` — they are not, for
instance when `D = 3k²` — and nothing needs to be: the interpretation `RingNum.toC` is a ring
homomorphism either way, which is all a certificate uses. -/
structure RingNum where
  /-- The rational part. -/
  base : ℚ
  /-- The coefficient of `i√3`. -/
  sq3 : ℚ
  /-- The coefficient of `i√D`. -/
  sqD : ℚ
  /-- The coefficient of `√(3D)`. -/
  sq3D : ℚ
deriving DecidableEq

namespace RingNum

/-- Addition of ring coordinates. -/
def add (x y : RingNum) : RingNum :=
  ⟨x.base + y.base, x.sq3 + y.sq3, x.sqD + y.sqD, x.sq3D + y.sq3D⟩

/-- Subtraction of ring coordinates. -/
def sub (x y : RingNum) : RingNum :=
  ⟨x.base - y.base, x.sq3 - y.sq3, x.sqD - y.sqD, x.sq3D - y.sq3D⟩

/-- Multiplication of ring coordinates, from `(i√3)² = -3`, `(i√D)² = -D`,
`i√3 · i√D = -√(3D)`, `i√3 · √(3D) = 3 i√D`, `i√D · √(3D) = D i√3` and `(√(3D))² = 3D`. -/
def mul (D : ℤ) (x y : RingNum) : RingNum :=
  ⟨x.base * y.base - 3 * x.sq3 * y.sq3 - (D : ℚ) * x.sqD * y.sqD + 3 * (D : ℚ) * x.sq3D * y.sq3D,
   x.base * y.sq3 + x.sq3 * y.base + (D : ℚ) * (x.sqD * y.sq3D + x.sq3D * y.sqD),
   x.base * y.sqD + x.sqD * y.base + 3 * (x.sq3 * y.sq3D + x.sq3D * y.sq3),
   x.base * y.sq3D + x.sq3D * y.base - (x.sq3 * y.sqD + x.sqD * y.sq3)⟩

/-- A rational multiple of a ring coordinate. -/
def smul (t : ℚ) (x : RingNum) : RingNum := ⟨t * x.base, t * x.sq3, t * x.sqD, t * x.sq3D⟩

/-- Powers of a ring coordinate. -/
def pow (D : ℤ) (x : RingNum) : ℕ → RingNum
  | 0 => ⟨1, 0, 0, 0⟩
  | n + 1 => mul D (pow D x n) x

/-- **The squared modulus of a ring coordinate**, as the pair `(A, B)` with `|x|² = A + B √(3D)`.
Complex conjugation negates `i√3` and `i√D` and fixes `√(3D)`, so the two imaginary generators
cancel in `x · conj x` and only the rationals and `√(3D)` survive: this is why one radical
suffices for every squared distance in a ring. -/
def normSq (D : ℤ) (x : RingNum) : ℚ × ℚ :=
  (x.base ^ 2 + 3 * x.sq3 ^ 2 + (D : ℚ) * x.sqD ^ 2 + 3 * (D : ℚ) * x.sq3D ^ 2,
   2 * (x.base * x.sq3D + x.sq3 * x.sqD))

/-- The lattice site `z`, as a ring coordinate: `z.1 + z.2 ρ = (z.1 + z.2/2) + (z.2/2) i√3`. -/
def eis (z : ℤ × ℤ) : RingNum := ⟨(z.1 : ℚ) + (z.2 : ℚ) / 2, (z.2 : ℚ) / 2, 0, 0⟩

/-- The hinge parameter `ringTau a b c σ = ((a+b-c) + σ i√D)/2`, as a ring coordinate. -/
def tau (a b c σ : ℤ) : RingNum := ⟨((a + b - c : ℤ) : ℚ) / 2, 0, (σ : ℚ) / 2, 0⟩

/-- **The interpretation** of a ring coordinate as a point of the plane. -/
noncomputable def toC (D : ℤ) (x : RingNum) : ℂ :=
  ⟨(x.base : ℝ) + (x.sq3D : ℝ) * Real.sqrt ((3 * D : ℤ) : ℝ),
   (x.sq3 : ℝ) * Real.sqrt 3 + (x.sqD : ℝ) * Real.sqrt ((D : ℤ) : ℝ)⟩

@[simp] theorem toC_re (D : ℤ) (x : RingNum) :
    (toC D x).re = (x.base : ℝ) + (x.sq3D : ℝ) * Real.sqrt ((3 * D : ℤ) : ℝ) := rfl

@[simp] theorem toC_im (D : ℤ) (x : RingNum) :
    (toC D x).im = (x.sq3 : ℝ) * Real.sqrt 3 + (x.sqD : ℝ) * Real.sqrt ((D : ℤ) : ℝ) := rfl

section Interpretation

variable {D : ℤ} (x y : RingNum)

private theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem sqrtD_sq (hD : 0 ≤ D) : Real.sqrt ((D : ℤ) : ℝ) ^ 2 = ((D : ℤ) : ℝ) :=
  Real.sq_sqrt (by exact_mod_cast hD)

private theorem sqrt3D_eq :
    Real.sqrt ((3 * D : ℤ) : ℝ) = Real.sqrt 3 * Real.sqrt ((D : ℤ) : ℝ) := by
  push_cast
  exact Real.sqrt_mul (by norm_num) _

theorem toC_add : toC D (add x y) = toC D x + toC D y := by
  refine Complex.ext ?_ ?_ <;> simp only [toC_re, toC_im, Complex.add_re, Complex.add_im, add] <;>
    push_cast <;> ring

theorem toC_sub : toC D (sub x y) = toC D x - toC D y := by
  refine Complex.ext ?_ ?_ <;> simp only [toC_re, toC_im, Complex.sub_re, Complex.sub_im, sub] <;>
    push_cast <;> ring

theorem toC_smul (t : ℚ) : toC D (smul t x) = (t : ℂ) * toC D x := by
  refine Complex.ext ?_ ?_ <;>
    simp only [toC_re, toC_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, smul] <;>
    push_cast <;> ring

/-- **The interpretation is multiplicative**: the four generators really do close up. -/
theorem toC_mul (hD : 0 ≤ D) : toC D (mul D x y) = toC D x * toC D y := by
  have h3 := sqrt3_sq
  have hd := sqrtD_sq hD
  refine Complex.ext ?_ ?_
  · simp only [toC_re, toC_im, Complex.mul_re, mul, sqrt3D_eq]
    push_cast
    linear_combination ((x.sq3 : ℝ) * y.sq3 -
        (x.sq3D : ℝ) * y.sq3D * Real.sqrt ((D : ℤ) : ℝ) ^ 2) * h3 +
      ((x.sqD : ℝ) * y.sqD - 3 * (x.sq3D : ℝ) * y.sq3D) * hd
  · simp only [toC_re, toC_im, Complex.mul_im, mul, sqrt3D_eq]
    push_cast
    linear_combination
      (-((x.sq3 : ℝ) * y.sq3D + (x.sq3D : ℝ) * y.sq3) * Real.sqrt ((D : ℤ) : ℝ)) * h3 +
      (-((x.sqD : ℝ) * y.sq3D + (x.sq3D : ℝ) * y.sqD) * Real.sqrt 3) * hd

theorem toC_one : toC D ⟨1, 0, 0, 0⟩ = 1 := by
  refine Complex.ext ?_ ?_ <;> simp

theorem toC_pow (hD : 0 ≤ D) (n : ℕ) : toC D (pow D x n) = toC D x ^ n := by
  induction n with
  | zero =>
      change toC D ⟨1, 0, 0, 0⟩ = toC D x ^ 0
      rw [pow_zero]
      exact toC_one
  | succ n ih =>
      change toC D (mul D (pow D x n) x) = _
      rw [toC_mul _ _ hD, ih, pow_succ]

/-- **Every squared modulus is `A + B √(3D)`**, with `A`, `B` rational and computable. -/
theorem normSq_toC (hD : 0 ≤ D) :
    Complex.normSq (toC D x) =
      ((normSq D x).1 : ℝ) + ((normSq D x).2 : ℝ) * Real.sqrt ((3 * D : ℤ) : ℝ) := by
  have h3 := sqrt3_sq
  have hd := sqrtD_sq hD
  simp only [Complex.normSq_apply, toC_re, toC_im, normSq, sqrt3D_eq]
  push_cast
  linear_combination
    ((x.sq3D : ℝ) ^ 2 * Real.sqrt ((D : ℤ) : ℝ) ^ 2 + (x.sq3 : ℝ) ^ 2) * h3 +
    (3 * (x.sq3D : ℝ) ^ 2 + (x.sqD : ℝ) ^ 2) * hd

/-- The squared distance between two ring coordinates, in the same form. -/
theorem dist_sq_toC (hD : 0 ≤ D) :
    dist (toC D x) (toC D y) ^ 2 =
      ((normSq D (sub x y)).1 : ℝ) + ((normSq D (sub x y)).2 : ℝ) *
        Real.sqrt ((3 * D : ℤ) : ℝ) := by
  rw [dist_eq_norm, ← toC_sub, Complex.sq_norm, normSq_toC _ hD]

/-- **The no-overlap test.** If the decidable sign test passes for the pair `(x, y)`, the two
circles are at least `2` apart. -/
theorem two_le_dist_toC (hD : 0 ≤ D)
    (h : nonnegSqrt ((normSq D (sub x y)).1 - 4) (normSq D (sub x y)).2 (3 * D) = true) :
    2 ≤ dist (toC D x) (toC D y) := by
  have key := nonnegSqrt_sound (by linarith : (0 : ℤ) ≤ 3 * D) h
  have hf := dist_sq_toC x y hD
  have hc : (((normSq D (sub x y)).1 - 4 : ℚ) : ℝ) = ((normSq D (sub x y)).1 : ℝ) - 4 := by
    push_cast; ring
  rw [hc] at key
  have h4 : (4 : ℝ) ≤ dist (toC D x) (toC D y) ^ 2 := by rw [hf]; linarith
  nlinarith [dist_nonneg (x := toC D x) (y := toC D y)]

/-- A lattice site, interpreted. -/
theorem toC_eis (z : ℤ × ℤ) : toC D (eis z) = RigidArrangements.eis z := by
  refine Complex.ext ?_ ?_ <;>
    simp only [toC_re, toC_im, eis, eis_re, eis_im] <;> push_cast <;> ring

/-- A lattice site, interpreted at twice the scale: `latticePoint z = 2 · eis z`. -/
theorem toC_smul_two_eis (z : ℤ × ℤ) : toC D (smul 2 (eis z)) = latticePoint z := by
  rw [toC_smul, toC_eis, latticePoint_eq_eis]
  push_cast
  ring

/-- The hinge parameter, interpreted. -/
theorem toC_tau (a b c σ : ℤ) :
    toC (ringD a b c) (tau a b c σ) = ringTau a b c ((σ : ℤ) : ℝ) := by
  refine Complex.ext ?_ ?_ <;> simp only [toC_re, toC_im, tau, ringTau_re, ringTau_im] <;>
    push_cast <;> ring

end Interpretation

end RingNum

/-! ## The two turns of a ring -/

section Turns

variable {al p q : ℤ × ℤ} {σ : ℝ}

/-- **The turn of body 2**, which carries body 2's frame to its place in body 1's frame. It is
the ring analogue of `hbAlpha`: the hinge `H₂₃` sits at `ringApex a b c σ al` in body 1's frame
and at the site `p` in body 2's, so the turn is `ringApex / eis p`, rationalized. -/
noncomputable def ringTurn₂ (al p q : ℤ × ℤ) (σ : ℝ) : ℂ :=
  ringTau (eNorm al) (eNorm p) (eNorm q) σ * eis (emul al (econj p)) /
    ((eNorm al * eNorm p : ℤ) : ℂ)

/-- **The turn of body 3**, which carries body 3's frame to its place in body 1's frame. Body 3
is turned about `latticePoint al`, the hinge `H₁₃`: the hinge `H₂₃` sits at
`ringApex a b c σ al - eis al` relative to that centre and at the site `q` in body 3's frame. -/
noncomputable def ringTurn₃ (al p q : ℤ × ℤ) (σ : ℝ) : ℂ :=
  (ringTau (eNorm al) (eNorm p) (eNorm q) σ - ((eNorm al : ℤ) : ℂ)) * eis (emul al (econj q)) /
    ((eNorm al * eNorm q : ℤ) : ℂ)

private theorem eNorm_cast_ne_zero {v : ℤ × ℤ} (h : v ≠ 0) : ((eNorm v : ℤ) : ℂ) ≠ 0 := by
  refine Int.cast_ne_zero.mpr fun h0 => h ?_
  exact (eNorm_eq_zero_iff v).1 h0

private theorem conj_eis_mul_eis (v : ℤ × ℤ) : conj (eis v) * eis v = ((eNorm v : ℤ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, normSq_eis]
  push_cast
  rfl

/-- **The turn of body 2 is a rotation**: `‖turn₂‖ = 1`, since `|τ|² = a b` (`normSq_ringTau`)
and `eNorm (emul al (econj p)) = a b`. -/
theorem norm_ringTurn₂ (hal : al ≠ 0) (hp : p ≠ 0)
    (hD : 0 ≤ ringD (eNorm al) (eNorm p) (eNorm q)) (hσ : σ ^ 2 = 1) :
    ‖ringTurn₂ al p q σ‖ = 1 := by
  have hA : (0 : ℝ) < eNorm al := eNorm_pos hal
  have hB : (0 : ℝ) < eNorm p := eNorm_pos hp
  have h2 : Complex.normSq (ringTurn₂ al p q σ) = 1 := by
    simp only [ringTurn₂, map_div₀, map_mul, normSq_eis, normSq_ringTau hD hσ,
      Complex.normSq_intCast, eNorm_emul, eNorm_econj]
    push_cast
    field_simp
  rw [Complex.norm_def, h2, Real.sqrt_one]

/-- **The turn of body 3 is a rotation**: `‖turn₃‖ = 1`, since `|τ - a|² = a c`
(`normSq_ringTau_sub`) and `eNorm (emul al (econj q)) = a c`. -/
theorem norm_ringTurn₃ (hal : al ≠ 0) (hq : q ≠ 0)
    (hD : 0 ≤ ringD (eNorm al) (eNorm p) (eNorm q)) (hσ : σ ^ 2 = 1) :
    ‖ringTurn₃ al p q σ‖ = 1 := by
  have hA : (0 : ℝ) < eNorm al := eNorm_pos hal
  have hC : (0 : ℝ) < eNorm q := eNorm_pos hq
  have h2 : Complex.normSq (ringTurn₃ al p q σ) = 1 := by
    simp only [ringTurn₃, map_div₀, map_mul, normSq_eis, normSq_ringTau_sub hD hσ,
      Complex.normSq_intCast, eNorm_emul, eNorm_econj]
    push_cast
    field_simp
  rw [Complex.norm_def, h2, Real.sqrt_one]

/-- **Body 2 puts the hinge `H₂₃` at the apex.** -/
theorem ringTurn₂_mul_eis (hal : al ≠ 0) (hp : p ≠ 0) :
    ringTurn₂ al p q σ * eis p = ringApex (eNorm al) (eNorm p) (eNorm q) σ al := by
  have ha := eNorm_cast_ne_zero hal
  have hb := eNorm_cast_ne_zero hp
  have key := conj_eis_mul_eis p
  have hcast : ((eNorm al * eNorm p : ℤ) : ℂ) = ((eNorm al : ℤ) : ℂ) * ((eNorm p : ℤ) : ℂ) := by
    push_cast; ring
  simp only [ringTurn₂, ringApex, eis_mul, eis_econj, hcast]
  rw [show ringTau (eNorm al) (eNorm p) (eNorm q) σ * (eis al * conj (eis p)) /
        (((eNorm al : ℤ) : ℂ) * ((eNorm p : ℤ) : ℂ)) * eis p =
      ringTau (eNorm al) (eNorm p) (eNorm q) σ * eis al * (conj (eis p) * eis p) /
        (((eNorm al : ℤ) : ℂ) * ((eNorm p : ℤ) : ℂ)) by ring, key]
  field_simp

/-- **Body 3 puts the hinge `H₂₃` at the same apex.** This is the one coincidence the ring
construction rests on; the rest of the file is bookkeeping. -/
theorem ringTurn₃_hinge (hal : al ≠ 0) (hq : q ≠ 0) :
    eis al + ringTurn₃ al p q σ * eis q = ringApex (eNorm al) (eNorm p) (eNorm q) σ al := by
  have ha := eNorm_cast_ne_zero hal
  have hc := eNorm_cast_ne_zero hq
  have key := conj_eis_mul_eis q
  have hcast : ((eNorm al * eNorm q : ℤ) : ℂ) = ((eNorm al : ℤ) : ℂ) * ((eNorm q : ℤ) : ℂ) := by
    push_cast; ring
  simp only [ringTurn₃, ringApex, eis_mul, eis_econj, hcast]
  rw [show (ringTau (eNorm al) (eNorm p) (eNorm q) σ - ((eNorm al : ℤ) : ℂ)) *
        (eis al * conj (eis q)) / (((eNorm al : ℤ) : ℂ) * ((eNorm q : ℤ) : ℂ)) * eis q =
      (ringTau (eNorm al) (eNorm p) (eNorm q) σ - ((eNorm al : ℤ) : ℂ)) * eis al *
        (conj (eis q) * eis q) / (((eNorm al : ℤ) : ℂ) * ((eNorm q : ℤ) : ℂ)) by ring, key]
  field_simp
  ring

end Turns

/-! ## Rigidity of a turned lattice body -/

/-- **A turned lattice body is rigid.** If the sites `B` carry a build certificate in *some*
order `m`, then the placement `o + γ · latticePoint ·` of `B` by a unit `γ` and a translation `o`
is locally rigid. The build order is separate from the listing because a body of a ring has its
two hinges listed first, and those are in general not tangent. -/
theorem isLocallyRigid_of_turn {B m : List (ℤ × ℤ)} (hm : m.Nodup) (hlen : m.length = B.length)
    (hmem : ∀ v ∈ m, v ∈ B) (hb : latticeBuilt m = true) {γ o : ℂ} (hγ : ‖γ‖ = 1)
    {P : Fin B.length → Plane} (hP : ∀ i, P i = o + γ * latticePoint (B.get i)) :
    IsLocallyRigid P := by
  obtain ⟨hB, hiso⟩ := Arrangement.iso_ofLattice_of_map hm id (fun _ _ => rfl) hlen hmem
  have hr : (Arrangement.ofLattice B hB).IsRigid :=
    hiso.isRigid (Arrangement.isRigid_ofLattice_of_latticeBuilt hm hb)
  have hc : Congruent P (Arrangement.ofLattice B hB).center := by
    rw [congruent_iff_dist_eq]
    intro i j
    change dist (P i) (P j) = dist (latticePoint (B.get i)) (latticePoint (B.get j))
    rw [hP, hP, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hγ,
      one_mul]
  exact (isLocallyRigid_iff_of_congruent hc).2 hr

/-! ## The certificate -/

/-- **The data of a ring.** Three lattice bodies pairwise sharing a hinge.

* body 1 is listed as `0 :: al :: r₁`: its hinge with body 2 at the lattice origin, its hinge
  with body 3 at `al`, then its remaining sites;
* body 2 is listed as `0 :: p :: r₂` in its own frame, its hinge with body 1 at the origin and
  its hinge with body 3 at `p`;
* body 3 is listed as `0 :: q :: r₃` in its own frame, its hinge with body 1 at the origin and
  its hinge with body 2 at `q`;
* `m₁`, `m₂`, `m₃` are the same three bodies in build order;
* `sg = ±1` chooses which side of the line `H₁₂ H₁₃` the third hinge lies on.

The circles of the arrangement are body 1's, then body 2's other than its hinge with body 1,
then body 3's other than *both* its hinges: `(r₁.length + 2) + (r₂.length + 1) + r₃.length`
in all. -/
structure RingData where
  /-- Body 1's hinge with body 3, in body 1's frame. -/
  al : ℤ × ℤ
  /-- Body 2's hinge with body 3, in body 2's frame. -/
  p : ℤ × ℤ
  /-- Body 3's hinge with body 2, in body 3's frame. -/
  q : ℤ × ℤ
  /-- Body 1's sites other than its two hinges. -/
  r₁ : List (ℤ × ℤ)
  /-- Body 2's sites other than its two hinges. -/
  r₂ : List (ℤ × ℤ)
  /-- Body 3's sites other than its two hinges. -/
  r₃ : List (ℤ × ℤ)
  /-- Body 1 in build order. -/
  m₁ : List (ℤ × ℤ)
  /-- Body 2 in build order. -/
  m₂ : List (ℤ × ℤ)
  /-- Body 3 in build order. -/
  m₃ : List (ℤ × ℤ)
  /-- The branch `±1`. -/
  sg : ℤ

/-- **The body check**: `m` is a build order for the body listed as `B`. -/
def bodyCheck (B m : List (ℤ × ℤ)) : Bool :=
  m.Nodup && (m.length = B.length) && m.all (· ∈ B) && latticeBuilt m

/-- Unpacking `bodyCheck`. -/
structure BodyOk (B m : List (ℤ × ℤ)) : Prop where
  /-- The build order has no repeats. -/
  nd : m.Nodup
  /-- It has as many sites as the body. -/
  len : m.length = B.length
  /-- Its sites are the body's sites. -/
  mem : ∀ v ∈ m, v ∈ B
  /-- It is a build order. -/
  built : latticeBuilt m = true

theorem BodyOk.of_check {B m : List (ℤ × ℤ)} (h : bodyCheck B m = true) : BodyOk B m := by
  simp only [bodyCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, fun v hv => by simpa using h.1.2 v hv, h.2⟩

/-- **A turned lattice body of a ring is rigid.** -/
theorem isLocallyRigid_of_bodyOk {B m : List (ℤ × ℤ)} (h : BodyOk B m) {γ o : ℂ} (hγ : ‖γ‖ = 1)
    {P : Fin B.length → Plane} (hP : ∀ i, P i = o + γ * latticePoint (B.get i)) :
    IsLocallyRigid P :=
  isLocallyRigid_of_turn h.nd h.len h.mem h.built hγ hP

namespace RingData

variable (d : RingData)

/-- The first hinge norm, `|H₁₂ H₁₃|² / 4`. -/
abbrev a : ℤ := eNorm d.al

/-- The second hinge norm, `|H₁₂ H₂₃|² / 4`. -/
abbrev b : ℤ := eNorm d.p

/-- The third hinge norm, `|H₁₃ H₂₃|² / 4`. -/
abbrev c : ℤ := eNorm d.q

/-- The ring discriminant, sixteen times the squared area of the hinge triangle. -/
abbrev D : ℤ := ringD d.a d.b d.c

/-- Body 1, listed with its two hinges first. -/
abbrev B₁ : List (ℤ × ℤ) := (0 : ℤ × ℤ) :: d.al :: d.r₁

/-- Body 2's own circles: its hinge with body 3, then its private sites. -/
abbrev L₂ : List (ℤ × ℤ) := d.p :: d.r₂

/-- Body 2, listed with its two hinges first. -/
abbrev B₂ : List (ℤ × ℤ) := (0 : ℤ × ℤ) :: d.L₂

/-- Body 3, listed with its two hinges first. -/
abbrev B₃ : List (ℤ × ℤ) := (0 : ℤ × ℤ) :: d.q :: d.r₃

/-- The circles of the ring: body 1, body 2 without its hinge with body 1, body 3 without both
of its hinges. -/
abbrev Idx : Type := Fin d.B₁.length ⊕ Fin d.L₂.length ⊕ Fin d.r₃.length

/-- The turn of body 2. -/
noncomputable abbrev turn₂ : ℂ := ringTurn₂ d.al d.p d.q (d.sg : ℝ)

/-- The turn of body 3. -/
noncomputable abbrev turn₃ : ℂ := ringTurn₃ d.al d.p d.q (d.sg : ℝ)

/-- **The centres of the ring.** Body 1 sits on the lattice; body 2 is turned about the hinge at
the origin; body 3 is turned about the hinge at `latticePoint al`. -/
noncomputable def center : d.Idx → Plane
  | .inl i => latticePoint (d.B₁.get i)
  | .inr (.inl j) => d.turn₂ * latticePoint (d.L₂.get j)
  | .inr (.inr k) => latticePoint d.al + d.turn₃ * latticePoint (d.r₃.get k)

/-- The turn of body 2, as a ring coordinate. -/
def turn₂Q : RingNum :=
  RingNum.smul (1 / ((d.a : ℚ) * (d.b : ℚ)))
    (RingNum.mul d.D (RingNum.tau d.a d.b d.c d.sg) (RingNum.eis (emul d.al (econj d.p))))

/-- The turn of body 3, as a ring coordinate. -/
def turn₃Q : RingNum :=
  RingNum.smul (1 / ((d.a : ℚ) * (d.c : ℚ)))
    (RingNum.mul d.D (RingNum.sub (RingNum.tau d.a d.b d.c d.sg) ⟨(d.a : ℚ), 0, 0, 0⟩)
      (RingNum.eis (emul d.al (econj d.q))))

/-- **The centres of the ring, as ring coordinates**: exact, computable, and in a single
`ℚ`-algebra for all three bodies at once. -/
def centerQ : d.Idx → RingNum
  | .inl i => RingNum.smul 2 (RingNum.eis (d.B₁.get i))
  | .inr (.inl j) =>
      RingNum.smul 2 (RingNum.mul d.D d.turn₂Q (RingNum.eis (d.L₂.get j)))
  | .inr (.inr k) =>
      RingNum.smul 2 (RingNum.add (RingNum.eis d.al)
        (RingNum.mul d.D d.turn₃Q (RingNum.eis (d.r₃.get k))))

/-- All the circles of the ring, as a list. -/
def idxList : List d.Idx :=
  (List.finRange d.B₁.length).map Sum.inl ++
    ((List.finRange d.L₂.length).map (fun j => Sum.inr (Sum.inl j)) ++
      (List.finRange d.r₃.length).map (fun k => Sum.inr (Sum.inr k)))

theorem mem_idxList (i : d.Idx) : i ∈ d.idxList := by
  rcases i with i | j | k
  · exact List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
  · exact List.mem_append_right _
      (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩))
  · exact List.mem_append_right _
      (List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩))

/-- **The separation test for one pair of circles**: `|c i - c j|² ≥ 4`, decided exactly by a
single `nonnegSqrt` over `3D`. -/
def sepPair (i j : d.Idx) : Bool :=
  nonnegSqrt ((RingNum.normSq d.D (RingNum.sub (d.centerQ i) (d.centerQ j))).1 - 4)
    (RingNum.normSq d.D (RingNum.sub (d.centerQ i) (d.centerQ j))).2 (3 * d.D)

/-- **The no-overlap test**, over every pair of circles of the ring: within a body, or across
any two of the three. One radical decides them all. -/
def sepCheck : Bool :=
  d.idxList.all fun i => d.idxList.all fun j => (i == j) || d.sepPair i j

/-- The numeric side conditions: the three hinge norms are positive, the hinge triangle closes,
and `σ = ±1`. -/
def numCheck : Bool :=
  (0 < d.a) && (0 < d.b) && (0 < d.c) && (0 ≤ d.D) && (d.sg ^ 2 = 1)

/-- **The decidable validity test for a ring.** -/
def Check : Bool :=
  d.numCheck && bodyCheck d.B₁ d.m₁ && bodyCheck d.B₂ d.m₂ && bodyCheck d.B₃ d.m₃ && d.sepCheck

end RingData

/-- Unpacking `RingData.Check`. -/
structure RingOk (d : RingData) : Prop where
  /-- `a > 0`, i.e. `al ≠ 0`. -/
  ha : 0 < d.a
  /-- `b > 0`, i.e. `p ≠ 0`. -/
  hb : 0 < d.b
  /-- `c > 0`, i.e. `q ≠ 0`. -/
  hc : 0 < d.c
  /-- The hinge triangle closes. -/
  hD : 0 ≤ d.D
  /-- The branch is `±1`. -/
  hsg : d.sg ^ 2 = 1
  /-- Body 1 is a lattice body with a build certificate. -/
  b₁ : BodyOk d.B₁ d.m₁
  /-- Body 2 is a lattice body with a build certificate. -/
  b₂ : BodyOk d.B₂ d.m₂
  /-- Body 3 is a lattice body with a build certificate. -/
  b₃ : BodyOk d.B₃ d.m₃
  /-- No two circles overlap. -/
  sep : ∀ i j : d.Idx, i ≠ j → d.sepPair i j = true

namespace RingOk

variable {d : RingData}

theorem of_check (h : d.Check = true) : RingOk d := by
  simp only [RingData.Check, RingData.numCheck, RingData.sepCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hn, h1⟩, h2⟩, h3⟩, hs⟩ := h
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hD⟩, hsg⟩ := hn
  refine ⟨ha, hb, hc, hD, hsg, BodyOk.of_check h1, BodyOk.of_check h2, BodyOk.of_check h3,
    fun i j hij => ?_⟩
  rcases hs i (d.mem_idxList i) j (d.mem_idxList j) with h | h
  · exact absurd h hij
  · exact h

theorem al_ne_zero (h : RingOk d) : d.al ≠ 0 := fun h0 => by
  have := h.ha
  rw [show d.a = eNorm d.al from rfl, h0] at this
  simp [eNorm] at this

theorem p_ne_zero (h : RingOk d) : d.p ≠ 0 := fun h0 => by
  have := h.hb
  rw [show d.b = eNorm d.p from rfl, h0] at this
  simp [eNorm] at this

theorem q_ne_zero (h : RingOk d) : d.q ≠ 0 := fun h0 => by
  have := h.hc
  rw [show d.c = eNorm d.q from rfl, h0] at this
  simp [eNorm] at this

theorem sg_sq (h : RingOk d) : ((d.sg : ℝ)) ^ 2 = 1 := by exact_mod_cast h.hsg

theorem norm_turn₂ (h : RingOk d) : ‖d.turn₂‖ = 1 :=
  norm_ringTurn₂ h.al_ne_zero h.p_ne_zero h.hD h.sg_sq

theorem norm_turn₃ (h : RingOk d) : ‖d.turn₃‖ = 1 :=
  norm_ringTurn₃ h.al_ne_zero h.q_ne_zero h.hD h.sg_sq

/-- **The two turns agree on the shared hinge**: body 2's circle at `p` and body 3's circle at
`q` are the same point of the plane, twice the apex of `Ring.lean`. -/
theorem hinge_eq (h : RingOk d) :
    d.turn₂ * latticePoint d.p = latticePoint d.al + d.turn₃ * latticePoint d.q := by
  rw [latticePoint_eq_eis, latticePoint_eq_eis, latticePoint_eq_eis,
    show d.turn₂ * (2 * eis d.p) = 2 * (d.turn₂ * eis d.p) by ring,
    show 2 * eis d.al + d.turn₃ * (2 * eis d.q) = 2 * (eis d.al + d.turn₃ * eis d.q) by ring,
    ringTurn₂_mul_eis h.al_ne_zero h.p_ne_zero, ringTurn₃_hinge h.al_ne_zero h.q_ne_zero]

/-! ### The centres, exactly -/

/-- The turn of body 2 is what its ring coordinate says. -/
theorem toC_turn₂Q (h : RingOk d) : RingNum.toC d.D d.turn₂Q = d.turn₂ := by
  have hane : ((d.a : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 h.ha.ne'
  have hbne : ((d.b : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 h.hb.ne'
  have haQ : ((d.a : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 h.ha.ne'
  have hbQ : ((d.b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 h.hb.ne'
  rw [RingData.turn₂Q, RingNum.toC_smul, RingNum.toC_mul _ _ h.hD, RingNum.toC_tau,
    RingNum.toC_eis]
  change _ = ringTurn₂ d.al d.p d.q (d.sg : ℝ)
  rw [ringTurn₂]
  push_cast
  field_simp

/-- The turn of body 3 is what its ring coordinate says. -/
theorem toC_turn₃Q (h : RingOk d) : RingNum.toC d.D d.turn₃Q = d.turn₃ := by
  have hane : ((d.a : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 h.ha.ne'
  have hcne : ((d.c : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 h.hc.ne'
  have haQ : ((d.a : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 h.ha.ne'
  have hcQ : ((d.c : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 h.hc.ne'
  rw [RingData.turn₃Q, RingNum.toC_smul, RingNum.toC_mul _ _ h.hD, RingNum.toC_sub,
    RingNum.toC_tau, RingNum.toC_eis]
  have h1 : RingNum.toC d.D ⟨(d.a : ℚ), 0, 0, 0⟩ = ((d.a : ℤ) : ℂ) := by
    refine Complex.ext ?_ ?_ <;> simp
  rw [h1]
  change _ = ringTurn₃ d.al d.p d.q (d.sg : ℝ)
  rw [ringTurn₃]
  push_cast
  field_simp

theorem center_eq (h : RingOk d) (i : d.Idx) : d.center i = RingNum.toC d.D (d.centerQ i) := by
  have ht₂ := h.toC_turn₂Q
  have ht₃ := h.toC_turn₃Q
  rcases i with i | j | k
  · change latticePoint _ = _
    rw [RingData.centerQ, RingNum.toC_smul_two_eis]
  · change d.turn₂ * latticePoint _ = _
    rw [RingData.centerQ, RingNum.toC_smul, RingNum.toC_mul _ _ h.hD, ht₂, RingNum.toC_eis,
      latticePoint_eq_eis]
    push_cast
    ring
  · change latticePoint d.al + d.turn₃ * latticePoint _ = _
    rw [RingData.centerQ, RingNum.toC_smul, RingNum.toC_add, RingNum.toC_mul _ _ h.hD, ht₃,
      RingNum.toC_eis, RingNum.toC_eis, latticePoint_eq_eis, latticePoint_eq_eis]
    push_cast
    ring

/-- **No two circles of the ring overlap.** -/
theorem two_le_dist (h : RingOk d) :
    Pairwise fun i j => 2 ≤ dist (d.center i) (d.center j) := by
  intro i j hij
  rw [h.center_eq i, h.center_eq j]
  exact RingNum.two_le_dist_toC _ _ h.hD (h.sep i j hij)

end RingOk

/-- **The arrangement of a ring**, when `RingData.Check` passes. -/
noncomputable def ringArr {d : RingData} (h : d.Check = true) : Arrangement d.Idx where
  center := d.center
  nonoverlap := (RingOk.of_check h).two_le_dist

/-! ## The three bodies as clusters -/

namespace RingData

variable (d : RingData)

/-- The hinge shared by bodies 1 and 2. -/
def H₁₂ : d.Idx := Sum.inl ⟨0, Nat.succ_pos _⟩

/-- The hinge shared by bodies 1 and 3. -/
def H₁₃ : d.Idx := Sum.inl ⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩

/-- The hinge shared by bodies 2 and 3. -/
def H₂₃ : d.Idx := Sum.inr (Sum.inl ⟨0, Nat.succ_pos _⟩)

/-- Body 1's circles, indexed by its site list. -/
def idx₁ : Fin d.B₁.length → d.Idx := Sum.inl

/-- Body 2's circles, indexed by its site list: site `0` is the hinge it shares with body 1,
which is one of body 1's circles. -/
def idx₂ : Fin d.B₂.length → d.Idx
  | ⟨0, _⟩ => d.H₁₂
  | ⟨j + 1, hj⟩ => Sum.inr (Sum.inl ⟨j, Nat.lt_of_succ_lt_succ hj⟩)

/-- Body 3's circles, indexed by its site list: site `0` is the hinge it shares with body 1 (a
circle of body 1) and site `1` is the hinge it shares with body 2 (a circle of body 2). -/
def idx₃ : Fin d.B₃.length → d.Idx
  | ⟨0, _⟩ => d.H₁₃
  | ⟨1, _⟩ => d.H₂₃
  | ⟨k + 2, hk⟩ => Sum.inr (Sum.inr ⟨k, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)⟩)

theorem idx₁_injective : Function.Injective d.idx₁ := Sum.inl_injective

theorem idx₂_injective : Function.Injective d.idx₂ := by
  rintro ⟨(_ | i), hi⟩ ⟨(_ | j), hj⟩ h <;> simp only [idx₂, H₁₂] at h
  · rfl
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at h
    simpa using h

theorem idx₃_injective : Function.Injective d.idx₃ := by
  rintro ⟨(_ | _ | i), hi⟩ ⟨(_ | _ | j), hj⟩ h <;> simp only [idx₃, H₁₃, H₂₃] at h
  · rfl
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · rfl
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Sum.inr.injEq, Fin.mk.injEq] at h
    simpa using h

end RingData

namespace RingOk

variable {d : RingData}

theorem center_idx₁ (i : Fin d.B₁.length) :
    d.center (d.idx₁ i) = 0 + (1 : ℂ) * latticePoint (d.B₁.get i) := by
  change latticePoint _ = _
  ring

theorem center_idx₂ (j : Fin d.B₂.length) :
    d.center (d.idx₂ j) = 0 + d.turn₂ * latticePoint (d.B₂.get j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · change latticePoint ((0 : ℤ × ℤ)) = 0 + d.turn₂ * latticePoint ((0 : ℤ × ℤ))
    rw [latticePoint_zero]
    ring
  · change d.turn₂ * latticePoint (d.L₂.get j) = 0 + d.turn₂ * latticePoint (d.L₂.get j)
    ring

theorem center_idx₃ (h : RingOk d) (k : Fin d.B₃.length) :
    d.center (d.idx₃ k) = latticePoint d.al + d.turn₃ * latticePoint (d.B₃.get k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · change latticePoint d.al = latticePoint d.al + d.turn₃ * latticePoint ((0 : ℤ × ℤ))
    rw [latticePoint_zero]
    ring
  · refine Fin.cases ?_ (fun k => ?_) k
    · change d.turn₂ * latticePoint d.p = latticePoint d.al + d.turn₃ * latticePoint d.q
      exact h.hinge_eq
    · change latticePoint d.al + d.turn₃ * latticePoint _ = _
      rfl

theorem body₁_isRigid (h : RingOk d) : IsLocallyRigid (d.center ∘ d.idx₁) :=
  isLocallyRigid_of_bodyOk h.b₁ (γ := 1) (o := 0) norm_one (fun i => center_idx₁ i)

theorem body₂_isRigid (h : RingOk d) : IsLocallyRigid (d.center ∘ d.idx₂) :=
  isLocallyRigid_of_bodyOk h.b₂ (o := 0) h.norm_turn₂ (fun j => center_idx₂ j)

theorem body₃_isRigid (h : RingOk d) : IsLocallyRigid (d.center ∘ d.idx₃) :=
  isLocallyRigid_of_bodyOk h.b₃ h.norm_turn₃ (fun k => h.center_idx₃ k)

end RingOk

/-! ## Rigidity of a ring -/

/-- **A ring is rigid.** Three clusters — the three turned lattice bodies, each fed in by
`Arrangement.rigidIn_of_comap` — pairwise share the three hinges `H₁₂`, `H₁₃`, `H₂₃`, which are
distinct circles. That is exactly the hypothesis shape of **R2**
(`Arrangement.RigidIn.union_of_ring`), so one merge gives a cluster containing every circle, and
`Arrangement.rigidIn_univ_iff` turns that into rigidity.

No non-degeneracy of the hinge triangle appears, and none is needed: R2 cares about the three
shared circles being distinct, not about the shape of their triangle. -/
theorem ringArr_isRigid {d : RingData} (h : d.Check = true) : (ringArr h).IsRigid := by
  have ok := RingOk.of_check h
  rw [← Arrangement.rigidIn_univ_iff]
  have h₁ : (ringArr h).RigidIn (Set.range d.idx₁) :=
    (ringArr h).rigidIn_of_comap d.idx₁ d.idx₁_injective ok.body₁_isRigid
  have h₂ : (ringArr h).RigidIn (Set.range d.idx₂) :=
    (ringArr h).rigidIn_of_comap d.idx₂ d.idx₂_injective ok.body₂_isRigid
  have h₃ : (ringArr h).RigidIn (Set.range d.idx₃) :=
    (ringArr h).rigidIn_of_comap d.idx₃ d.idx₃_injective ok.body₃_isRigid
  refine (h₁.union_of_ring h₂ h₃ (c₁ := d.H₂₃) (c₂ := d.H₁₃) (c₃ := d.H₁₂)
    ⟨⟨⟨0, Nat.succ_pos _⟩, rfl⟩, ⟨⟨0, Nat.succ_pos _⟩, rfl⟩⟩
    ⟨⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩, rfl⟩, ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩, rfl⟩⟩
    ⟨⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩, rfl⟩, ⟨⟨0, Nat.succ_pos _⟩, rfl⟩⟩
    (by simp [RingData.H₂₃, RingData.H₁₃]) (by simp [RingData.H₂₃, RingData.H₁₂])
    (by simp [RingData.H₁₃, RingData.H₁₂])).mono ?_
  rintro (i | j | k) -
  · exact Or.inl (Or.inl ⟨i, rfl⟩)
  · exact Or.inl (Or.inr ⟨j.succ, rfl⟩)
  · exact Or.inr ⟨k.succ.succ, rfl⟩

/-! ## The hinge triangle closes -/

/-- **`|H₁₂ H₂₃|² = 4b`**, by `normSq_ringApex`: body 2's hinge with body 3 really is at the
prescribed distance from the origin. -/
theorem ringArr_hinge_dist₁₂ {d : RingData} (h : d.Check = true) :
    dist ((ringArr h).center d.H₁₂) ((ringArr h).center d.H₂₃) ^ 2 = 4 * (d.b : ℝ) := by
  have ok := RingOk.of_check h
  have hap := ringTurn₂_mul_eis (q := d.q) (σ := (d.sg : ℝ)) ok.al_ne_zero ok.p_ne_zero
  change dist (latticePoint ((0 : ℤ × ℤ))) (d.turn₂ * latticePoint d.p) ^ 2 = _
  rw [latticePoint_zero, latticePoint_eq_eis, dist_zero_left, Complex.sq_norm,
    show d.turn₂ * (2 * eis d.p) = 2 * (d.turn₂ * eis d.p) by ring, hap, map_mul,
    normSq_ringApex ok.hD ok.sg_sq ok.al_ne_zero rfl]
  norm_num

/-- **`|H₁₃ H₂₃|² = 4c`**, by `normSq_ringApex_sub`. -/
theorem ringArr_hinge_dist₁₃ {d : RingData} (h : d.Check = true) :
    dist ((ringArr h).center d.H₁₃) ((ringArr h).center d.H₂₃) ^ 2 = 4 * (d.c : ℝ) := by
  have ok := RingOk.of_check h
  have hap := ringTurn₂_mul_eis (q := d.q) (σ := (d.sg : ℝ)) ok.al_ne_zero ok.p_ne_zero
  change dist (latticePoint d.al) (d.turn₂ * latticePoint d.p) ^ 2 = _
  rw [latticePoint_eq_eis, latticePoint_eq_eis,
    show d.turn₂ * (2 * eis d.p) = 2 * (d.turn₂ * eis d.p) by ring, hap, dist_eq_norm,
    Complex.sq_norm,
    show 2 * eis d.al - 2 * ringApex d.a d.b d.c (d.sg : ℝ) d.al =
      -(2 * (ringApex d.a d.b d.c (d.sg : ℝ) d.al - eis d.al)) by ring,
    Complex.normSq_neg, map_mul, normSq_ringApex_sub ok.hD ok.sg_sq ok.al_ne_zero rfl]
  norm_num

/-! ## Off the lattice, by the turn of body 2 -/

/-- **A ring is off the lattice when its second body is turned out of the frame.** Body 1 and
body 2 each contain a contact; on the lattice all contacts would have the same frame invariant
(`Arrangement.IsLattice.frameInv_eq`), and these two differ by `turn₂ ^ 6`.

The hypothesis is the decidable statement that the exact sixth power of the turn, computed in
`RingNum`, has vanishing `√(3D)` part and rational part other than `1`: then its *real part* is
not `1`, so `turn₂ ^ 6 ≠ 1`. No irrationality of `√(3D)` is needed. -/
theorem ringArr_not_isLattice {d : RingData} (h : d.Check = true)
    (hz : (RingNum.pow d.D d.turn₂Q 6).sq3D = 0) (hr : (RingNum.pow d.D d.turn₂Q 6).base ≠ 1)
    {s s' : ℤ × ℤ} (hs : s ∈ d.B₁) (hs' : s' ∈ d.B₁) (hss : eNorm (s - s') = 1)
    {t t' : ℤ × ℤ} (ht : t ∈ d.B₂) (ht' : t' ∈ d.B₂) (htt : eNorm (t - t') = 1) :
    ¬ (ringArr h).IsLattice := by
  have ok := RingOk.of_check h
  have ht₂ := ok.toC_turn₂Q
  -- the sixth power of the turn is not one, because its real part is not one
  have hpow : d.turn₂ ^ 6 ≠ 1 := by
    intro he
    have hcalc : d.turn₂ ^ 6 = RingNum.toC d.D (RingNum.pow d.D d.turn₂Q 6) := by
      rw [RingNum.toC_pow _ ok.hD, ht₂]
    rw [hcalc] at he
    have hre := congrArg Complex.re he
    rw [RingNum.toC_re, hz] at hre
    simp only [Rat.cast_zero, zero_mul, add_zero, Complex.one_re] at hre
    exact hr (by exact_mod_cast hre)
  -- a contact inside body 1, and one inside body 2
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 hs
  obtain ⟨i', hi'⟩ := List.mem_iff_get.1 hs'
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 ht
  obtain ⟨j', hj'⟩ := List.mem_iff_get.1 ht'
  have hcen : (ringArr h).center = d.center := rfl
  have t₁ : Tangent (ringArr h).center (d.idx₁ i) (d.idx₁ i') := by
    change dist (latticePoint (d.B₁.get i)) (latticePoint (d.B₁.get i')) = 2
    rw [hi, hi', tangent_latticePoint_iff, hss]
  have t₂ : Tangent (ringArr h).center (d.idx₂ j) (d.idx₂ j') := by
    change dist (d.center (d.idx₂ j)) (d.center (d.idx₂ j')) = 2
    rw [RingOk.center_idx₂ j, RingOk.center_idx₂ j', hj, hj', zero_add, zero_add, dist_eq_norm,
      ← mul_sub, norm_mul, ok.norm_turn₂, one_mul, ← dist_eq_norm, tangent_latticePoint_iff, htt]
  refine Arrangement.not_isLattice_of_frameInv_ne t₁ t₂ ?_
  have e₁ : (ringArr h).center (d.idx₁ i') - (ringArr h).center (d.idx₁ i) =
      latticePoint (s' - s) := by
    change latticePoint (d.B₁.get i') - latticePoint (d.B₁.get i) = _
    rw [hi, hi', latticePoint_sub]
  have e₂ : (ringArr h).center (d.idx₂ j') - (ringArr h).center (d.idx₂ j) =
      d.turn₂ * latticePoint (t' - t) := by
    change d.center (d.idx₂ j') - d.center (d.idx₂ j) = _
    rw [RingOk.center_idx₂ j, RingOk.center_idx₂ j', hj, hj', zero_add, zero_add, ← mul_sub,
      latticePoint_sub]
  rw [e₁, e₂, mul_pow, latticePoint_unit_pow_six (by rw [← eNorm_neg, neg_sub]; exact hss),
    latticePoint_unit_pow_six (by rw [← eNorm_neg, neg_sub]; exact htt)]
  intro e
  exact hpow (by linear_combination (1 / 64 : ℂ) * e.symm)

/-! ## `T14`, the first ring in Lean -/

/-- **`T14`.** Hinge norms `(a, b, c) = (3, 4, 3)`, so `D = 32`; three bodies — a six-circle
chevron, a five-circle trapezoid and a six-circle chevron — pairwise sharing a hinge, with
`6 + 5 + 6 - 3 = 14` circles and `9 + 7 + 9 = 25 = 2 · 14 - 3` contacts, all of them inside a
body. The site lists are the bodies of `docs/offlattice.md` §5 read in each body's own frame:
`B₁` is the chevron `c0 … c5` with its hinges `c4`, `c5` first; `B₂` is `{c4, c6, c7, c8, c9}`;
`B₃` is `{c5, c6, c10, …, c13}`. -/
def t14Data : RingData where
  al := (1, -2)
  p := (2, 0)
  q := (1, 1)
  r₁ := [(-1, -1), (-1, 0), (0, -2), (0, -1)]
  r₂ := [(1, 0), (0, 1), (1, 1)]
  r₃ := [(1, 0), (1, -1), (2, -1), (2, 0)]
  m₁ := [(0, 0), (0, -1), (-1, 0), (-1, -1), (0, -2), (1, -2)]
  m₂ := [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0)]
  m₃ := [(0, 0), (1, 0), (1, -1), (2, -1), (2, 0), (1, 1)]
  sg := 1

/-- `T14`'s hinge norms are `(3, 4, 3)` and its discriminant is `32`, as `t14_ringD` of
`RigidArrangements/Ring.lean` computes. -/
theorem t14Data_ringD : t14Data.a = 3 ∧ t14Data.b = 4 ∧ t14Data.c = 3 ∧ t14Data.D = 32 := by decide

/-- **The `T14` certificate.** All three bodies have build orders, the hinge triangle closes
(`D = 32 ≥ 0`), and none of the `91` pairs of circles overlaps — every squared distance is
`A + B √96` with `A`, `B` rational, and a single `nonnegSqrt` decides each one. -/
theorem t14Check : t14Data.Check = true := by decide +kernel

/-- **`T14` as an arrangement of fourteen circles.** -/
noncomputable def t14 : Arrangement t14Data.Idx := ringArr t14Check

/-- **`T14` is rigid**, by one application of R2 to its three bodies. -/
theorem t14_isRigid : t14.IsRigid := ringArr_isRigid t14Check

/-- **`T14` has fourteen circles**: `6 + 4 + 4`, the three bodies' `6 + 5 + 6` sites with the
three hinges counted once each. -/
theorem t14_card : Fintype.card t14Data.Idx = 14 := rfl

/-- **Each of `T14`'s three bodies is isostatic**: `9`, `7` and `9` contacts, counted here as
`18`, `14` and `18` ordered pairs of sites, so `9 + 7 + 9 = 25 = 2 · 14 - 3`. That is exactly
the contact count `docs/offlattice.md` §5 records for `T14`, so — taking that count as given,
since this file does not prove it — no contact of `T14` joins two bodies. -/
theorem t14_body_contacts :
    (t14Data.B₁.map fun x => t14Data.B₁.countP fun y => eNorm (x - y) == 1).sum = 18 ∧
      (t14Data.B₂.map fun x => t14Data.B₂.countP fun y => eNorm (x - y) == 1).sum = 14 ∧
        (t14Data.B₃.map fun x => t14Data.B₃.countP fun y => eNorm (x - y) == 1).sum = 18 := by
  decide +kernel

/-- **`T14`'s hinge triangle has squared sides `12`, `16`, `12`**, as `docs/offlattice.md` §5
records: the two sides at the apex come from `normSq_ringApex` and `normSq_ringApex_sub` of
`RigidArrangements/Ring.lean`, the third from the lattice. -/
theorem t14_hinge_dists :
    dist (t14.center t14Data.H₁₂) (t14.center t14Data.H₂₃) ^ 2 = 16 ∧
      dist (t14.center t14Data.H₁₃) (t14.center t14Data.H₂₃) ^ 2 = 12 ∧
        dist (t14.center t14Data.H₁₂) (t14.center t14Data.H₁₃) ^ 2 = 12 := by
  obtain ⟨-, hb, hc, -⟩ := t14Data_ringD
  have e : t14 = ringArr t14Check := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ringArr_hinge_dist₁₂ t14Check, hb]; norm_num
  · rw [e, ringArr_hinge_dist₁₃ t14Check, hc]; norm_num
  · change dist (latticePoint ((0 : ℤ × ℤ))) (latticePoint t14Data.al) ^ 2 = 12
    rw [dist_latticePoint_sq, show eNorm ((0 : ℤ × ℤ) - t14Data.al) = 3 from by decide]
    norm_num

/-- **`T14` is off the lattice.** Its body-2 turn is `(√6 - i√3)/3`, whose sixth power is
`(-69 + 30 i√2)/81`: the `√96` part vanishes and the rational part is `-23/27`, not `1`. The
contacts used are `(0,0)-(0,-1)` inside body 1 and `(0,0)-(1,0)` inside body 2.

The hinge-triangle route of `hbArr_not_isLattice` is unavailable here: it needs a contact for
one side of the triangle it tests, and a ring has no bar — `T14`'s hinge triangle has squared
sides `12`, `16`, `12`. Only the relative turn of two bodies betrays the arrangement. -/
theorem t14_not_isLattice : ¬ t14.IsLattice :=
  ringArr_not_isLattice t14Check (by decide +kernel) (by decide +kernel)
    (s := (0, 0)) (s' := (0, -1)) (by decide) (by decide) (by decide)
    (t := (0, 0)) (t' := (1, 0)) (by decide) (by decide) (by decide)

end RigidArrangements

