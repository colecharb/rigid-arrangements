import RigidArrangements.Rigidity

/-!
# Infinitesimal rigidity

Local rigidity (`IsLocallyRigid`) talks about *all* placements near `p`, so it is hard to
check directly. *Infinitesimal rigidity* is a finite linear-algebra condition that implies it.
It is the standard certificate of rigidity in rigidity theory.

Let each center `p i` move with velocity `u i`. To first order, the contact `i j` keeps its
length `2` exactly when `⟪p i - p j, u i - u j⟫ = 0`: the relative velocity of the two centers
is perpendicular to the line through them. A velocity field with this property for every
contact is an *infinitesimal flex*. Moving the whole plane rigidly (a translation plus a
rotation) always gives one; these are the *trivial* flexes. The placement is *infinitesimally
rigid* when every infinitesimal flex is trivial.

Throughout, the plane is `ℂ`, and `⟪z, w⟫ = Re (w * conj z)` is the usual dot product of `ℝ²`.
Turning a vector `z` by a right angle is multiplication by `I`.

## Main definitions

* `IsInfFlex p u`: the velocity field `u` keeps every contact of `p` to first order.
* `IsTrivialFlex p u`: `u` is the velocity field of a rigid motion of the plane.
* `IsInfRigid p`: some contact `a b` of `p` has the property that pinning `a` and `b`
  (velocity `0`) leaves no infinitesimal flex except `0`.
* `rigidityMap p`: the linear map `u ↦ (⟪p i - p j, u i - u j⟫)` over the contacts `i j`.
  Its kernel is the space of infinitesimal flexes.

## Main results

* `isInfRigid_iff`: `p` is infinitesimally rigid exactly when it has a contact and every
  infinitesimal flex is trivial. This is the textbook definition.
* `isLocallyRigid_of_isInfRigid`: **infinitesimal rigidity implies local rigidity**, for
  finitely many circles.
* `Arrangement.isRigid_of_isInfRigid`: the same statement for arrangements.
* `Arrangement.triangle_isInfRigid`: the equilateral triangle is infinitesimally rigid.
* `not_isInfRigid_of_taut`, `Arrangement.not_isInfRigid_of_taut`: a circle that touches
  exactly two circles, whose centers are `4` apart, can always move sideways to first order,
  so the arrangement is not infinitesimally rigid.

## How the main result is proved

The proof is elementary: a quadratic estimate, no implicit function theorem. Let `q` be a
placement close to `p` that keeps every contact. Move `q` by a rigid motion so that it agrees
with `p` at the pinned circles `a` and `b`, and let `u = q - p`. For a contact `i j` put
`x = p i - p j` and `y = u i - u j`. Then `‖x‖ = ‖x + y‖ = 2`, and expanding `‖x + y‖²` gives
`2 ⟪x, y⟫ = -‖y‖²`. So the rigidity map is quadratically small at `u`:
`‖R u‖ ≤ 2 ‖u‖²`. Infinitesimal rigidity says that `R` is injective on the (finite-dimensional)
space of velocity fields vanishing at `a` and `b`, so `‖u‖ ≤ K ‖R u‖` for some constant `K`.
Together, `‖u‖ ≤ 2 K ‖u‖²`: either `u = 0`, or `‖u‖ ≥ 1 / (2 K)`. The second is impossible when
`q` is close enough to `p`. Hence `u = 0`, and `q` is congruent to `p`.

## Infinitesimal rigidity is strictly stronger

The converse of `isLocallyRigid_of_isInfRigid` fails. If two circles of a rigid cluster are
exactly `4` apart, a circle touching both of them is forced to sit at their midpoint, so it
cannot move at all. But it can move sideways to first order (`not_isInfRigid_of_taut`). So
`IsInfRigid` is only a certificate: it proves rigidity when it holds, and says nothing when it
fails. Also, by our definition a single circle, which has no contact, is not infinitesimally
rigid, although it is rigid.
-/

open Complex

namespace RigidArrangements

/-! ### Perpendicular vectors in the plane -/

/-- Turning a vector by a right angle (and scaling it) makes it perpendicular to the original
vector. -/
theorem inner_ofReal_mul_I_mul_self (ω : ℝ) (x : Plane) : inner ℝ x (ω * I * x) = 0 := by
  rw [Complex.inner]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, conj_re, conj_im]
  ring

/-- `I * x` is `x` turned by a right angle, so it is perpendicular to `x`. -/
theorem inner_I_mul_self (x : Plane) : inner ℝ x (I * x) = 0 := by
  simpa using inner_ofReal_mul_I_mul_self 1 x

/-- In the plane, a vector `y` perpendicular to a nonzero vector `x` is a real multiple of `x`
turned by a right angle. -/
theorem exists_eq_ofReal_mul_I_mul {x y : Plane} (hx : x ≠ 0) (h : inner ℝ x y = 0) :
    ∃ ω : ℝ, y = ω * I * x := by
  refine ⟨(y / x).im, ?_⟩
  rw [Complex.inner] at h
  simp only [mul_re, conj_re, conj_im] at h
  have hre : (y / x).re = 0 := by
    rw [div_re, ← add_div, show y.re * x.re + y.im * x.im = 0 by linarith, zero_div]
  have hyx : y / x = (y / x).im * I := Complex.ext (by simp [hre]) (by simp)
  calc y = y / x * x := (div_mul_cancel₀ y hx).symm
    _ = _ := by rw [← hyx]

/-- If `w` is at distance `2` from both `a` and `b`, and `a`, `b` are `4` apart, then `w` is
the midpoint of `a` and `b`: `a - w = w - b`. -/
theorem sub_eq_sub_of_taut {a b w : Plane} (ha : dist w a = 2) (hb : dist w b = 2)
    (hab : dist a b = 4) : a - w = w - b := by
  rw [Complex.dist_eq] at ha hb hab
  have ha' : ‖a - w‖ = 2 := by rw [norm_sub_rev]; exact ha
  have hpar := parallelogram_law_with_norm ℝ (a - w) (w - b)
  rw [show a - w + (w - b) = a - b by abel, hab, ha', hb] at hpar
  have h0 : ‖a - w - (w - b)‖ = 0 := by nlinarith [norm_nonneg (a - w - (w - b))]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

section InfRigid

variable {ι : Type*}

/-! ### Infinitesimal flexes -/

/-- An *infinitesimal flex* of the placement `p`: a velocity `u i` for every center that keeps
every contact length to first order.

If the centers move as `p + t • u`, the squared length of the contact `i j` changes at rate
`2 ⟪p i - p j, u i - u j⟫` at `t = 0`. So the condition is that, for every contact, the
relative velocity `u i - u j` is perpendicular to the line of centers `p i - p j`. -/
def IsInfFlex (p u : ι → Plane) : Prop :=
  ∀ i j, Tangent p i j → inner ℝ (p i - p j) (u i - u j) = 0

/-- A *trivial* infinitesimal flex: the velocity field of a rigid motion of the plane, namely a
translation with velocity `c` together with a rotation about `0` with angular speed `ω`. Under
that rotation the point `z` moves with velocity `ω * I * z`. -/
def IsTrivialFlex (p u : ι → Plane) : Prop :=
  ∃ (c : Plane) (ω : ℝ), ∀ i, u i = c + ω * I * p i

/-- *Infinitesimal rigidity*: there is a contact `a b` such that every infinitesimal flex that
pins `a` and `b` (velocity `0` at both) is `0`.

Pinning the two ends of a contact is how we get rid of the trivial flexes. A trivial flex is
determined by its values at two circles, and every infinitesimal flex agrees at `a` and `b`
with some trivial flex. So "pinning `a` and `b` leaves only `0`" says exactly that every
infinitesimal flex is trivial; this is `isInfRigid_iff`. Asking for a contact only excludes
placements without any contact; of those, only the empty placement and a single circle are
rigid. -/
def IsInfRigid (p : ι → Plane) : Prop :=
  ∃ a b, Tangent p a b ∧ ∀ u, IsInfFlex p u → u a = 0 → u b = 0 → u = 0

variable {p u v : ι → Plane}

/-- The difference of two infinitesimal flexes is an infinitesimal flex. -/
theorem IsInfFlex.sub (hu : IsInfFlex p u) (hv : IsInfFlex p v) : IsInfFlex p (u - v) :=
  fun i j hij => by
    simp only [Pi.sub_apply, sub_sub_sub_comm, inner_sub_right, hu i j hij, hv i j hij,
      sub_zero]

/-- Every trivial flex is an infinitesimal flex: rigid motions keep all distances. -/
theorem IsTrivialFlex.isInfFlex (h : IsTrivialFlex p u) : IsInfFlex p u := by
  obtain ⟨c, ω, hu⟩ := h
  intro i j _
  rw [hu i, hu j, show c + ω * I * p i - (c + ω * I * p j) = ω * I * (p i - p j) by ring]
  exact inner_ofReal_mul_I_mul_self ω _

/-- Two tangent circles have different centers. -/
theorem sub_ne_zero_of_tangent {a b : ι} (h : Tangent p a b) : p a - p b ≠ 0 := by
  intro h0
  rw [Tangent, Complex.dist_eq, h0, norm_zero] at h
  norm_num at h

/-- A trivial flex that vanishes at two circles with different centers vanishes everywhere. -/
theorem IsTrivialFlex.eq_zero (h : IsTrivialFlex p u) {a b : ι} (hab : p a - p b ≠ 0)
    (ha : u a = 0) (hb : u b = 0) : u = 0 := by
  obtain ⟨c, ω, hc⟩ := h
  have hω : (ω : ℂ) = 0 := by
    have h0 : (ω : ℂ) * I * (p a - p b) = 0 := by
      linear_combination hc b - hc a - hb + ha
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_right I_ne_zero
    · exact absurd h1 hab
  have hc0 : c = 0 := by
    have := hc a
    rw [ha, hω, zero_mul, zero_mul, add_zero] at this
    exact this.symm
  funext k
  rw [hc k, hω, hc0, zero_mul, zero_mul, add_zero, Pi.zero_apply]

/-- **Infinitesimal rigidity, textbook form.** `p` is infinitesimally rigid exactly when it has
a contact and every infinitesimal flex is trivial. -/
theorem isInfRigid_iff :
    IsInfRigid p ↔ (∃ a b, Tangent p a b) ∧ ∀ u, IsInfFlex p u → IsTrivialFlex p u := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    refine ⟨⟨a, b, hab⟩, fun u hu => ?_⟩
    obtain ⟨ω, hω⟩ := exists_eq_ofReal_mul_I_mul (sub_ne_zero_of_tangent hab) (hu a b hab)
    -- the trivial flex that agrees with `u` at `a` and `b`
    let t : ι → Plane := fun k => (u a - ω * I * p a) + ω * I * p k
    have ht : IsTrivialFlex p t := ⟨_, ω, fun _ => rfl⟩
    have h0 := h (u - t) (hu.sub ht.isInfFlex) (by simp [t])
      (by simp only [t, Pi.sub_apply]; linear_combination -hω)
    exact ⟨u a - ω * I * p a, ω, fun k => sub_eq_zero.mp (congrFun h0 k)⟩
  · rintro ⟨⟨a, b, hab⟩, h⟩
    exact ⟨a, b, hab, fun u hu ha hb => (h u hu).eq_zero (sub_ne_zero_of_tangent hab) ha hb⟩

/-! ### The rigidity map -/

open Classical in
/-- The *rigidity map* of `p`. It sends a velocity field `u` to the first-order change
`⟪p i - p j, u i - u j⟫` of each contact `i j` (and to `0` for pairs that do not touch). Its
kernel is the space of infinitesimal flexes (`rigidityMap_eq_zero_iff`). -/
noncomputable def rigidityMap (p : ι → Plane) : (ι → Plane) →ₗ[ℝ] ι → ι → ℝ where
  toFun u i j := if Tangent p i j then inner ℝ (p i - p j) (u i - u j) else 0
  map_add' u v := by
    ext i j
    simp only [Pi.add_apply]
    split_ifs <;> simp [add_sub_add_comm, inner_add_right]
  map_smul' c u := by
    ext i j
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs
    · rw [← smul_sub, real_inner_smul_right]
    · simp

/-- On a contact, the rigidity map records the first-order change of its length. -/
theorem rigidityMap_apply_of_tangent {i j : ι} (h : Tangent p i j) :
    rigidityMap p u i j = inner ℝ (p i - p j) (u i - u j) := by
  simp only [rigidityMap, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left h]

/-- On a pair that does not touch, the rigidity map is `0`. -/
theorem rigidityMap_apply_of_not_tangent {i j : ι} (h : ¬ Tangent p i j) :
    rigidityMap p u i j = 0 := by
  simp only [rigidityMap, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right h]

/-- The kernel of the rigidity map is the space of infinitesimal flexes. -/
theorem rigidityMap_eq_zero_iff : rigidityMap p u = 0 ↔ IsInfFlex p u := by
  constructor
  · intro h i j hij
    rw [← rigidityMap_apply_of_tangent hij, h, Pi.zero_apply, Pi.zero_apply]
  · intro h
    ext i j
    by_cases hij : Tangent p i j
    · rw [rigidityMap_apply_of_tangent hij, h i j hij, Pi.zero_apply, Pi.zero_apply]
    · rw [rigidityMap_apply_of_not_tangent hij, Pi.zero_apply, Pi.zero_apply]

/-- If `x` and `x + y` both have length `2`, then `2 ⟪x, y⟫ = -‖y‖²`. This is the second-order
identity behind `isLocallyRigid_of_isInfRigid`. -/
theorem two_mul_inner_eq_neg_sq {x y : Plane} (hx : ‖x‖ = 2) (hxy : ‖x + y‖ = 2) :
    2 * inner ℝ x y = -‖y‖ ^ 2 := by
  have h := norm_add_sq_real x y
  rw [hx, hxy] at h
  linarith

/-! ### Infinitesimal rigidity implies local rigidity -/

/-- **Infinitesimal rigidity implies local rigidity.** If pinning the two ends of some contact
leaves no infinitesimal flex except `0`, then every placement close to `p` that keeps all
contacts of `p` is congruent to `p`. -/
theorem isLocallyRigid_of_isInfRigid [Finite ι] (h : IsInfRigid p) : IsLocallyRigid p := by
  have := Fintype.ofFinite ι
  rw [isLocallyRigid_iff_eps]
  obtain ⟨a, b, htab, hrig⟩ := h
  -- velocity fields pinned at `a` and `b`
  let V : Submodule ℝ (ι → Plane) :=
    LinearMap.ker (LinearMap.proj a) ⊓ LinearMap.ker (LinearMap.proj b)
  have mem_V : ∀ {w : ι → Plane}, w ∈ V ↔ w a = 0 ∧ w b = 0 := by
    intro w
    simp only [V, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
  -- the rigidity map is injective on `V`, hence bounded below
  have hker : LinearMap.ker ((rigidityMap p).comp V.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hflex : IsInfFlex p w := rigidityMap_eq_zero_iff.mp hw
    exact Subtype.ext (hrig w hflex (mem_V.mp w.2).1 (mem_V.mp w.2).2)
  obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith _ hker
  -- a bound on the size of `p`
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ i, ‖p i - p a‖ ≤ D :=
    ⟨∑ i, ‖p i - p a‖, by positivity, fun i =>
      Finset.single_le_sum (f := fun i => ‖p i - p a‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)⟩
  set C : ℝ := D + 4 with hC
  have hCpos : 0 < C := by positivity
  have hKpos' : (0 : ℝ) < K := by exact_mod_cast hKpos
  refine ⟨min 1 (1 / (4 * K * C)), by positivity, fun q hq hkeep i j => ?_⟩
  have hε1 : ∀ i, dist (q i) (p i) < 1 := fun i => (hq i).trans_le (min_le_left _ _)
  set ε := min 1 (1 / (4 * K * C)) with hε
  -- move `q` rigidly so that it agrees with `p` at `a` and `b`
  have hpab : ‖p b - p a‖ = 2 := by rw [← Complex.dist_eq, dist_comm]; exact htab
  have hqab : ‖q b - q a‖ = 2 := by rw [← Complex.dist_eq, dist_comm]; exact hkeep a b htab
  have hqab0 : q b - q a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hqab
    norm_num at hqab
  set ρ : ℂ := (p b - p a) / (q b - q a) with hρ
  have hρn : ‖ρ‖ = 1 := by rw [hρ, norm_div, hpab, hqab]; norm_num
  set q' : ι → Plane := fun k => p a + ρ * (q k - q a) with hq'
  have hdist' : ∀ k l, dist (q' k) (q' l) = dist (q k) (q l) := by
    intro k l
    simp only [hq', Complex.dist_eq]
    rw [show p a + ρ * (q k - q a) - (p a + ρ * (q l - q a)) = ρ * (q k - q l) by ring,
      norm_mul, hρn, one_mul]
  have hq'a : q' a = p a := by simp [hq']
  have hq'b : q' b = p b := by
    simp only [hq', hρ]
    field_simp
    ring
  set u : ι → Plane := q' - p with hu
  have hu_mem : u ∈ V := mem_V.mpr ⟨by simp [hu, hq'a], by simp [hu, hq'b]⟩
  -- `u` is small
  have hρ1 : ‖ρ - 1‖ ≤ ε := by
    have e : ρ - 1 = ((p b - p a) - (q b - q a)) / (q b - q a) := by
      rw [hρ]
      field_simp
    rw [e, norm_div, hqab]
    have h1 : ‖(p b - p a) - (q b - q a)‖ ≤ ‖q a - p a‖ + ‖q b - p b‖ := by
      calc ‖(p b - p a) - (q b - q a)‖ = ‖(q a - p a) - (q b - p b)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖q a - p a‖ < ε := by rw [← Complex.dist_eq]; exact hq a
    have h3 : ‖q b - p b‖ < ε := by rw [← Complex.dist_eq]; exact hq b
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hu_small : ∀ k, ‖u k‖ ≤ ε * C := by
    intro k
    have e1 : u k = (ρ - 1) * (q k - q a) + ((q k - p k) - (q a - p a)) := by
      simp only [hu, hq', Pi.sub_apply]
      ring
    have hk : ‖q k - p k‖ < ε := by rw [← Complex.dist_eq]; exact hq k
    have ha : ‖q a - p a‖ < ε := by rw [← Complex.dist_eq]; exact hq a
    have hqk : ‖q k - q a‖ ≤ D + 2 := by
      have e2 : q k - q a = (p k - p a) + ((q k - p k) - (q a - p a)) := by ring
      have hk1 := hε1 k
      have ha1 := hε1 a
      rw [Complex.dist_eq] at hk1 ha1
      rw [e2]
      calc _ ≤ ‖p k - p a‖ + ‖(q k - p k) - (q a - p a)‖ := norm_add_le _ _
        _ ≤ D + (‖q k - p k‖ + ‖q a - p a‖) := add_le_add (hD k) (norm_sub_le _ _)
        _ ≤ D + 2 := by linarith
    rw [e1]
    calc _ ≤ ‖(ρ - 1) * (q k - q a)‖ + ‖(q k - p k) - (q a - p a)‖ := norm_add_le _ _
      _ ≤ ε * (D + 2) + (ε + ε) := by
        rw [norm_mul]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add hk.le ha.le)
      _ = ε * C := by rw [hC]; ring
  -- the rigidity map is quadratically small at `u`
  have hRu : ‖rigidityMap p u‖ ≤ 2 * ‖u‖ ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
    by_cases hij : Tangent p i j
    · rw [rigidityMap_apply_of_tangent hij]
      have hx : ‖p i - p j‖ = 2 := by rw [← Complex.dist_eq]; exact hij
      have hxy : ‖(p i - p j) + (u i - u j)‖ = 2 := by
        have e : (p i - p j) + (u i - u j) = q' i - q' j := by
          simp only [hu, Pi.sub_apply]
          ring
        rw [e, ← Complex.dist_eq, hdist']
        exact hkeep i j hij
      have key := two_mul_inner_eq_neg_sq hx hxy
      have hui : ‖u i - u j‖ ≤ 2 * ‖u‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_le_pi_norm u i, norm_le_pi_norm u j])
      rw [Real.norm_eq_abs, abs_le]
      have h0 : 0 ≤ ‖u i - u j‖ := norm_nonneg _
      constructor <;> nlinarith
    · rw [rigidityMap_apply_of_not_tangent hij, norm_zero]
      positivity
  -- so `u = 0`
  have hu0 : u = 0 := by
    by_contra hne
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hne
    have hanti := hK.le_mul_dist (⟨u, hu_mem⟩ : V) 0
    simp only [dist_zero_right, map_zero, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype] at hanti
    have h1 : ‖u‖ ≤ K * (2 * ‖u‖ ^ 2) :=
      hanti.trans (mul_le_mul_of_nonneg_left hRu (by positivity))
    have hu_norm : ‖u‖ ≤ ε * C := (pi_norm_le_iff_of_nonneg (by positivity)).mpr hu_small
    have h2 : ε * C ≤ 1 / (4 * K) := by
      calc ε * C ≤ 1 / (4 * K * C) * C := by gcongr; exact min_le_right _ _
        _ = 1 / (4 * K) := by field_simp
    have h3 : 1 ≤ 2 * K * ‖u‖ := by nlinarith
    have h4 : 2 * K * ‖u‖ ≤ 1 / 2 := by
      calc 2 * K * ‖u‖ ≤ 2 * K * (1 / (4 * K)) := by gcongr; linarith
        _ = 1 / 2 := by field_simp; ring
    linarith
  have hq'p : q' = p := sub_eq_zero.mp hu0
  rw [← hdist' i j, hq'p]

/-! ### Taut circles -/

/-- **A taut circle flexes to first order.** Suppose circle `w` touches circles `u` and `v`,
and no others, and the centers of `u` and `v` are exactly `4` apart. Then `w` sits at the
midpoint of `u` and `v`, and moving `w` alone perpendicular to the line `u v` keeps both of
its contacts to first order. This flex is not trivial, since it moves `w` but neither `u` nor
`v`. So the placement is never infinitesimally rigid, even when it is rigid. -/
theorem not_isInfRigid_of_taut {w u v : ι} (hw : ∀ k, Tangent p w k → k = u ∨ k = v)
    (hu : Tangent p w u) (hv : Tangent p w v) (h4 : dist (p u) (p v) = 4) :
    ¬ IsInfRigid p := by
  classical
  intro hrig
  have hm : p u - p w = p w - p v := sub_eq_sub_of_taut hu hv h4
  set x := p w - p u with hx
  have hwu : u ≠ w := fun h => sub_ne_zero_of_tangent hu (by rw [h, sub_self])
  have hwv : v ≠ w := fun h => sub_ne_zero_of_tangent hv (by rw [h, sub_self])
  -- move `w` alone, perpendicular to the line `u v`
  let f : ι → Plane := fun k => if k = w then I * x else 0
  have hfu : f u = 0 := ite_eq_right hwu
  have hfv : f v = 0 := ite_eq_right hwv
  have hfw : f w = I * x := ite_eq_left rfl
  -- `p w - p k = ± x` for the two neighbours `k` of `w`
  have hnb : ∀ k, Tangent p w k → p w - p k = x ∨ p w - p k = -x := by
    intro k hk
    rcases hw k hk with rfl | rfl
    · exact Or.inl rfl
    · right
      rw [hx, ← hm, neg_sub]
  have hflex : IsInfFlex p f := by
    intro i j hij
    by_cases hi : i = w <;> by_cases hj : j = w
    · rw [hi, hj, sub_self, inner_zero_left]
    · subst hi
      rw [hfw, show f j = 0 from ite_eq_right hj, sub_zero]
      rcases hnb j hij with h | h <;> rw [h]
      · exact inner_I_mul_self x
      · rw [inner_neg_left, inner_I_mul_self, neg_zero]
    · subst hj
      rw [hfw, show f i = 0 from ite_eq_right hi, zero_sub, inner_neg_right, ← neg_sub,
        inner_neg_left, neg_neg]
      rcases hnb i (tangent_comm.mp hij) with h | h <;> rw [h]
      · exact inner_I_mul_self x
      · rw [inner_neg_left, inner_I_mul_self, neg_zero]
    · rw [show f i = 0 from ite_eq_right hi, show f j = 0 from ite_eq_right hj, sub_zero,
        inner_zero_right]
  have huv : p u - p v ≠ 0 := by
    intro h0
    rw [Complex.dist_eq, h0, norm_zero] at h4
    norm_num at h4
  have hf0 := ((isInfRigid_iff.mp hrig).2 f hflex).eq_zero huv hfu hfv
  have hx0 : I * x = 0 := by rw [← hfw, hf0, Pi.zero_apply]
  exact sub_ne_zero_of_tangent hu ((mul_eq_zero.mp hx0).resolve_left I_ne_zero)

end InfRigid

namespace Arrangement

variable {ι : Type*}

/-- **Infinitesimally rigid arrangements are rigid.** -/
theorem isRigid_of_isInfRigid [Finite ι] (A : Arrangement ι) (h : IsInfRigid A.center) :
    A.IsRigid :=
  isLocallyRigid_of_isInfRigid h

/-- A circle `w` of an arrangement whose only neighbours are two circles `u`, `v` with centers
exactly `4` apart can move sideways to first order. So the arrangement is not infinitesimally
rigid. -/
theorem not_isInfRigid_of_taut (A : Arrangement ι) {w u v : ι}
    (hnb : ∀ k, A.contactGraph.Adj w k ↔ k = u ∨ k = v)
    (h4 : dist (A.center u) (A.center v) = 4) : ¬ IsInfRigid A.center := by
  refine RigidArrangements.not_isInfRigid_of_taut (w := w) (fun k hk => (hnb k).1 ⟨?_, hk⟩)
    ((hnb u).2 (Or.inl rfl)).2 ((hnb v).2 (Or.inr rfl)).2 h4
  rintro rfl
  exact sub_ne_zero_of_tangent hk (sub_self _)

/-- **The equilateral triangle is infinitesimally rigid**: with circles `0` and `1` pinned,
circle `2` touches both, and the two lines of centers through circle `2` are not parallel. -/
theorem triangle_isInfRigid : IsInfRigid triangle.center := by
  refine ⟨0, 1, triangle_tangent (by decide), fun u hu h0 h1 => ?_⟩
  have e0 := hu 2 0 (triangle_tangent (by decide))
  have e1 := hu 2 1 (triangle_tangent (by decide))
  rw [h0, sub_zero, Complex.inner] at e0
  rw [h1, sub_zero, Complex.inner] at e1
  simp only [triangle, trianglePoint, Matrix.cons_val, mul_re, conj_re, conj_im, sub_re,
    sub_im, re_ofNat, im_ofNat, sub_zero] at e0 e1
  have h3 : (u 2).im * Real.sqrt 3 = 0 := by linear_combination (e0 + e1) / 2
  have him : (u 2).im = 0 :=
    (mul_eq_zero.mp h3).resolve_right (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hre : (u 2).re = 0 := by linear_combination e0 - h3
  funext k
  fin_cases k <;> simp [h0, h1, Complex.ext_iff, hre, him]

end Arrangement

end RigidArrangements
