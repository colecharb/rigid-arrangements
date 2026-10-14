import RigidArrangements.Rigidity

/-!
# Henneberg steps: adding or removing a circle with two contacts

In the rigidity theory of bar frameworks, a *Henneberg type-1 step* (also called a
0-extension, or vertex addition) adds a new vertex joined by bars to two existing vertices.
For circle arrangements it means: put a new unit circle so that it touches two circles of the
arrangement. This file proves that the step preserves local rigidity, and that the reverse
step does too under a mild extra hypothesis.

* **Adding a circle keeps rigidity** (`IsLocallyRigid.of_comp_of_tangent`). Suppose the old
  circles are rigid and the new circle touches two old circles whose centers `a`, `b` are
  distinct. After a small motion that keeps every tangency, the old circles have the same
  pairwise distances as before, so a rotation and translation moves `a` and `b` back into
  place. Then each center, the new one included, has the same distances to `a` and `b` as
  before, which leaves two possible positions: the old one and its mirror image in the line
  `ab`. A small motion cannot jump to the mirror image (unless the point is on the line, where
  the two positions coincide), so nothing has moved. No hypothesis on the distance between
  `a` and `b` is needed: if they are exactly `4` apart, the new center is their midpoint,
  which lies on the line.
* **Removing a circle with exactly two contacts keeps rigidity**
  (`IsLocallyRigid.comp_of_tangent`), provided the two circles it touches have centers less
  than `4` apart. Any small motion of the remaining circles extends to the removed one: put
  it at the apex, on the same side as before, of the isosceles triangle with sides `2, 2`
  over its two moved neighbours. The apex moves continuously because the neighbours stay
  strictly between `0` and `4` apart. Since the removed circle had no other contacts, the
  extended motion keeps every tangency, so by rigidity of the whole arrangement it preserves
  all distances.

  Both hypotheses are needed for this argument. If the removed circle had a third contact,
  the apex need not keep it. If the neighbours are exactly `4` apart, the removed circle sits
  at their midpoint and there is no position for it once they move further apart: it imposes
  the extra constraint "at most `4` apart", which the smaller arrangement does not see.

The theorems are stated for a general relabeling: the old circles are indexed by `κ` and
placed inside `ι` by `f : κ → ι`, which misses only the new circle `i₀`. The two main special
cases are `Option ι` (new circle `none`, `IsLocallyRigid.option`, `IsLocallyRigid.of_option`)
and `Fin (n + 1)` with `Fin.succAbove` (deleting circle `i` and renumbering the rest in
order).

## Main results

* `eq_or_eq_reflect`: a point with prescribed distances to two distinct points of the plane is
  one of two mirror-image points.
* `IsLocallyRigid.of_comp_of_tangent`, `IsLocallyRigid.option`: adding a circle that touches
  two circles keeps local rigidity.
* `IsLocallyRigid.comp_of_tangent`, `IsLocallyRigid.of_option`: removing a circle that touches
  exactly two circles, less than `4` apart, keeps local rigidity.
* `Arrangement.comap`, `Arrangement.erase`, `Arrangement.addCircle`: restricting an
  arrangement to some of its circles, and adding a circle.
* `Arrangement.IsRigid.of_comap`, `Arrangement.IsRigid.addCircle`,
  `Arrangement.IsRigid.of_erase`, `Arrangement.IsRigid.of_comap_succAbove`: the adding step
  for arrangements.
* `Arrangement.IsRigid.comap`, `Arrangement.IsRigid.erase`,
  `Arrangement.IsRigid.comap_succAbove`: the removing step for arrangements.
* `Arrangement.rhombus_isRigid`: two equilateral triangles sharing an edge form a rigid
  arrangement of four circles, obtained from the triangle by one adding step.
-/

open Filter Topology ComplexConjugate

namespace RigidArrangements

/-! ### Two computations in the plane -/

/-- **Two-circle lemma.** A point `y` that has the same distances as `x` to two distinct
points `a` and `b` of the plane is `x` itself or the mirror image of `x` in the line `ab`.
The mirror image is `a + (b - a) * conj ((x - a) / (b - a))`. -/
theorem eq_or_eq_reflect {a b x y : ℂ} (hab : a ≠ b) (ha : dist y a = dist x a)
    (hb : dist y b = dist x b) :
    y = x ∨ y = a + (b - a) * conj ((x - a) / (b - a)) := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  set s := (y - a) / (b - a) with hs
  set t := (x - a) / (b - a) with ht
  have hy : y = a + (b - a) * s := by rw [hs]; field_simp; ring
  have hx : x = a + (b - a) * t := by rw [ht]; field_simp; ring
  have hn : ‖s‖ = ‖t‖ := by
    have : ‖b - a‖ * ‖s‖ = ‖b - a‖ * ‖t‖ := by
      rw [← norm_mul, ← norm_mul, show (b - a) * s = y - a by rw [hy]; ring,
        show (b - a) * t = x - a by rw [hx]; ring, ← dist_eq_norm, ← dist_eq_norm, ha]
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hd) this
  have hn1 : ‖s - 1‖ = ‖t - 1‖ := by
    have : ‖b - a‖ * ‖s - 1‖ = ‖b - a‖ * ‖t - 1‖ := by
      rw [← norm_mul, ← norm_mul, show (b - a) * (s - 1) = y - b by rw [hy]; ring,
        show (b - a) * (t - 1) = x - b by rw [hx]; ring, ← dist_eq_norm, ← dist_eq_norm, hb]
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hd) this
  have e1 := congrArg (· ^ 2) hn
  have e2 := congrArg (· ^ 2) hn1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero] at e1 e2
  have hre : s.re = t.re := by nlinarith
  have him : (s.im - t.im) * (s.im + t.im) = 0 := by nlinarith
  rcases mul_eq_zero.mp him with h | h
  · left
    rw [hy, hx]
    congr 2
    exact Complex.ext hre (by linarith)
  · right
    rw [hy]
    congr 2
    exact Complex.ext (by simp [hre]) (by simp; linarith)

/-- Norm identity for the apex of an isosceles triangle: if `v` is purely imaginary and `s`,
`l` are real, then `‖z * (s + v * l)‖² = ‖z‖² * (s² + l² ‖v‖²)`. -/
theorem norm_sq_apex {z v : ℂ} (hv : v.re = 0) (s l : ℝ) :
    ‖z * ((s : ℂ) + v * (l : ℂ))‖ ^ 2 = ‖z‖ ^ 2 * (s ^ 2 + l ^ 2 * ‖v‖ ^ 2) := by
  rw [norm_mul, mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re, hv,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im]
  ring

/-! ### Adding a circle -/

section Framework

variable {ι κ : Type*}

/-- **Henneberg step: adding a circle keeps rigidity.** The circles `f j` (for `j : κ`) are
all circles except `i₀`. If they form a locally rigid placement, and circle `i₀` touches two
of them, `f u` and `f w`, whose centers are distinct, then the whole placement is locally
rigid. No hypothesis on the distance between the centers of `f u` and `f w` is needed. -/
theorem IsLocallyRigid.of_comp_of_tangent [Finite ι] {p : ι → Plane} {f : κ → ι} {i₀ : ι}
    (hf : {i₀}ᶜ ⊆ Set.range f) (h : IsLocallyRigid (p ∘ f)) {u w : κ}
    (hu : Tangent p i₀ (f u)) (hw : Tangent p i₀ (f w)) (huw : p (f u) ≠ p (f w)) :
    IsLocallyRigid p := by
  have := Fintype.ofFinite ι
  have hcases : ∀ k, k = i₀ ∨ ∃ j, f j = k := fun k =>
    (eq_or_ne k i₀).imp_right fun hk => hf hk
  set a := p (f u) with ha_def
  set b := p (f w) with hb_def
  have hu' : dist (p i₀) a = 2 := hu
  have hw' : dist (p i₀) b = 2 := hw
  have hd : b - a ≠ 0 := sub_ne_zero.mpr huw.symm
  -- The mirror image in the line `ab`, and a uniform positive lower bound `δ` for the
  -- distance between a center off that line and its mirror image.
  set σ : ℂ → ℂ := fun z => a + (b - a) * conj ((z - a) / (b - a))
  obtain ⟨δ, hδ, hδk⟩ : ∃ δ > 0, ∀ k, σ (p k) ≠ p k → δ ≤ dist (σ (p k)) (p k) := by
    have : Nonempty ι := ⟨i₀⟩
    let g : ι → ℝ := fun k => if σ (p k) = p k then 1 else dist (σ (p k)) (p k)
    obtain ⟨k₀, hk₀⟩ := Finite.exists_min g
    refine ⟨g k₀, ?_, fun k hk => ?_⟩
    · simp only [g]
      split_ifs with h1
      · exact one_pos
      · exact dist_pos.mpr h1
    · have := hk₀ k
      simp only [g, hk, ite_false] at this ⊢
      exact this
  -- `Φ q` is `q` moved by the rotation and translation taking `q (f u)`, `q (f w)` to `a`, `b`
  -- (when these are at the right distance).
  let Φ : (ι → ℂ) → (ι → ℂ) :=
    fun q k => a + (b - a) / (q (f w) - q (f u)) * (q k - q (f u))
  have hΦp : Φ p = p := by
    funext k
    simp only [Φ, ← ha_def, ← hb_def]
    field_simp
    ring
  have hΦc : ContinuousAt Φ p := by
    refine continuousAt_pi.2 fun k => ?_
    have hden : (fun q : ι → ℂ => q (f w) - q (f u)) p ≠ 0 := by simpa using hd
    have c1 : ContinuousAt (fun q : ι → ℂ => q (f w) - q (f u)) p := by fun_prop
    have c2 : ContinuousAt (fun q : ι → ℂ => q k - q (f u)) p := by fun_prop
    exact continuousAt_const.add ((continuousAt_const.div c1 hden).mul c2)
  have hev1 : ∀ᶠ q in 𝓝 p, ∀ k, dist (Φ q k) (p k) < δ := by
    have := hΦc.eventually (Metric.ball_mem_nhds (Φ p) hδ)
    filter_upwards [this] with q hq k
    rw [hΦp] at hq
    exact (dist_le_pi_dist (Φ q) p k).trans_lt hq
  have hev2 : ∀ᶠ q in 𝓝 p, KeepsContacts (p ∘ f) (q ∘ f) → Congruent (q ∘ f) (p ∘ f) := by
    have hc : Continuous fun q : ι → ℂ => q ∘ f :=
      continuous_pi fun i => continuous_apply (f i)
    exact hc.continuousAt.eventually h
  filter_upwards [hev1, hev2] with q h1 h2 hk
  have hc := h2 fun i j hij => hk (f i) (f j) hij
  rw [congruent_iff_dist_eq] at hc
  have hqab : dist (q (f w)) (q (f u)) = dist b a := hc w u
  have hq0 : q (f w) - q (f u) ≠ 0 := by
    intro h0
    rw [dist_eq_norm, h0, norm_zero, eq_comm, dist_eq_zero] at hqab
    exact huw hqab.symm
  set ρ := (b - a) / (q (f w) - q (f u)) with hρ
  have hρn : ‖ρ‖ = 1 := by
    rw [hρ, norm_div, ← dist_eq_norm, ← dist_eq_norm, hqab, div_self]
    exact dist_ne_zero.mpr huw.symm
  have hΦdist : ∀ k l, dist (Φ q k) (Φ q l) = dist (q k) (q l) := by
    intro k l
    simp only [Φ, ← hρ, dist_eq_norm]
    rw [show a + ρ * (q k - q (f u)) - (a + ρ * (q l - q (f u))) = ρ * (q k - q l) by ring,
      norm_mul, hρn, one_mul]
  have hΦu : Φ q (f u) = a := by simp [Φ]
  have hΦw : Φ q (f w) = b := by
    simp only [Φ]
    field_simp
    ring
  -- After normalizing, every center is back in place.
  have pin : ∀ k, Φ q k = p k := by
    intro k
    have hda : dist (Φ q k) a = dist (p k) a := by
      have e : dist (Φ q k) a = dist (q k) (q (f u)) := by rw [← hΦdist, hΦu]
      rw [e]
      rcases hcases k with hk0 | ⟨j, rfl⟩
      · rw [hk0, hu', hk _ _ hu]
      · exact hc j u
    have hdb : dist (Φ q k) b = dist (p k) b := by
      have e : dist (Φ q k) b = dist (q k) (q (f w)) := by rw [← hΦdist, hΦw]
      rw [e]
      rcases hcases k with hk0 | ⟨j, rfl⟩
      · rw [hk0, hw', hk _ _ hw]
      · exact hc j w
    rcases eq_or_eq_reflect huw hda hdb with h | h
    · exact h
    · by_cases hfix : σ (p k) = p k
      · rw [h]
        exact hfix
      · exfalso
        have := hδk k hfix
        have := h1 k
        rw [h] at this
        linarith
  rw [congruent_iff_dist_eq]
  intro i j
  rw [← hΦdist, pin, pin]

/-- `Option.some` misses exactly `none`. -/
theorem range_some_eq_compl_none : Set.range (some : ι → Option ι) = {none}ᶜ := by
  rw [← Set.compl_range_some, compl_compl]

/-- **Henneberg step, `Option` form.** If the circles `some i` form a locally rigid placement
and the new circle `none` touches two of them with distinct centers, the whole placement is
locally rigid. -/
theorem IsLocallyRigid.option [Finite ι] {p : Option ι → Plane} (h : IsLocallyRigid (p ∘ some))
    {u w : ι} (hu : Tangent p none (some u)) (hw : Tangent p none (some w))
    (huw : p (some u) ≠ p (some w)) : IsLocallyRigid p :=
  IsLocallyRigid.of_comp_of_tangent range_some_eq_compl_none.ge h hu hw huw

/-! ### Removing a circle -/

/-- **Reverse Henneberg step: removing a circle keeps rigidity.** The circles `f j` (for
`j : κ`, with `f` injective) are all circles except `i₀`. Suppose circle `i₀` touches exactly
two of them, `f u` and `f w`, whose centers are distinct and less than `4` apart. If the
whole placement is locally rigid, so is the placement of the circles `f j`. -/
theorem IsLocallyRigid.comp_of_tangent {p : ι → Plane} {f : κ → ι} {i₀ : ι}
    (hf : Function.Injective f) (hrange : Set.range f = {i₀}ᶜ) (h : IsLocallyRigid p)
    {u w : κ} (hu : Tangent p i₀ (f u)) (hw : Tangent p i₀ (f w))
    (honly : ∀ j, Tangent p i₀ (f j) → j = u ∨ j = w)
    (huw : p (f u) ≠ p (f w)) (h4 : dist (p (f u)) (p (f w)) < 4) :
    IsLocallyRigid (p ∘ f) := by
  have hne : ∀ j, f j ≠ i₀ := fun j => by
    have := Set.mem_range_self (f := f) j
    rw [hrange] at this
    simpa using this
  have hcov : ∀ k, k ≠ i₀ → ∃ j, f j = k := fun k hk => by
    have : k ∈ Set.range f := by
      rw [hrange]
      simpa using hk
    exact this
  set a := p (f u) with ha_def
  set b := p (f w) with hb_def
  set c := p i₀
  have hd : b - a ≠ 0 := sub_ne_zero.mpr huw.symm
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.mpr hd
  have hd4 : ‖b - a‖ < 4 := by
    rw [← dist_eq_norm, dist_comm]
    exact h4
  -- Write `c = (a + b) / 2 + (b - a) * v`: `v` is purely imaginary, and `‖v‖` is determined
  -- by `‖b - a‖`.
  set v : ℂ := (c - (a + b) / 2) / (b - a) with hv_def
  have hca : c - a = (b - a) * ((1 / 2 : ℝ) + v) := by
    rw [hv_def]
    field_simp
    push_cast
    ring
  have hcb : c - b = (b - a) * ((-1 / 2 : ℝ) + v) := by
    rw [hv_def]
    field_simp
    push_cast
    ring
  have hca2 : ‖c - a‖ = 2 := by
    rw [← dist_eq_norm]
    exact hu
  have hcb2 : ‖c - b‖ = 2 := by
    rw [← dist_eq_norm]
    exact hw
  have e1 : ‖b - a‖ ^ 2 * ‖(1 / 2 : ℝ) + v‖ ^ 2 = 4 := by
    rw [← mul_pow, ← norm_mul, ← hca, hca2]
    norm_num
  have e2 : ‖b - a‖ ^ 2 * ‖(-1 / 2 : ℝ) + v‖ ^ 2 = 4 := by
    rw [← mul_pow, ← norm_mul, ← hcb, hcb2]
    norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, zero_add] at e1 e2
  have hvre : v.re = 0 := by
    have hpos : 0 < Complex.normSq (b - a) := Complex.normSq_pos.mpr hd
    rw [Complex.normSq_apply] at hpos
    nlinarith
  have hvn : ‖b - a‖ ^ 2 * ‖v‖ ^ 2 = 4 - ‖b - a‖ ^ 2 / 4 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    rw [hvre] at e1
    nlinarith
  -- The apex over a base `x y`, on the same side as `c` is over `a b`.
  set L₀ : ℝ := Real.sqrt (4 / ‖b - a‖ ^ 2 - 1 / 4) with hL₀
  have hL₀pos : 0 < L₀ := by
    apply Real.sqrt_pos.mpr
    have : ‖b - a‖ ^ 2 < 16 := by nlinarith
    rw [sub_pos, lt_div_iff₀ (by positivity)]
    linarith
  let lam : ℂ → ℂ → ℝ := fun x y => Real.sqrt (4 / ‖y - x‖ ^ 2 - 1 / 4) / L₀
  let apex : ℂ → ℂ → ℂ := fun x y => (x + y) / 2 + (y - x) * (v * (lam x y : ℂ))
  have hapex0 : apex a b = c := by
    simp only [apex, lam, ← hL₀, div_self hL₀pos.ne', Complex.ofReal_one, mul_one, hv_def]
    field_simp
    ring
  have hapex : ∀ x y : ℂ, 0 < ‖y - x‖ → ‖y - x‖ < 4 →
      dist (apex x y) x = 2 ∧ dist (apex x y) y = 2 := by
    intro x y h0 h4'
    have hlam : (lam x y) ^ 2 * ‖v‖ ^ 2 = 4 / ‖y - x‖ ^ 2 - 1 / 4 := by
      have hpos : 0 ≤ 4 / ‖y - x‖ ^ 2 - 1 / 4 := by
        have : ‖y - x‖ ^ 2 < 16 := by nlinarith
        rw [sub_nonneg, le_div_iff₀ (by positivity)]
        linarith
      simp only [lam, div_pow, Real.sq_sqrt hpos]
      have hL2 : L₀ ^ 2 = 4 / ‖b - a‖ ^ 2 - 1 / 4 := by
        rw [hL₀, Real.sq_sqrt]
        have : ‖b - a‖ ^ 2 < 16 := by nlinarith
        rw [sub_nonneg, le_div_iff₀ (by positivity)]
        linarith
      have hv2 : ‖v‖ ^ 2 = L₀ ^ 2 := by
        rw [hL2]
        field_simp
        linarith [hvn]
      rw [hv2]
      field_simp
    have key : ∀ s : ℝ, s ^ 2 = 1 / 4 → ‖(y - x) * ((s : ℂ) + v * (lam x y : ℂ))‖ = 2 := by
      intro s hs
      have := norm_sq_apex (z := y - x) hvre s (lam x y)
      rw [hs, hlam] at this
      have h2 : ‖(y - x) * ((s : ℂ) + v * (lam x y : ℂ))‖ ^ 2 = 2 ^ 2 := by
        rw [this]
        field_simp
        ring
      exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1 h2
    constructor
    · rw [dist_eq_norm, ← key (1 / 2) (by norm_num)]
      congr 1
      simp only [apex]
      push_cast
      ring
    · rw [dist_eq_norm, ← key (-1 / 2) (by norm_num)]
      congr 1
      simp only [apex]
      push_cast
      ring
  -- Extend a placement `q` of the circles `f j` by putting circle `i₀` at the apex.
  let E : (κ → ℂ) → (ι → ℂ) := fun q => Function.extend f q fun _ => apex (q u) (q w)
  have hEf : ∀ q j, E q (f j) = q j := fun q j => hf.extend_apply _ _ _
  have hE0 : ∀ q, E q i₀ = apex (q u) (q w) := fun q =>
    Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hne j hj
  have hEp : E (p ∘ f) = p := by
    funext k
    by_cases hk : k = i₀
    · rw [hk, hE0]
      exact hapex0
    · obtain ⟨j, rfl⟩ := hcov k hk
      exact hEf _ j
  have hEc : ContinuousAt E (p ∘ f) := by
    refine continuousAt_pi.2 fun k => ?_
    by_cases hk : k = i₀
    · rw [hk]
      simp only [hE0]
      have hne0 : (fun q : κ → ℂ => ‖q w - q u‖ ^ 2) (p ∘ f) ≠ 0 := by
        simp only [Function.comp_apply]
        positivity
      have c1 : ContinuousAt (fun q : κ → ℂ => ‖q w - q u‖ ^ 2) (p ∘ f) := by fun_prop
      have c2 : ContinuousAt (fun q : κ → ℂ => lam (q u) (q w)) (p ∘ f) := by
        simp only [lam]
        exact ((Real.continuous_sqrt.continuousAt).comp
          ((continuousAt_const.div c1 hne0).sub continuousAt_const)).div_const _
      have c3 : ContinuousAt (fun q : κ → ℂ => ((lam (q u) (q w) : ℝ) : ℂ)) (p ∘ f) :=
        Complex.continuous_ofReal.continuousAt.comp c2
      simp only [apex]
      fun_prop
    · obtain ⟨j, rfl⟩ := hcov k hk
      simp only [hEf]
      exact (continuous_apply j).continuousAt
  have hev1 : ∀ᶠ q in 𝓝 (p ∘ f), KeepsContacts p (E q) → Congruent (E q) p := by
    have h' : IsLocallyRigid (E (p ∘ f)) := by
      rw [hEp]
      exact h
    have := hEc.eventually h'
    rw [hEp] at this
    exact this
  have hev2 : ∀ᶠ q in 𝓝 (p ∘ f), 0 < ‖q w - q u‖ ∧ ‖q w - q u‖ < 4 := by
    have hcont : ContinuousAt (fun q : κ → ℂ => ‖q w - q u‖) (p ∘ f) := by fun_prop
    have hmem : Set.Ioo (0 : ℝ) 4 ∈ 𝓝 ((fun q : κ → ℂ => ‖q w - q u‖) (p ∘ f)) := by
      apply Ioo_mem_nhds
      · simpa using hdn
      · simpa using hd4
    exact hcont.eventually hmem
  filter_upwards [hev1, hev2] with q hq1 hq2 hk
  -- The extended placement keeps every tangency.
  have hnew : ∀ j, Tangent p i₀ (f j) → Tangent (E q) i₀ (f j) := by
    intro j hj
    simp only [Tangent, hE0, hEf]
    rcases honly j hj with rfl | rfl
    · exact (hapex _ _ hq2.1 hq2.2).1
    · exact (hapex _ _ hq2.1 hq2.2).2
  have hkE : KeepsContacts p (E q) := by
    intro i j hij
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · subst hi hj
      simp [Tangent] at hij
    · subst hi
      obtain ⟨j, rfl⟩ := hcov j hj
      exact hnew j hij
    · subst hj
      obtain ⟨i, rfl⟩ := hcov i hi
      exact tangent_comm.mpr (hnew i (tangent_comm.mp hij))
    · obtain ⟨i, rfl⟩ := hcov i hi
      obtain ⟨j, rfl⟩ := hcov j hj
      simp only [Tangent, hEf]
      exact hk i j hij
  have := hq1 hkE
  rw [congruent_iff_dist_eq] at this ⊢
  intro i j
  simpa only [hEf, Function.comp_apply] using this (f i) (f j)

/-- **Reverse Henneberg step, `Option` form.** If circle `none` touches exactly the circles
`some u` and `some w`, whose centers are distinct and less than `4` apart, and the whole
placement is locally rigid, then so is the placement of the circles `some i`. -/
theorem IsLocallyRigid.of_option {p : Option ι → Plane} (h : IsLocallyRigid p) {u w : ι}
    (hu : Tangent p none (some u)) (hw : Tangent p none (some w))
    (honly : ∀ k, Tangent p none (some k) → k = u ∨ k = w)
    (huw : p (some u) ≠ p (some w)) (h4 : dist (p (some u)) (p (some w)) < 4) :
    IsLocallyRigid (p ∘ some) :=
  IsLocallyRigid.comp_of_tangent (Option.some_injective ι) range_some_eq_compl_none h hu hw
    honly huw h4

end Framework

/-! ### Arrangements -/

namespace Arrangement

variable {ι κ : Type*}

/-- The arrangement formed by the circles `f j` of `A`, relabeled by `j : κ`. Since `f` is
injective, these are distinct circles of `A`, so they do not overlap. -/
def comap (A : Arrangement ι) (f : κ → ι) (hf : Function.Injective f) : Arrangement κ where
  center := A.center ∘ f
  nonoverlap _ _ hij := A.nonoverlap (hf.ne hij)

@[simp]
theorem comap_center (A : Arrangement ι) (f : κ → ι) (hf : Function.Injective f) :
    (A.comap f hf).center = A.center ∘ f :=
  rfl

/-- The arrangement `A` with the circle `none` removed. -/
def erase (A : Arrangement (Option ι)) : Arrangement ι :=
  A.comap some (Option.some_injective ι)

@[simp]
theorem erase_center (A : Arrangement (Option ι)) (i : ι) :
    A.erase.center i = A.center (some i) :=
  rfl

/-- The arrangement `A` with one more circle, labeled `none`, centered at `c`. The hypothesis
`hc` says that the new circle overlaps no circle of `A`. -/
def addCircle (A : Arrangement ι) (c : Plane) (hc : ∀ i, 2 ≤ dist c (A.center i)) :
    Arrangement (Option ι) where
  center k := k.elim c A.center
  nonoverlap := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact hc j
    · rw [dist_comm]
      exact hc i
    · exact A.nonoverlap fun h => hij (congrArg some h)

section addCircle

variable (A : Arrangement ι) (c : Plane) (hc : ∀ i, 2 ≤ dist c (A.center i))

@[simp]
theorem addCircle_center_none : (A.addCircle c hc).center none = c :=
  rfl

@[simp]
theorem addCircle_center_some (i : ι) : (A.addCircle c hc).center (some i) = A.center i :=
  rfl

@[simp]
theorem erase_addCircle : (A.addCircle c hc).erase = A :=
  rfl

end addCircle

/-- **Adding a circle keeps rigidity** (general labels). The circles `f j` are all circles of
`A` except `i₀`. If they form a rigid arrangement and circle `i₀` touches two of them, then
`A` is rigid. -/
theorem IsRigid.of_comap [Finite ι] {A : Arrangement ι} {f : κ → ι}
    {hf : Function.Injective f} (h : (A.comap f hf).IsRigid) {i₀ : ι}
    (hrange : {i₀}ᶜ ⊆ Set.range f) {u w : κ} (hu : Tangent A.center i₀ (f u))
    (hw : Tangent A.center i₀ (f w)) (huw : u ≠ w) : A.IsRigid :=
  IsLocallyRigid.of_comp_of_tangent hrange h hu hw (A.center_injective.ne (hf.ne huw))

/-- **Removing a circle with two contacts keeps rigidity** (general labels). The circles `f j`
are all circles of `A` except `i₀`. If `A` is rigid and circle `i₀` touches exactly two
circles, whose centers are less than `4` apart, then the other circles form a rigid
arrangement. -/
theorem IsRigid.comap {A : Arrangement ι} (h : A.IsRigid) {f : κ → ι}
    (hf : Function.Injective f) {i₀ : ι} (hrange : Set.range f = {i₀}ᶜ) {u w : κ}
    (hu : Tangent A.center i₀ (f u)) (hw : Tangent A.center i₀ (f w))
    (honly : ∀ j, Tangent A.center i₀ (f j) → j = u ∨ j = w) (huw : u ≠ w)
    (h4 : dist (A.center (f u)) (A.center (f w)) < 4) : (A.comap f hf).IsRigid :=
  IsLocallyRigid.comp_of_tangent (p := A.center) hf hrange h hu hw honly
    (A.center_injective.ne (hf.ne huw)) h4

/-- **Adding a circle keeps rigidity** (`Option` labels). If `A` without circle `none` is
rigid and circle `none` touches two other circles, then `A` is rigid. -/
theorem IsRigid.of_erase [Finite ι] {A : Arrangement (Option ι)} (h : A.erase.IsRigid)
    {u w : ι} (hu : Tangent A.center none (some u)) (hw : Tangent A.center none (some w))
    (huw : u ≠ w) : A.IsRigid :=
  h.of_comap range_some_eq_compl_none.ge hu hw huw

/-- **Adding a circle keeps rigidity.** Adding to a rigid arrangement a circle that touches
two of its circles gives a rigid arrangement. -/
theorem IsRigid.addCircle [Finite ι] {A : Arrangement ι} (h : A.IsRigid) {c : Plane}
    (hc : ∀ i, 2 ≤ dist c (A.center i)) {u w : ι} (hu : dist c (A.center u) = 2)
    (hw : dist c (A.center w) = 2) (huw : u ≠ w) : (A.addCircle c hc).IsRigid :=
  IsRigid.of_erase (A := A.addCircle c hc) h hu hw huw

/-- **Removing a circle with two contacts keeps rigidity** (`Option` labels). If `A` is rigid
and circle `none` touches exactly two other circles, whose centers are less than `4` apart,
then `A` without circle `none` is rigid. -/
theorem IsRigid.erase {A : Arrangement (Option ι)} (h : A.IsRigid) {u w : ι}
    (hu : Tangent A.center none (some u)) (hw : Tangent A.center none (some w))
    (honly : ∀ k, Tangent A.center none (some k) → k = u ∨ k = w) (huw : u ≠ w)
    (h4 : dist (A.center (some u)) (A.center (some w)) < 4) : A.erase.IsRigid :=
  h.comap (Option.some_injective ι) range_some_eq_compl_none hu hw honly huw h4

/-- **Adding a circle keeps rigidity** (`Fin` labels). If the circles of `A` other than `i`,
renumbered in order, form a rigid arrangement, and circle `i` touches two of them, then `A`
is rigid. -/
theorem IsRigid.of_comap_succAbove {n : ℕ} {A : Arrangement (Fin (n + 1))} {i : Fin (n + 1)}
    (h : (A.comap i.succAbove Fin.succAbove_right_injective).IsRigid) {u w : Fin n}
    (hu : Tangent A.center i (i.succAbove u)) (hw : Tangent A.center i (i.succAbove w))
    (huw : u ≠ w) : A.IsRigid :=
  h.of_comap (Fin.range_succAbove i).ge hu hw huw

/-- **Removing a circle with two contacts keeps rigidity** (`Fin` labels). If `A` is rigid
and circle `i` touches exactly two other circles, whose centers are less than `4` apart, then
the remaining circles, renumbered in order, form a rigid arrangement. -/
theorem IsRigid.comap_succAbove {n : ℕ} {A : Arrangement (Fin (n + 1))} (h : A.IsRigid)
    {i : Fin (n + 1)} {u w : Fin n} (hu : Tangent A.center i (i.succAbove u))
    (hw : Tangent A.center i (i.succAbove w))
    (honly : ∀ j, Tangent A.center i (i.succAbove j) → j = u ∨ j = w) (huw : u ≠ w)
    (h4 : dist (A.center (i.succAbove u)) (A.center (i.succAbove w)) < 4) :
    (A.comap i.succAbove Fin.succAbove_right_injective).IsRigid :=
  h.comap Fin.succAbove_right_injective (Fin.range_succAbove i) hu hw honly huw h4

/-! ### Example: the rhombus -/

/-- The four vertices of a rhombus made of two equilateral triangles of side `2` that share
the edge from `0` to `2`. The first three are the vertices of `trianglePoint`. -/
noncomputable def rhombusPoint : Fin 4 → Plane :=
  ![0, 2, ⟨1, Real.sqrt 3⟩, ⟨1, -Real.sqrt 3⟩]

/-- The two vertices off the shared edge are `2 √3` apart. -/
theorem rhombusPoint_dist_two_three :
    dist (rhombusPoint 2) (rhombusPoint 3) = 2 * Real.sqrt 3 := by
  rw [Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq]
  norm_num [rhombusPoint, two_mul]

/-- Every other pair of distinct vertices is `2` apart. -/
theorem rhombusPoint_dist {i j : Fin 4} (hij : i ≠ j) (h23 : ¬(i = 2 ∧ j = 3))
    (h32 : ¬(i = 3 ∧ j = 2)) : dist (rhombusPoint i) (rhombusPoint j) = 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact (h23 ⟨rfl, rfl⟩).elim
    | exact (h32 ⟨rfl, rfl⟩).elim
    | (rw [Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq, ← h4]
       norm_num [rhombusPoint])

/-- Distinct vertices are at least `2` apart. -/
theorem two_le_dist_rhombusPoint {i j : Fin 4} (hij : i ≠ j) :
    2 ≤ dist (rhombusPoint i) (rhombusPoint j) := by
  have h3 : 1 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  by_cases h23 : i = 2 ∧ j = 3
  · obtain ⟨rfl, rfl⟩ := h23
    rw [rhombusPoint_dist_two_three]
    linarith
  by_cases h32 : i = 3 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h32
    rw [dist_comm, rhombusPoint_dist_two_three]
    linarith
  exact (rhombusPoint_dist hij h23 h32).ge

/-- The rhombus: two equilateral triangles of unit circles sharing an edge. Four circles,
five contacts (all pairs except the long diagonal). -/
noncomputable def rhombus : Arrangement (Fin 4) where
  center := rhombusPoint
  nonoverlap _ _ hij := two_le_dist_rhombusPoint hij

/-- All pairs of distinct circles of the rhombus touch, except the two circles off the shared
edge. -/
theorem rhombus_tangent {i j : Fin 4} (hij : i ≠ j) (h23 : ¬(i = 2 ∧ j = 3))
    (h32 : ¬(i = 3 ∧ j = 2)) : Tangent rhombus.center i j :=
  rhombusPoint_dist hij h23 h32

/-- The two circles off the shared edge do not touch: their centers are `2 √3` apart. -/
theorem rhombus_not_tangent_two_three : ¬Tangent rhombus.center 2 3 := by
  intro h
  have h' : 2 * Real.sqrt 3 = 2 := rhombusPoint_dist_two_three.symm.trans h
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith

/-- **The rhombus is rigid**: it is the triangle plus a circle touching two of its circles. -/
theorem rhombus_isRigid : rhombus.IsRigid := by
  have ht : (rhombus.comap Fin.castSucc (Fin.castSucc_injective 3)).IsRigid := by
    have e : rhombusPoint ∘ Fin.castSucc = trianglePoint := by
      funext i
      fin_cases i <;> rfl
    change IsLocallyRigid (rhombusPoint ∘ Fin.castSucc)
    rw [e]
    exact triangle_isRigid
  have hrange : {(3 : Fin 4)}ᶜ ⊆ Set.range (Fin.castSucc : Fin 3 → Fin 4) := by
    rw [← Fin.succAbove_last, Fin.range_succAbove]
    rfl
  exact ht.of_comap hrange (u := 0) (w := 1) (rhombus_tangent (by decide) (by decide)
    (by decide)) (rhombus_tangent (by decide) (by decide) (by decide)) (by decide)

end Arrangement

end RigidArrangements
