import RigidArrangements.Rigidity

/-!
# Flexes and structural consequences of rigidity

To show that an arrangement is *not* rigid we exhibit a *flex*: an explicit continuous motion
that keeps every contact but changes some distance. This file builds the flexes used in the
project and derives from them the basic structure of rigid arrangements.

## Flexes

All flexes here move one part `S` of the circles by rigid motions of the plane and keep the
other circles fixed.

* `IsLocallyRigid.eventually_dist_move`: the general principle, for any placement in a
  pseudometric space. If moving `S` never breaks a contact between `S` and the rest, local
  rigidity forces every distance between `S` and the rest to stay the same for small motions.
* `eq_zero_or_eq_zero_of_eventually_norm_exp_mul_add`: the one fact about the plane behind the
  flexes. A point moving on a circle changes its distance to every point other than the center.
* `Arrangement.not_isRigid_of_rotate` (**rotation flex**): if every contact between `S` and the
  rest goes to one circle `c`, rotate `S` about `c`.
* `Arrangement.not_isRigid_of_shear` (**shear flex**): if every contact between `S` and the rest
  is a translate of one vector `d`, translate `S` along a circle of radius `2`. Every circle of
  `S` that touches the rest then rolls around its partner, all in step. This is a genuine
  flex as soon as some `i ∈ S` and `k ∉ S` have `center i - center k ≠ d`.
* `Arrangement.not_isRigid_of_shear_of_three_le`: with at least three circles, the shear flex
  only needs `S` and the rest to be nonempty.
* `Arrangement.not_isRigid_of_isolated`: if no contact leaves `S`, and both `S` and the rest
  are nonempty, slide `S` away.

Apart from the `three_le` variant, none of this needs finitely many circles.

## Structure of rigid arrangements

* `Arrangement.IsRigid.connected`: the contact graph of a rigid arrangement is connected.
* `Arrangement.IsRigid.connected_induce_ne`: a rigid arrangement has no *cut circle*. Removing
  any one circle leaves the contact graph connected, if at least one circle is left.
* `Arrangement.IsRigid.touchesTwo`: in a rigid arrangement of at least three circles, every
  circle touches at least two others. So the clause "each circle touches two others" of the
  original problem is a consequence of rigidity, which is why `IsRigid` does not include it.
* `Arrangement.isRigid_two_iff`: two circles are rigid exactly when they touch.
* `Arrangement.isRigid_three_iff`, `Arrangement.iso_triangle_of_isRigid`: three circles are
  rigid exactly when they touch pairwise, so the triangle is the only rigid arrangement of
  three circles.
* `Arrangement.not_isRigid_of_iso_cycleGraph_four`: four circles whose contact graph is a
  4-cycle are never rigid. Their centers form a rhombus, which the shear flex deforms. For
  example, four circles centered at the corners of a square of side `2` have a 4-cycle as
  contact graph, so they are not rigid (this instance is not stated separately in Lean).
-/

open Filter Topology

namespace RigidArrangements

section Framework

variable {ι P X : Type*} [PseudoMetricSpace P] [TopologicalSpace X]

/-- Along any path of placements that starts at a locally rigid `p` and keeps every
tangency of `p`, the placement stays congruent to `p` for a short while. -/
theorem IsLocallyRigid.eventually_congruent {p : ι → P} (h : IsLocallyRigid p)
    {q : X → ι → P} {x₀ : X} (hq : ContinuousAt q x₀) (h₀ : q x₀ = p)
    (hk : ∀ᶠ x in 𝓝 x₀, KeepsContacts p (q x)) : ∀ᶠ x in 𝓝 x₀, Congruent (q x) p := by
  have hq' : Tendsto q (𝓝 x₀) (𝓝 p) := h₀ ▸ hq
  filter_upwards [hq'.eventually h, hk] with x hx hkx using hx hkx

/-- **Moving one part.** Let `m θ` be a family of distance-preserving maps of `P`, depending
continuously on the parameter `θ` and equal to the identity at `θ = 0`. Apply `m θ` to the
points of `S` and keep the others fixed. If this never breaks a tangency between `S` and its
complement, and `p` is locally rigid, then for all small `θ` the motion keeps every distance
between a point of `S` and a point outside `S`. -/
theorem IsLocallyRigid.eventually_dist_move {p : ι → P} (h : IsLocallyRigid p) (S : Set ι)
    (m : ℝ → P → P) (hm : ∀ θ x y, dist (m θ x) (m θ y) = dist x y)
    (hc : ∀ x, ContinuousAt (fun θ => m θ x) 0) (h₀ : ∀ x, m 0 x = x)
    (hcross : ∀ θ i j, i ∈ S → j ∉ S → Tangent p i j → dist (m θ (p i)) (p j) = 2) :
    ∀ᶠ θ in 𝓝 (0 : ℝ), ∀ i ∈ S, ∀ k ∉ S, dist (m θ (p i)) (p k) = dist (p i) (p k) := by
  classical
  let q : ℝ → ι → P := fun θ l => if l ∈ S then m θ (p l) else p l
  have hq0 : q 0 = p := funext fun l => by by_cases hl : l ∈ S <;> simp [q, hl, h₀]
  have hqc : ContinuousAt q 0 := continuousAt_pi.2 fun l => by
    by_cases hl : l ∈ S
    · simpa [q, hl] using hc (p l)
    · simpa [q, hl] using continuousAt_const
  have hk : ∀ θ, KeepsContacts p (q θ) := by
    intro θ a b hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · simp only [Tangent, q, ha, hb, ↓reduceIte, hm]; exact hab
    · simp only [Tangent, q, ha, hb, ↓reduceIte]; exact hcross θ a b ha hb hab
    · simp only [Tangent, q, ha, hb, ↓reduceIte]
      rw [dist_comm]; exact hcross θ b a hb ha (tangent_comm.mp hab)
    · simp only [Tangent, q, ha, hb, ↓reduceIte]; exact hab
  filter_upwards [h.eventually_congruent hqc hq0 (Eventually.of_forall hk)] with θ hθ i hi k hkS
  simpa [q, hi, hkS] using (congruent_iff_dist_eq.mp hθ) i k

end Framework

/-- Rotating `a` by every small angle `θ` and then adding `b` cannot keep `‖a + b‖` unchanged,
unless `a = 0` or `b = 0`. Geometrically: when a point moves on a circle of radius `‖a‖`, its
distance to a point other than the center changes. -/
theorem eq_zero_or_eq_zero_of_eventually_norm_exp_mul_add {a b : ℂ}
    (h : ∀ᶠ θ : ℝ in 𝓝 0, ‖Complex.exp (θ * Complex.I) * a + b‖ = ‖a + b‖) :
    a = 0 ∨ b = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  set θ : ℝ := min (ε / 2) 1
  have hθ0 : 0 < θ := by positivity
  have hθε : dist θ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hθ0]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  have hθε' : dist (-θ) 0 < ε := by
    rwa [Real.dist_eq, sub_zero, abs_neg, ← sub_zero θ, ← Real.dist_eq]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 ((min_le_right _ _).trans_lt (by linarith [Real.pi_gt_three]))
  have hcos : Real.cos θ < 1 := by
    nlinarith [Real.cos_sq_add_sin_sq θ, Real.cos_le_one θ]
  -- squared norms in coordinates
  have expand : ∀ φ : ℝ, ‖Complex.exp (φ * Complex.I) * a + b‖ ^ 2 =
      Complex.normSq a + Complex.normSq b + 2 * (Real.cos φ * (a.re * b.re + a.im * b.im) +
        Real.sin φ * (a.re * b.im - a.im * b.re)) := by
    intro φ
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination (a.re * a.re + a.im * a.im) * Real.cos_sq_add_sin_sq φ
  have e0 : ‖a + b‖ ^ 2 = Complex.normSq a + Complex.normSq b +
      2 * (a.re * b.re + a.im * b.im) := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  have e1 : ‖Complex.exp (θ * Complex.I) * a + b‖ ^ 2 = ‖a + b‖ ^ 2 := by rw [hball hθε]
  have e2 : ‖Complex.exp ((-θ : ℝ) * Complex.I) * a + b‖ ^ 2 = ‖a + b‖ ^ 2 := by
    rw [hball hθε']
  rw [expand, e0] at e1 e2
  rw [Real.cos_neg, Real.sin_neg] at e2
  have hB : a.re * b.im - a.im * b.re = 0 := by
    have : Real.sin θ * (a.re * b.im - a.im * b.re) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hsin.ne'
  have hA : a.re * b.re + a.im * b.im = 0 := by
    have : (Real.cos θ - 1) * (a.re * b.re + a.im * b.im) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hcos.ne)
  have hab : Complex.normSq a * Complex.normSq b = 0 := by
    simp only [Complex.normSq_apply]
    linear_combination (a.re * b.re + a.im * b.im) * hA + (a.re * b.im - a.im * b.re) * hB
  rcases mul_eq_zero.mp hab with h | h
  · exact Or.inl (Complex.normSq_eq_zero.mp h)
  · exact Or.inr (Complex.normSq_eq_zero.mp h)

namespace Arrangement

variable {ι : Type*} (A : Arrangement ι)

/-- With at least three circles, there is always a third circle besides `a` and `b`. -/
private theorem exists_ne_ne [Finite ι] (hn : 3 ≤ Nat.card ι) (a b : ι) :
    ∃ k, k ≠ a ∧ k ≠ b :=
  ENat.exists_ne_ne_of_three_le (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast hn) a b

/-- **Rotation flex.** If every contact between the circles of `S` and the circles outside `S`
goes to one circle `c ∉ S`, then rotating `S` about the center of `c` keeps all contacts. If
moreover some circle `k ∉ S` other than `c` exists, this changes the distance between `k` and
the circles of `S`, so the arrangement is not rigid. -/
theorem not_isRigid_of_rotate (S : Set ι) (c : ι) (hc : c ∉ S)
    (hcross : ∀ i j, i ∈ S → j ∉ S → A.contactGraph.Adj i j → j = c)
    {i k : ι} (hi : i ∈ S) (hk : k ∉ S) (hkc : k ≠ c) : ¬ A.IsRigid := by
  intro h
  have hev := IsLocallyRigid.eventually_dist_move h S
    (fun θ x => A.center c + Complex.exp (θ * Complex.I) * (x - A.center c))
    (fun θ x y => by
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul,
        Complex.norm_exp_ofReal_mul_I, one_mul, sub_sub_sub_cancel_right])
    (fun x => by fun_prop) (fun x => by simp)
    (fun θ a b ha hb hab => by
      have hbc := hcross a b ha hb ⟨fun e => hb (e ▸ ha), hab⟩
      rw [hbc] at hab ⊢
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        ← dist_eq_norm]
      exact hab)
  have key : ∀ᶠ θ : ℝ in 𝓝 0, ‖Complex.exp (θ * Complex.I) * (A.center i - A.center c) +
      (A.center c - A.center k)‖ = ‖(A.center i - A.center c) + (A.center c - A.center k)‖ := by
    filter_upwards [hev] with θ hθ
    have := hθ i hi k hk
    rw [dist_eq_norm, dist_eq_norm] at this
    rw [sub_add_sub_cancel, ← this]
    congr 1
    ring
  rcases eq_zero_or_eq_zero_of_eventually_norm_exp_mul_add key with h1 | h1
  · exact (fun e => hc (e ▸ hi) : i ≠ c) (A.center_injective (sub_eq_zero.mp h1))
  · exact hkc (A.center_injective (sub_eq_zero.mp h1)).symm

/-- **Shear flex.** Suppose every contact between a circle `i ∈ S` and a circle `j ∉ S` is the
same vector: `center i - center j = d` for one fixed `d`. For a unit complex number `ζ` close
to `1`, translating `S` by `(ζ - 1) d` turns each such contact vector `d` into `ζ d`, of the
same length, so all contacts are kept. Suppose some `i ∈ S` and `k ∉ S` have
`center i - center k ≠ d`. If `d ≠ 0`, their distance changes, so the arrangement is not
rigid. If `d = 0`, no contact leaves `S` at all (tangent centers are distinct), and the proof
uses the shear along `d' = 2 (center i - center k)` instead (see also
`not_isRigid_of_isolated`). -/
theorem not_isRigid_of_shear (S : Set ι) (d : ℂ)
    (hcross : ∀ i j, i ∈ S → j ∉ S → A.contactGraph.Adj i j → A.center i - A.center j = d)
    {i k : ι} (hi : i ∈ S) (hk : k ∉ S) (hik : A.center i - A.center k ≠ d) : ¬ A.IsRigid := by
  have hne : ∀ {a b}, a ∈ S → b ∉ S → a ≠ b := fun ha hb e => hb (e ▸ ha)
  -- if `d = 0` there is no cross contact at all, and any other `d` works as well
  wlog hd : d ≠ 0 generalizing d
  · rw [not_not] at hd
    subst hd
    refine this (2 * (A.center i - A.center k)) (fun a b ha hb hab => ?_) ?_ ?_
    · exact absurd (sub_eq_zero.mp (hcross a b ha hb hab)) (A.center_injective.ne hab.ne)
    · intro e
      exact hik (by linear_combination -e)
    · exact mul_ne_zero two_ne_zero hik
  intro h
  have hev := IsLocallyRigid.eventually_dist_move h S
    (fun θ x => x + (Complex.exp (θ * Complex.I) - 1) * d)
    (fun θ x y => dist_add_right _ _ _) (fun x => by fun_prop) (fun x => by simp)
    (fun θ a b ha hb hab => by
      have had := hcross a b ha hb ⟨hne ha hb, hab⟩
      rw [dist_eq_norm, show A.center a + (Complex.exp (θ * Complex.I) - 1) * d - A.center b =
          Complex.exp (θ * Complex.I) * d by linear_combination had,
        norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← had, ← dist_eq_norm]
      exact hab)
  have key : ∀ᶠ θ : ℝ in 𝓝 0, ‖Complex.exp (θ * Complex.I) * d +
      (A.center i - A.center k - d)‖ = ‖d + (A.center i - A.center k - d)‖ := by
    filter_upwards [hev] with θ hθ
    have := hθ i hi k hk
    rw [dist_eq_norm, dist_eq_norm] at this
    rw [add_sub_cancel, ← this]
    congr 1
    ring
  rcases eq_zero_or_eq_zero_of_eventually_norm_exp_mul_add key with h1 | h1
  · exact hd h1
  · exact hik (sub_eq_zero.mp h1)

/-- **Translation flex.** If no circle of `S` touches a circle outside `S`, and both parts are
nonempty, then sliding `S` away is a flex: the arrangement is not rigid. -/
theorem not_isRigid_of_isolated (S : Set ι)
    (hcross : ∀ i j, i ∈ S → j ∉ S → ¬ A.contactGraph.Adj i j)
    {i k : ι} (hi : i ∈ S) (hk : k ∉ S) : ¬ A.IsRigid :=
  A.not_isRigid_of_shear S 0 (fun a b ha hb hab => absurd hab (hcross a b ha hb)) hi hk
    (sub_ne_zero.mpr (A.center_injective.ne fun e => hk (e ▸ hi)))

/-- The shear flex for three or more circles: if all contacts between `S` and its complement
are translates of one vector `d`, and both parts are nonempty, the arrangement is not rigid.
(A third circle supplies a pair `i ∈ S`, `k ∉ S` with `center i - center k ≠ d`.) -/
theorem not_isRigid_of_shear_of_three_le [Finite ι] (hn : 3 ≤ Nat.card ι) (S : Set ι) (d : ℂ)
    (hcross : ∀ i j, i ∈ S → j ∉ S → A.contactGraph.Adj i j → A.center i - A.center j = d)
    {i k : ι} (hi : i ∈ S) (hk : k ∉ S) : ¬ A.IsRigid := by
  by_cases hik : A.center i - A.center k = d
  · obtain ⟨m, hmi, hmk⟩ := exists_ne_ne hn i k
    by_cases hm : m ∈ S
    · refine A.not_isRigid_of_shear S d hcross hm hk fun h => hmi (A.center_injective ?_)
      linear_combination h - hik
    · refine A.not_isRigid_of_shear S d hcross hi hm fun h => hmk (A.center_injective ?_)
      linear_combination hik - h
  · exact A.not_isRigid_of_shear S d hcross hi hk hik

/-! ### Connectivity -/

/-- **A rigid arrangement is connected**: any two circles are joined by a chain of contacts.
Otherwise the circles reachable from one of them could slide away from the rest. -/
theorem IsRigid.preconnected {A : Arrangement ι} (h : A.IsRigid) :
    A.contactGraph.Preconnected := by
  intro u v
  by_contra huv
  exact A.not_isRigid_of_isolated {w | A.contactGraph.Reachable u w}
    (fun a b ha hb hab => hb (SimpleGraph.Reachable.trans ha hab.reachable))
    (SimpleGraph.Reachable.refl u) huv h

/-- The contact graph of a nonempty rigid arrangement is connected. This includes one circle
and two tangent circles, the only nonempty rigid arrangements of fewer than three circles. -/
theorem IsRigid.connected [Nonempty ι] {A : Arrangement ι} (h : A.IsRigid) :
    A.contactGraph.Connected :=
  ⟨h.preconnected⟩

/-- **No cut circle.** In a rigid arrangement, removing any one circle `v` leaves the remaining
contact graph preconnected. Otherwise one of the pieces could be rotated about `v`. -/
theorem IsRigid.preconnected_induce_ne {A : Arrangement ι} (h : A.IsRigid) (v : ι) :
    (A.contactGraph.induce {w | w ≠ v}).Preconnected := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  by_contra hxy
  let G := A.contactGraph.induce {w | w ≠ v}
  refine A.not_isRigid_of_rotate {w | ∃ hw : w ≠ v, G.Reachable ⟨x, hx⟩ ⟨w, hw⟩} v
    (fun ⟨hv, _⟩ => hv rfl) (fun a b ⟨ha, hra⟩ hb hab => ?_) ⟨hx, .refl _⟩
    (fun ⟨_, hr⟩ => hxy hr) hy h
  by_contra hbv
  exact hb ⟨hbv, hra.trans (SimpleGraph.Adj.reachable (G := G) (u := ⟨a, ha⟩) (v := ⟨b, hbv⟩)
    hab)⟩

/-- **No cut circle**, connected form: if a rigid arrangement has at least two circles,
removing any one circle leaves a connected contact graph. -/
theorem IsRigid.connected_induce_ne [Nontrivial ι] {A : Arrangement ι} (h : A.IsRigid)
    (v : ι) : (A.contactGraph.induce {w | w ≠ v}).Connected := by
  obtain ⟨w, hw⟩ := exists_ne v
  have : Nonempty {w | w ≠ v} := ⟨⟨w, hw⟩⟩
  exact ⟨h.preconnected_induce_ne v⟩

/-! ### Every circle touches two others -/

/-- Every circle touches at least two other circles. This is the clause "each circle touches
two others" of the original problem statement. By `IsRigid.touchesTwo` it is automatic for
rigid arrangements of at least three circles, which is why it is not part of `IsRigid`. -/
def TouchesTwo : Prop :=
  ∀ i, ∃ j k, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧ Tangent A.center i j ∧ Tangent A.center i k

/-- **Rigidity forces two contacts per circle.** In a rigid arrangement of at least three
circles, every circle touches at least two others: a circle with at most one contact could
be rolled around its neighbour (or slid away), changing its distance to a third circle. -/
theorem IsRigid.touchesTwo [Finite ι] {A : Arrangement ι} (h : A.IsRigid)
    (hn : 3 ≤ Nat.card ι) : A.TouchesTwo := by
  intro i
  by_contra hcon
  -- a circle `c ≠ i` such that every contact of `i` is with `c`
  obtain ⟨c, hci, hc⟩ : ∃ c, c ≠ i ∧ ∀ j, A.contactGraph.Adj i j → j = c := by
    by_cases hex : ∃ j, A.contactGraph.Adj i j
    · obtain ⟨j, hj⟩ := hex
      refine ⟨j, hj.ne.symm, fun m hm => ?_⟩
      by_contra hmj
      exact hcon ⟨m, j, hmj, hm.ne, hj.ne, hm.2, hj.2⟩
    · push Not at hex
      obtain ⟨c, hc, -⟩ := exists_ne_ne hn i i
      exact ⟨c, hc, fun j hj => absurd hj (hex j)⟩
  obtain ⟨k, hki, hkc⟩ := exists_ne_ne hn i c
  refine A.not_isRigid_of_rotate {i} c hci (fun a b ha _ hab => hc b ?_) (Set.mem_singleton i)
    hki hkc h
  rwa [Set.mem_singleton_iff.mp ha] at hab

/-! ### Two and three circles -/

/-- **Two circles are rigid exactly when they touch.** -/
theorem isRigid_two_iff (A : Arrangement (Fin 2)) : A.IsRigid ↔ Tangent A.center 0 1 := by
  refine ⟨fun h => ?_, A.isRigid_pair⟩
  by_contra h01
  have key : ∀ a b : Fin 2, a = 0 → b ≠ 0 → b = 1 := by decide
  refine A.not_isRigid_of_isolated {0} (fun a b ha hb hab => h01 ?_) (Set.mem_singleton 0)
    (k := 1) (by simp) h
  rw [Set.mem_singleton_iff] at ha hb
  rw [← ha, ← key a b ha hb]
  exact hab.2

/-- **Three circles are rigid exactly when they touch pairwise.** -/
theorem isRigid_three_iff (A : Arrangement (Fin 3)) :
    A.IsRigid ↔ ∀ i j, i ≠ j → Tangent A.center i j := by
  refine ⟨fun h i j hij => ?_, A.isRigid_of_forall_tangent⟩
  obtain ⟨j', k', hjk, hij', hik', hj', hk'⟩ := h.touchesTwo (by simp) i
  have key : ∀ i j j' k' : Fin 3, i ≠ j → j' ≠ k' → i ≠ j' → i ≠ k' → j = j' ∨ j = k' := by
    decide
  rcases key i j j' k' hij hjk hij' hik' with rfl | rfl
  · exact hj'
  · exact hk'

/-- **The only rigid arrangement of three circles is the triangle**, up to isomorphism. -/
theorem iso_triangle_of_isRigid {A : Arrangement (Fin 3)} (h : A.IsRigid) : A.Iso triangle :=
  iso_triangle_of_forall_tangent ((isRigid_three_iff A).mp h)

/-! ### Four circles in a cycle -/

/-- Four vectors of length `2` that add up to zero cancel in pairs: one of `x + y`, `x + z`,
`x + w` vanishes. (Their conjugates `4 / x, …` also add up to zero, so the third elementary
symmetric function of `x, y, z, w` vanishes as well.) -/
private theorem mul_add_eq_zero_of_norm_eq_two {x y z w : ℂ} (hx : ‖x‖ = 2) (hy : ‖y‖ = 2)
    (hz : ‖z‖ = 2) (hw : ‖w‖ = 2) (hs : x + y + z + w = 0) :
    (x + y) * (x + z) * (x + w) = 0 := by
  have hc : ∀ u : ℂ, ‖u‖ = 2 → u * starRingEnd ℂ u = 4 := fun u hu => by
    rw [Complex.mul_conj', hu]
    norm_num
  have hs' : starRingEnd ℂ x + starRingEnd ℂ y + starRingEnd ℂ z + starRingEnd ℂ w = 0 := by
    simp only [← map_add, hs, map_zero]
  linear_combination x ^ 2 * hs + x * y * z * w / 4 * hs' - y * z * w / 4 * hc x hx -
    x * z * w / 4 * hc y hy - x * y * w / 4 * hc z hz - x * y * z / 4 * hc w hw

/-- **A 4-cycle is never rigid.** If the contact graph is a cycle of length four (each circle
touches exactly its two cyclic neighbours), then the four centers form a rhombus of side `2`,
and the rhombus can be sheared: translate two adjacent circles along a circle of radius `2`. -/
theorem not_isRigid_of_iso_cycleGraph_four (e : A.contactGraph ≃g SimpleGraph.cycleGraph 4) :
    ¬ A.IsRigid := by
  have hadj : ∀ x y, A.contactGraph.Adj x y ↔ (SimpleGraph.cycleGraph 4).Adj (e x) (e y) :=
    fun x y => e.map_adj_iff.symm
  have hT : ∀ s t : Fin 4, (SimpleGraph.cycleGraph 4).Adj s t →
      ‖A.center (e.symm s) - A.center (e.symm t)‖ = 2 := fun s t hst => by
    rw [← dist_eq_norm]
    exact ((hadj _ _).mpr (by simpa using hst)).2
  have hne : ∀ s t : Fin 4, s ≠ t → A.center (e.symm s) - A.center (e.symm t) ≠ 0 :=
    fun s t hst => sub_ne_zero.mpr (A.center_injective.ne (e.symm.injective.ne hst))
  -- the centers form a parallelogram: `center 1 - center 0 = center 2 - center 3`
  have hpar : A.center (e.symm 1) - A.center (e.symm 0) =
      A.center (e.symm 2) - A.center (e.symm 3) := by
    have := mul_add_eq_zero_of_norm_eq_two (hT 1 0 (by decide)) (hT 2 1 (by decide))
      (hT 3 2 (by decide)) (hT 0 3 (by decide)) (by ring)
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (by linear_combination h) (hne 2 0 (by decide))
      · linear_combination h
    · exact absurd (by linear_combination h) (hne 1 3 (by decide))
  -- shear the circles `1, 2` along the direction of the contact `1 - 0`
  have key : ∀ s t : Fin 4, (s = 1 ∨ s = 2) → ¬ (t = 1 ∨ t = 2) →
      (SimpleGraph.cycleGraph 4).Adj s t → (s = 1 ∧ t = 0) ∨ (s = 2 ∧ t = 3) := by
    decide
  refine A.not_isRigid_of_shear {x | e x = 1 ∨ e x = 2}
    (A.center (e.symm 1) - A.center (e.symm 0)) (fun x y hx hy hxy => ?_) (i := e.symm 1)
    (k := e.symm 3) (by simp) (by simp) ?_
  · have hx' : x = e.symm (e x) := (e.symm_apply_apply x).symm
    have hy' : y = e.symm (e y) := (e.symm_apply_apply y).symm
    rcases key (e x) (e y) hx hy ((hadj x y).mp hxy) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hx', hy', h1, h2]
    · rw [hx', hy', h1, h2, hpar]
  · intro h
    exact hne 0 3 (by decide) (by linear_combination h)

end Arrangement

end RigidArrangements
