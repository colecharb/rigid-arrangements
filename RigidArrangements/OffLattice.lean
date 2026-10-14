import RigidArrangements.Core
import RigidArrangements.Henneberg
import RigidArrangements.Isometry
import RigidArrangements.Lattice

/-!
# Off the lattice: the hinge-and-bar lemma and the arrangement `O11`

The rigid arrangements of few circles found so far all sit on the triangular lattice (the
penny packing). This file constructs one that does not: an arrangement `O11` of eleven circles,
rigid, and not on the lattice in any position.

## The hinge-and-bar lemma

Two rigid *bodies* that share one circle, the *hinge*, can still turn about it. One more contact
between the bodies, a *bar* from a circle `x` of the first body to a circle `y` of the second,
locks the hinge (`IsLocallyRigid.of_hinge`, `Arrangement.IsRigid.of_hinge`,
`Arrangement.IsRigid.of_hinge_of_union`).

Proof. Take a small motion that keeps every contact. By rigidity each body moves congruently.
Move everything back by the rotation and translation that returns the hinge `h` and the near
end `x` of the bar to their places. Each circle of the first body keeps its distances to `h`
and `x`, so it is back in place or at its mirror image in the line `hx`; the mirror image is
too far away (`eventually_eq_of_dist_eq_of_dist_eq`). So the first body is back in place. The
far end `y` of the bar keeps its distance to `h` (same body) and to `x` (the bar), so the same
argument puts it back in place. Finally every circle of the second body keeps its distances
to `h` and `y`, so it is back in place too.

The only non-degeneracy needed is that neither end of the bar is the hinge. In particular, the
hinge and the two ends of the bar may be collinear: turning about the hinge then changes the
length of the bar to second order only, which still forbids every small motion. (If the bodies
share only the hinge and the bar is the only contact between them, the first-order rotation of
one body about the hinge is then an infinitesimal flex: such an arrangement is rigid without
being *infinitesimally* rigid.) The bodies may also share more circles than the hinge.

## The arrangement `O11`

A *chevron* is six circles forming a fan of four equilateral triangles around one circle; its
two end circles are `2 √3` apart. Take two chevrons that share an end circle `H` (the hinge)
and turn them about `H` until their other ends `X` and `Y` touch. The triangle `X H Y` has
sides `2 √3, 2 √3, 2`, so the angle at `H` is `arccos (5 / 6) ≈ 33.56°`
(`Arrangement.o11_angle_hinge`). We place it symmetrically: `X = 0`, `Y = 2`, `H = 1 + i √11`,
with the right chevron the mirror image of the left one in the line `Re z = 1`. The left chevron
is the lattice chevron `(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (-1, 2)` (centered at `(0, 1)`)
moved by the reflection `z ↦ ω conj z` with `ω = (-√33 + i √3) / 6`. Its centers are

| circle | lattice site | center |
|---|---|---|
| `0` (`X`) | `(0, 0)` | `0` |
| `1` | `(1, 0)` | `(-√33 + i √3) / 3` |
| `2` (fan center) | `(0, 1)` | `((3 - √33) + i (√3 + 3 √11)) / 6` |
| `3` | `(1, 1)` | `((1 - √33) + i (√3 + √11)) / 2` |
| `4` | `(0, 2)` | `(1 - √33 / 3) + i (√3 / 3 + √11)` |
| `5` (`H`) | `(-1, 2)` | `1 + i √11` |

and circles `6, …, 10` are the mirror images `z ↦ 2 - conj z` of circles `0, …, 4` (circle `6`
is `Y = 2`). All coordinates lie in `ℚ(√3, √11)` (we write `√33 = √3 √11`). Up to an isometry
of the plane this is the arrangement `B₁ ∪ σ(B₁)` of the research notes, which puts the hinge
at the origin.

* **Non-overlap** (`two_le_dist_o11Center`). Two circles of one chevron are as far apart as
  the corresponding lattice points. Apart from the hinge, the left chevron lies in the
  half-plane `Re z ≤ 0` and the right one in `Re z ≥ 2`.
* **Contacts** (`Arrangement.o11_tangent_iff`, `card_o11Contact`). Exactly the nine contacts
  inside each chevron and the bar `X Y`: `19 = 2 · 11 - 3` contacts.
* **Rigidity** (`Arrangement.o11_isRigid`). Each chevron is congruent to the lattice chevron,
  which is the triangle plus three Henneberg steps (`isLocallyRigid_o11Sites`). The hinge-and-bar
  lemma does the rest.
* **Off the lattice** (`Arrangement.o11_not_isLattice`). On the lattice, `X`, `Y`, `H` would be
  lattice points with `|HX| = |HY| = 2 √3` and `|XY| = 2`. But two lattice vectors of length
  `2 √3` are never `2` apart (`eNorm_sub_ne_one_of_eNorm_eq_three`). Since being on the lattice
  is invariant under isomorphism (`Arrangement.Iso.isLattice_iff`), `O11` is isomorphic to no
  arrangement on the lattice (`Arrangement.o11_not_iso_of_isLattice`).
* **A core** (`Arrangement.o11_isCore`, `o11_not_noCoresBetween`). Every circle of `O11`
  touches at least three others, so no circle can be removed by a reverse Henneberg step: `O11`
  is not obtained from a smaller rigid arrangement by adding a circle that touches two.
* **Mirror symmetry** (`Arrangement.o11_center_swap`). The reflection in `Re z = 1` swaps the
  chevrons and fixes the hinge.

## Where the polyiamond picture breaks

By the exploratory enumerations, the rigid arrangements *on the lattice* with at most twelve
circles are exactly the corner sets of saturated polyiamonds. `O11` is no polyiamond corner set
at all: it is not even on the lattice. So the lattice (polyform) count of rigid arrangements
is only a lower bound from eleven circles on.
-/

open Filter Topology ComplexConjugate

namespace RigidArrangements

/-! ### Pinning a point by its distances to two points -/

/-- **Pinning.** A point `w` close enough to `z` that has the same distances as `z` to two
distinct points `a` and `b` is `z` itself. The only other candidate is the mirror image of `z`
in the line `ab` (`eq_or_eq_reflect`), which is either `z` again or a fixed positive distance
away. -/
theorem eventually_eq_of_dist_eq_of_dist_eq {a b z : ℂ} (hab : a ≠ b) :
    ∀ᶠ w in 𝓝 z, dist w a = dist z a → dist w b = dist z b → w = z := by
  by_cases hσ : a + (b - a) * conj ((z - a) / (b - a)) = z
  · refine Eventually.of_forall fun w ha hb => ?_
    rcases eq_or_eq_reflect hab ha hb with h | h
    · exact h
    · exact h.trans hσ
  · filter_upwards [eventually_ne_nhds (Ne.symm hσ)] with w hw ha hb
    rcases eq_or_eq_reflect hab ha hb with h | h
    · exact h
    · exact absurd h hw

/-- **Pinning, for a whole placement.** Every placement `r` close enough to `p` has this
property: each point `r k` that has the same distances as `p k` to the two distinct points `a`
and `b` equals `p k`. -/
theorem eventually_forall_eq_of_dist_eq_of_dist_eq {ι : Type*} [Finite ι] {p : ι → ℂ}
    {a b : ℂ} (hab : a ≠ b) :
    ∀ᶠ r in 𝓝 p, ∀ k, dist (r k) a = dist (p k) a → dist (r k) b = dist (p k) b →
      r k = p k := by
  rw [eventually_all]
  intro k
  exact ((continuous_apply k).tendsto p).eventually (eventually_eq_of_dist_eq_of_dist_eq hab)

/-! ### The hinge-and-bar lemma -/

section Framework

variable {ι κ κ₁ κ₂ : Type*}

/-- Local rigidity of the sub-placement `p ∘ f`, read on placements of all circles: every
placement `q` close to `p` that keeps the contacts among the circles `f j` moves them
congruently. -/
theorem IsLocallyRigid.eventually_comp {p : ι → Plane} {f : κ → ι}
    (h : IsLocallyRigid (p ∘ f)) :
    ∀ᶠ q in 𝓝 p, KeepsContacts (p ∘ f) (q ∘ f) → Congruent (q ∘ f) (p ∘ f) := by
  have hc : Continuous fun q : ι → Plane => q ∘ f :=
    continuous_pi fun i => continuous_apply (f i)
  exact hc.continuousAt.eventually h

/-- **Hinge and bar.** Two locally rigid bodies, the circles `f₁ j` and the circles `f₂ j`,
together contain every circle and share the *hinge* circle `f₁ a₁ = f₂ a₂`. On its own the
pair could still turn about the hinge. A contact between a circle `f₁ x` of the first body and
a circle `f₂ y` of the second (the *bar*) locks the hinge, provided neither end of the bar has
the same center as the hinge. Then the whole placement is locally rigid.

The bodies may share more circles than the hinge, and no non-collinearity is needed: if the
hinge and the two ends of the bar are collinear, turning about the hinge still stretches or
compresses the bar (to second order), so local rigidity survives. (Infinitesimal rigidity may
not: if the bar is the only contact between the bodies, the first-order rotation of one body
about the hinge is then an infinitesimal flex.) -/
theorem IsLocallyRigid.of_hinge [Finite ι] {p : ι → Plane} {f₁ : κ₁ → ι} {f₂ : κ₂ → ι}
    (hcover : ∀ i, (∃ j, f₁ j = i) ∨ ∃ j, f₂ j = i)
    (h₁ : IsLocallyRigid (p ∘ f₁)) (h₂ : IsLocallyRigid (p ∘ f₂))
    {a₁ x : κ₁} {a₂ y : κ₂} (ha : f₁ a₁ = f₂ a₂) (hxy : Tangent p (f₁ x) (f₂ y))
    (hx : p (f₁ a₁) ≠ p (f₁ x)) (hy : p (f₂ a₂) ≠ p (f₂ y)) : IsLocallyRigid p := by
  have := Fintype.ofFinite ι
  have hd : p (f₁ x) - p (f₁ a₁) ≠ 0 := sub_ne_zero.mpr hx.symm
  -- `Φ q` is `q` moved by the rotation and translation taking `q (f₁ a₁)` to `p (f₁ a₁)` and
  -- the direction of `q (f₁ x)` to that of `p (f₁ x)`.
  let Φ : (ι → ℂ) → (ι → ℂ) := fun q k =>
    p (f₁ a₁) + (p (f₁ x) - p (f₁ a₁)) / (q (f₁ x) - q (f₁ a₁)) * (q k - q (f₁ a₁))
  have hΦp : Φ p = p := by
    funext k
    simp only [Φ]
    field_simp
    ring
  have hΦc : ContinuousAt Φ p := by
    refine continuousAt_pi.2 fun k => ?_
    have hden : (fun q : ι → ℂ => q (f₁ x) - q (f₁ a₁)) p ≠ 0 := hd
    have c1 : ContinuousAt (fun q : ι → ℂ => q (f₁ x) - q (f₁ a₁)) p := by fun_prop
    have c2 : ContinuousAt (fun q : ι → ℂ => q k - q (f₁ a₁)) p := by fun_prop
    exact continuousAt_const.add ((continuousAt_const.div c1 hden).mul c2)
  have hT : Tendsto Φ (𝓝 p) (𝓝 p) := by
    have := hΦc.tendsto
    rwa [hΦp] at this
  have hpin₁ := hT.eventually (eventually_forall_eq_of_dist_eq_of_dist_eq (p := p) hx)
  have hpin₂ := hT.eventually (eventually_forall_eq_of_dist_eq_of_dist_eq (p := p) (ha ▸ hy))
  filter_upwards [hpin₁, hpin₂, h₁.eventually_comp, h₂.eventually_comp] with q hq₁ hq₂ hr₁ hr₂ hk
  have hc₁ := hr₁ fun i j hij => hk (f₁ i) (f₁ j) hij
  have hc₂ := hr₂ fun i j hij => hk (f₂ i) (f₂ j) hij
  rw [congruent_iff_dist_eq] at hc₁ hc₂
  simp only [Function.comp_apply] at hc₁ hc₂
  -- normalize `q` by the rotation and translation `Φ q`
  have hqx : dist (q (f₁ x)) (q (f₁ a₁)) = dist (p (f₁ x)) (p (f₁ a₁)) := hc₁ x a₁
  have hq0 : q (f₁ x) - q (f₁ a₁) ≠ 0 := by
    intro h0
    rw [dist_eq_norm, h0, norm_zero, eq_comm, dist_eq_zero] at hqx
    exact hx hqx.symm
  have hρn : ‖(p (f₁ x) - p (f₁ a₁)) / (q (f₁ x) - q (f₁ a₁))‖ = 1 := by
    rw [norm_div, ← dist_eq_norm, ← dist_eq_norm, hqx, div_self]
    exact dist_ne_zero.mpr hx.symm
  have hΦdist : ∀ k l, dist (Φ q k) (Φ q l) = dist (q k) (q l) := by
    intro k l
    simp only [Φ, dist_eq_norm]
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hρn, one_mul, sub_sub_sub_cancel_right]
  have hΦa : Φ q (f₁ a₁) = p (f₁ a₁) := by simp [Φ]
  have hΦx : Φ q (f₁ x) = p (f₁ x) := by
    simp only [Φ]
    field_simp
    ring
  -- distances to a center that is already back in place
  have hfix : ∀ k l, Φ q l = p l → dist (Φ q k) (p l) = dist (q k) (q l) := fun k l hl => by
    rw [← hl, hΦdist]
  -- the first body is back in place
  have pin₁ : ∀ j, Φ q (f₁ j) = p (f₁ j) := fun j =>
    hq₁ (f₁ j) (by rw [hfix _ _ hΦa]; exact hc₁ j a₁) (by rw [hfix _ _ hΦx]; exact hc₁ j x)
  -- so is the far end of the bar: it keeps its distances to the hinge and to the near end
  have pinY : Φ q (f₂ y) = p (f₂ y) := by
    refine hq₁ (f₂ y) ?_ ?_
    · rw [hfix _ _ hΦa, ha]
      exact hc₂ y a₂
    · rw [hfix _ _ hΦx, dist_comm, dist_comm (p (f₂ y))]
      exact (hk _ _ hxy).trans hxy.symm
  -- hence so is the second body
  have pin₂ : ∀ j, Φ q (f₂ j) = p (f₂ j) := by
    intro j
    refine hq₂ (f₂ j) ?_ ?_
    · rw [hfix _ _ hΦa, ha]
      exact hc₂ j a₂
    · rw [hfix _ _ pinY]
      exact hc₂ j y
  have pin : ∀ k, Φ q k = p k := by
    intro k
    rcases hcover k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact pin₁ j
    · exact pin₂ j
  rw [congruent_iff_dist_eq]
  intro i j
  rw [← hΦdist, pin, pin]

end Framework

namespace Arrangement

variable {ι κ₁ κ₂ : Type*}

/-- **Hinge and bar**, for arrangements. The circles `f₁ j` and the circles `f₂ j` form two
rigid sub-arrangements (*bodies*) that together contain every circle and share the *hinge*
circle `f₁ a₁ = f₂ a₂`. If some circle `f₁ x ≠ f₁ a₁` of the first body touches some circle
`f₂ y ≠ f₂ a₂` of the second (the *bar*), the whole arrangement is rigid. -/
theorem IsRigid.of_hinge [Finite ι] {A : Arrangement ι} {f₁ : κ₁ → ι} {f₂ : κ₂ → ι}
    {hf₁ : Function.Injective f₁} {hf₂ : Function.Injective f₂}
    (h₁ : (A.comap f₁ hf₁).IsRigid) (h₂ : (A.comap f₂ hf₂).IsRigid)
    (hcover : ∀ i, (∃ j, f₁ j = i) ∨ ∃ j, f₂ j = i)
    {a₁ x : κ₁} {a₂ y : κ₂} (ha : f₁ a₁ = f₂ a₂) (hxy : Tangent A.center (f₁ x) (f₂ y))
    (hx : a₁ ≠ x) (hy : a₂ ≠ y) : A.IsRigid :=
  IsLocallyRigid.of_hinge hcover h₁ h₂ ha hxy (A.center_injective.ne (hf₁.ne hx))
    (A.center_injective.ne (hf₂.ne hy))

/-- **Hinge and bar**, with the bodies given as sets of circles. If the circles of `S₁` and
the circles of `S₂` form rigid arrangements, `S₁ ∪ S₂` contains every circle, the circle `h`
lies in both, and some `x ∈ S₁` touches some `y ∈ S₂` with `x, y ≠ h`, then the whole
arrangement is rigid. -/
theorem IsRigid.of_hinge_of_union [Finite ι] {A : Arrangement ι} {S₁ S₂ : Set ι}
    (h₁ : (A.comap ((↑) : S₁ → ι) Subtype.val_injective).IsRigid)
    (h₂ : (A.comap ((↑) : S₂ → ι) Subtype.val_injective).IsRigid)
    (hcover : S₁ ∪ S₂ = Set.univ) {h x y : ι} (hh₁ : h ∈ S₁) (hh₂ : h ∈ S₂) (hx : x ∈ S₁)
    (hy : y ∈ S₂) (hxy : Tangent A.center x y) (hxh : x ≠ h) (hyh : y ≠ h) : A.IsRigid := by
  refine h₁.of_hinge h₂ (fun i => ?_) (a₁ := ⟨h, hh₁⟩) (a₂ := ⟨h, hh₂⟩) (x := ⟨x, hx⟩)
    (y := ⟨y, hy⟩) rfl hxy (fun e => hxh (congrArg Subtype.val e).symm)
    (fun e => hyh (congrArg Subtype.val e).symm)
  have hi : i ∈ S₁ ∪ S₂ := hcover ▸ Set.mem_univ i
  rcases hi with hi | hi
  · exact Or.inl ⟨⟨i, hi⟩, rfl⟩
  · exact Or.inr ⟨⟨i, hi⟩, rfl⟩

end Arrangement

/-! ### The arrangement `O11` -/

/-- The chevron on the lattice: a fan of four triangles around the circle at `(0, 1)`, listed
in an order in which each circle from the fourth on touches two earlier ones. Circle `0`, at
`(0, 0)`, and circle `5`, at `(-1, 2)`, are the two ends of the fan; they are `2 √3` apart. -/
def o11Sites : Fin 6 → ℤ × ℤ :=
  ![(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (-1, 2)]

/-- The six sites of the chevron are distinct. -/
theorem o11Sites_injective : Function.Injective o11Sites := by
  decide

/-- The unit complex number `ω = (-√33 + i √3) / 6`, with `√33` written as `√3 √11`. -/
noncomputable def o11Turn : ℂ :=
  ⟨-(Real.sqrt 3 * Real.sqrt 11) / 6, Real.sqrt 3 / 6⟩

/-- `ω` is a unit: `33 / 36 + 3 / 36 = 1`. -/
theorem norm_o11Turn : ‖o11Turn‖ = 1 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h11 := Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [o11Turn]
  linear_combination (Real.sqrt 11 ^ 2 / 36 + 1 / 36) * h3 + (3 / 36) * h11

/-- The reflection `z ↦ ω conj z` of the plane in a line through `0`, which places the left
chevron of `O11`. -/
noncomputable def o11Place (z : Plane) : Plane :=
  o11Turn * conj z

/-- The reflection `z ↦ 2 - conj z` in the vertical line `Re z = 1`, which swaps the two
chevrons of `O11`. -/
noncomputable def o11Mirror (z : Plane) : Plane :=
  2 - conj z

/-- `o11Place` is an isometry. -/
theorem dist_o11Place (z w : Plane) : dist (o11Place z) (o11Place w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm, o11Place, o11Place, ← mul_sub, ← map_sub, norm_mul,
    norm_o11Turn, one_mul, Complex.norm_conj]

/-- `o11Mirror` is an isometry. -/
theorem dist_o11Mirror (z w : Plane) : dist (o11Mirror z) (o11Mirror w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm, o11Mirror, o11Mirror, sub_sub_sub_cancel_left, ← map_sub,
    Complex.norm_conj, ← dist_eq_norm, ← dist_eq_norm, dist_comm]

/-- `o11Mirror` is an involution. -/
theorem o11Mirror_o11Mirror (z : Plane) : o11Mirror (o11Mirror z) = z := by
  rw [o11Mirror, o11Mirror, map_sub, map_ofNat, Complex.conj_conj]
  ring

/-- The six circles of the left chevron of `O11`: the lattice chevron `o11Sites`, placed by
`o11Place`. -/
noncomputable def o11Left (k : Fin 6) : Plane :=
  o11Place (latticePoint (o11Sites k))

/-- The six circles of the right chevron of `O11`: the mirror image of the left chevron in the
line `Re z = 1`. -/
noncomputable def o11Right (k : Fin 6) : Plane :=
  o11Mirror (o11Left k)

/-- Two circles of the left chevron are as far apart as their lattice sites. -/
theorem dist_o11Left (a b : Fin 6) :
    dist (o11Left a) (o11Left b) = dist (latticePoint (o11Sites a)) (latticePoint (o11Sites b)) :=
  dist_o11Place _ _

/-- Two circles of the right chevron are as far apart as their lattice sites. -/
theorem dist_o11Right (a b : Fin 6) :
    dist (o11Right a) (o11Right b) =
      dist (latticePoint (o11Sites a)) (latticePoint (o11Sites b)) :=
  (dist_o11Mirror _ _).trans (dist_o11Left a b)

/-- The real part of a circle of the left chevron. -/
theorem o11Left_re (k : Fin 6) :
    (o11Left k).re = -(Real.sqrt 3 * Real.sqrt 11) / 6 * (2 * (o11Sites k).1 + (o11Sites k).2)
      + (o11Sites k).2 / 2 := by
  have h3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [o11Left, o11Place, o11Turn, latticePoint, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  linear_combination ((o11Sites k).2 : ℝ) / 6 * h3

/-- The imaginary part of a circle of the left chevron. -/
theorem o11Left_im (k : Fin 6) :
    (o11Left k).im = Real.sqrt 3 / 6 * (2 * (o11Sites k).1 + (o11Sites k).2)
      + Real.sqrt 11 * (o11Sites k).2 / 2 := by
  have h3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [o11Left, o11Place, o11Turn, latticePoint, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  linear_combination ((o11Sites k).2 : ℝ) * Real.sqrt 11 / 6 * h3

/-- The far end `X` of the left chevron is at `0`. -/
theorem o11Left_zero : o11Left 0 = 0 := by
  apply Complex.ext
  · rw [o11Left_re]
    norm_num [o11Sites]
  · rw [o11Left_im]
    norm_num [o11Sites]

/-- The far end `Y` of the right chevron is at `2`. -/
theorem o11Right_zero : o11Right 0 = 2 := by
  rw [o11Right, o11Left_zero, o11Mirror, map_zero, sub_zero]

/-- The hinge `H`, the common circle of the two chevrons, is at `1 + i √11`. -/
theorem o11Left_five : o11Left 5 = ⟨1, Real.sqrt 11⟩ := by
  apply Complex.ext
  · rw [o11Left_re]
    norm_num [o11Sites]
  · rw [o11Left_im]
    norm_num [o11Sites]

/-- The hinge lies on the mirror line, so it belongs to both chevrons. -/
theorem o11Right_five : o11Right 5 = o11Left 5 := by
  rw [o11Right, o11Left_five, o11Mirror]
  apply Complex.ext <;> norm_num

/-- `√33 ≥ 3`, in the form used below. -/
private theorem three_le_sqrt_three_mul_sqrt_eleven : 3 ≤ Real.sqrt 3 * Real.sqrt 11 := by
  have h1 : 1 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : 3 ≤ Real.sqrt 11 := Real.le_sqrt_of_sq_le (by norm_num)
  nlinarith

/-- Every circle of the left chevron other than the hinge lies in the half-plane `Re z ≤ 0`. -/
theorem o11Left_re_nonpos (k : Fin 5) : (o11Left k.castSucc).re ≤ 0 := by
  have hs := three_le_sqrt_three_mul_sqrt_eleven
  have hk : 0 ≤ (o11Sites k.castSucc).1 ∧ 0 ≤ (o11Sites k.castSucc).2 := by
    fin_cases k <;> decide
  have ha : (0 : ℝ) ≤ (o11Sites k.castSucc).1 := by exact_mod_cast hk.1
  have hb : (0 : ℝ) ≤ (o11Sites k.castSucc).2 := by exact_mod_cast hk.2
  rw [o11Left_re]
  nlinarith

/-- Every circle of the right chevron other than the hinge lies in the half-plane `Re z ≥ 2`. -/
theorem two_le_o11Right_re (k : Fin 5) : 2 ≤ (o11Right k.castSucc).re := by
  have := o11Left_re_nonpos k
  simp only [o11Right, o11Mirror, Complex.sub_re, Complex.conj_re]
  norm_num
  linarith

/-- Away from the far end `X`, the left chevron lies in the open half-plane `Re z < 0`. -/
theorem o11Left_re_neg {k : Fin 5} (hk : k ≠ 0) : (o11Left k.castSucc).re < 0 := by
  have h1 : 1 ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : 3 < Real.sqrt 11 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hs : 3 < Real.sqrt 3 * Real.sqrt 11 := by nlinarith
  have hk' : 0 ≤ (o11Sites k.castSucc).1 ∧ 0 ≤ (o11Sites k.castSucc).2 ∧
      0 < 2 * (o11Sites k.castSucc).1 + (o11Sites k.castSucc).2 := by
    fin_cases k
    · exact absurd rfl hk
    all_goals decide
  have ha : (0 : ℝ) ≤ (o11Sites k.castSucc).1 := by exact_mod_cast hk'.1
  have hb : (0 : ℝ) ≤ (o11Sites k.castSucc).2 := by exact_mod_cast hk'.2.1
  have hab : (0 : ℝ) < 2 * (o11Sites k.castSucc).1 + (o11Sites k.castSucc).2 := by
    exact_mod_cast hk'.2.2
  rw [o11Left_re]
  nlinarith

/-- Away from the far end `Y`, the right chevron lies in the open half-plane `Re z > 2`. -/
theorem two_lt_o11Right_re {k : Fin 5} (hk : k ≠ 0) : 2 < (o11Right k.castSucc).re := by
  have := o11Left_re_neg hk
  simp only [o11Right, o11Mirror, Complex.sub_re, Complex.conj_re]
  norm_num
  linarith

/-- The distance between two points is at least the difference of their real parts. -/
private theorem re_sub_re_le_dist (z w : Plane) : w.re - z.re ≤ dist z w := by
  rw [dist_eq_norm]
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, abs_sub_comm]
  exact le_abs_self _

/-- Points in the half-planes `Re z ≤ 0` and `Re w ≥ 2` are at least `2` apart. -/
private theorem two_le_dist_of_re {z w : Plane} (hz : z.re ≤ 0) (hw : 2 ≤ w.re) :
    2 ≤ dist z w :=
  le_trans (by linarith) (re_sub_re_le_dist z w)

/-- The centers of `O11`: circles `0, …, 5` are the left chevron (circle `5` is the hinge), and
circles `6, …, 10` are the right chevron without the hinge. -/
noncomputable def o11Center : Fin 11 → Plane :=
  Fin.append o11Left fun k : Fin 5 => o11Right k.castSucc

/-- The labels in `O11` of the circles of the left chevron. -/
def o11LeftIdx : Fin 6 → Fin 11 :=
  Fin.castAdd 5

/-- The labels in `O11` of the circles of the right chevron: the hinge is circle `5`. -/
def o11RightIdx : Fin 6 → Fin 11 :=
  Fin.lastCases (Fin.castAdd 5 (Fin.last 5)) (Fin.natAdd 6)

/-- Distinct circles of the left chevron have distinct labels. -/
theorem o11LeftIdx_injective : Function.Injective o11LeftIdx := by
  decide

/-- Distinct circles of the right chevron have distinct labels. -/
theorem o11RightIdx_injective : Function.Injective o11RightIdx := by
  decide

/-- Every circle of `O11` is in one of the two chevrons. -/
theorem o11Idx_cover (i : Fin 11) : (∃ j, o11LeftIdx j = i) ∨ ∃ j, o11RightIdx j = i := by
  revert i
  decide

/-- The circles labeled by `o11LeftIdx` form the left chevron. -/
theorem o11Center_left (k : Fin 6) : o11Center (o11LeftIdx k) = o11Left k :=
  Fin.append_left _ _ k

/-- The circles labeled by `o11RightIdx` form the right chevron. -/
theorem o11Center_right (k : Fin 6) : o11Center (o11RightIdx k) = o11Right k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [o11RightIdx, Fin.lastCases_last, o11Center, Fin.append_left]
    exact o11Right_five.symm
  | cast k =>
    simp only [o11RightIdx, Fin.lastCases_castSucc, o11Center, Fin.append_right]

/-- No two circles of `O11` overlap. Two circles of the same chevron are as far apart as the
corresponding lattice points. A circle of the left chevron other than the hinge lies in the
half-plane `Re z ≤ 0`, and a circle of the right chevron other than the hinge in `Re z ≥ 2`. -/
theorem two_le_dist_o11Center {i j : Fin 11} (hij : i ≠ j) :
    2 ≤ dist (o11Center i) (o11Center j) := by
  have hL : ∀ a b, a ≠ b → 2 ≤ dist (o11Left a) (o11Left b) := fun a b hab => by
    rw [dist_o11Left]
    exact two_le_dist_latticePoint (o11Sites_injective.ne hab)
  have hR : ∀ a b, a ≠ b → 2 ≤ dist (o11Right a) (o11Right b) := fun a b hab => by
    rw [dist_o11Right]
    exact two_le_dist_latticePoint (o11Sites_injective.ne hab)
  have h5 : o11Left (Fin.last 5) = o11Right (Fin.last 5) := o11Right_five.symm
  have hLR : ∀ a b, o11LeftIdx a ≠ o11RightIdx b → 2 ≤ dist (o11Left a) (o11Right b) := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      rw [h5]
      refine hR _ _ fun e => hab ?_
      rw [← e]
      decide
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [← h5]
        exact hL _ _ (Fin.castSucc_ne_last a)
      | cast b => exact two_le_dist_of_re (o11Left_re_nonpos a) (two_le_o11Right_re b)
  rcases o11Idx_cover i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases o11Idx_cover j with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
    simp only [o11Center_left, o11Center_right]
  · exact hL a b fun e => hij (by rw [e])
  · exact hLR a b hij
  · rw [dist_comm]
    exact hLR b a hij.symm
  · exact hR a b fun e => hij (by rw [e])

namespace Arrangement

/-- **The off-lattice arrangement `O11`.** Two chevrons of six circles (fans of four triangles)
share an end circle, the hinge `H = 1 + i √11`, and their other ends `X = 0` and `Y = 2` touch.
The two chevrons are mirror images of each other in the line `Re z = 1`. -/
noncomputable def o11 : Arrangement (Fin 11) where
  center := o11Center
  nonoverlap _ _ hij := two_le_dist_o11Center hij

end Arrangement

/-! ### Combinatorial data: the contacts and the mirror relabeling -/

/-- The contacts of `O11`, as a decidable relation: two circles of the same chevron whose
lattice sites are adjacent, or the bar between the far ends `X` (circle `0`) and `Y`
(circle `6`). -/
def o11Contact (i j : Fin 11) : Prop :=
  (∃ a b, o11LeftIdx a = i ∧ o11LeftIdx b = j ∧ eNorm (o11Sites a - o11Sites b) = 1) ∨
    (∃ a b, o11RightIdx a = i ∧ o11RightIdx b = j ∧ eNorm (o11Sites a - o11Sites b) = 1) ∨
    (i = 0 ∧ j = 6) ∨ (i = 6 ∧ j = 0)

instance : DecidableRel o11Contact := fun i j => by
  unfold o11Contact
  infer_instance

/-- `O11` has `19 = 2 · 11 - 3` contacts: nine in each chevron, and the bar. -/
theorem card_o11Contact :
    (Finset.univ.filter fun e : Fin 11 × Fin 11 => e.1 < e.2 ∧ o11Contact e.1 e.2).card = 19 := by
  decide

/-- The relabeling that swaps the two chevrons of `O11` and fixes the hinge. -/
def o11Swap : Equiv.Perm (Fin 11) :=
  Function.Involutive.toPerm ![6, 7, 8, 9, 10, 5, 0, 1, 2, 3, 4] (by
    intro i
    revert i
    decide)

/-- `o11Swap` takes the left chevron to the right one. -/
theorem o11Swap_left (k : Fin 6) : o11Swap (o11LeftIdx k) = o11RightIdx k := by
  revert k
  decide

/-- `o11Swap` takes the right chevron to the left one. -/
theorem o11Swap_right (k : Fin 6) : o11Swap (o11RightIdx k) = o11LeftIdx k := by
  revert k
  decide

/-! ### `O11` is rigid -/

/-- One Henneberg step on the lattice: if the first `n` points of `v` form a locally rigid
placement and the last point touches two distinct earlier points, then all of `v` is locally
rigid. -/
private theorem isLocallyRigid_latticePoint_snoc {n : ℕ} {v : Fin (n + 1) → ℤ × ℤ}
    (h : IsLocallyRigid (latticePoint ∘ v ∘ Fin.castSucc)) (u w : Fin n)
    (huw : v u.castSucc ≠ v w.castSucc) (hu : eNorm (v (Fin.last n) - v u.castSucc) = 1)
    (hw : eNorm (v (Fin.last n) - v w.castSucc) = 1) : IsLocallyRigid (latticePoint ∘ v) := by
  have hrange : {Fin.last n}ᶜ ⊆ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
    rw [← Fin.succAbove_last, Fin.range_succAbove]
  exact IsLocallyRigid.of_comp_of_tangent hrange h ((tangent_latticePoint_iff _ _).2 hu)
    ((tangent_latticePoint_iff _ _).2 hw) (latticePoint_injective.ne huw)

/-- **The lattice chevron is rigid**: three mutually touching circles, then three Henneberg
steps. -/
theorem isLocallyRigid_o11Sites : IsLocallyRigid (latticePoint ∘ o11Sites) := by
  have h3 : IsLocallyRigid (latticePoint ∘ ![((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)]) := by
    refine isLocallyRigid_of_forall_tangent fun i j hij => (tangent_latticePoint_iff _ _).2 ?_
    revert i j
    decide
  have h4 : IsLocallyRigid (latticePoint ∘ ![((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)]) := by
    refine isLocallyRigid_latticePoint_snoc ?_ 1 2 (by decide) (by decide) (by decide)
    convert h3 using 2
    funext i
    fin_cases i <;> rfl
  have h5 : IsLocallyRigid
      (latticePoint ∘ ![((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1), (0, 2)]) := by
    refine isLocallyRigid_latticePoint_snoc ?_ 2 3 (by decide) (by decide) (by decide)
    convert h4 using 2
    funext i
    fin_cases i <;> rfl
  refine isLocallyRigid_latticePoint_snoc ?_ 2 4 (by decide) (by decide) (by decide)
  convert h5 using 2
  funext i
  fin_cases i <;> rfl

namespace Arrangement

/-- The left chevron of `O11` is rigid: it is congruent to the lattice chevron. -/
theorem o11_comap_left_isRigid : (o11.comap o11LeftIdx o11LeftIdx_injective).IsRigid := by
  have hc : Congruent (o11.center ∘ o11LeftIdx) (latticePoint ∘ o11Sites) := by
    rw [congruent_iff_dist_eq]
    intro a b
    simp only [Function.comp_apply]
    exact (congrArg₂ dist (o11Center_left a) (o11Center_left b)).trans (dist_o11Left a b)
  exact (isLocallyRigid_iff_of_congruent hc).mpr isLocallyRigid_o11Sites

/-- The right chevron of `O11` is rigid: it is congruent to the lattice chevron. -/
theorem o11_comap_right_isRigid : (o11.comap o11RightIdx o11RightIdx_injective).IsRigid := by
  have hc : Congruent (o11.center ∘ o11RightIdx) (latticePoint ∘ o11Sites) := by
    rw [congruent_iff_dist_eq]
    intro a b
    simp only [Function.comp_apply]
    exact (congrArg₂ dist (o11Center_right a) (o11Center_right b)).trans (dist_o11Right a b)
  exact (isLocallyRigid_iff_of_congruent hc).mpr isLocallyRigid_o11Sites

/-- The bar: the far ends `X = 0` (circle `0`) and `Y = 2` (circle `6`) of the two chevrons
touch. -/
theorem o11_tangent_zero_six : Tangent o11.center 0 6 := by
  change dist (o11Center (o11LeftIdx 0)) (o11Center (o11RightIdx 0)) = 2
  rw [o11Center_left, o11Center_right, o11Left_zero, o11Right_zero, dist_eq_norm, zero_sub,
    norm_neg]
  norm_num

/-- **`O11` is rigid**, by the hinge-and-bar lemma: the two chevrons are rigid, share the hinge
`H` (circle `5`), and the bar `X Y` (circles `0` and `6`) locks the hinge. -/
theorem o11_isRigid : o11.IsRigid :=
  o11_comap_left_isRigid.of_hinge o11_comap_right_isRigid o11Idx_cover (a₁ := 5)
    (a₂ := 5) (x := 0) (y := 0) (by decide) o11_tangent_zero_six (by decide) (by decide)

/-- The hinge `H` is `2 √3` away from each far end: `|HX|² = 12` (and `|HY|² = 12`). -/
theorem o11_dist_sq_five_zero : dist (o11.center 5) (o11.center 0) ^ 2 = 12 := by
  change dist (o11Center (o11LeftIdx 5)) (o11Center (o11LeftIdx 0)) ^ 2 = 12
  rw [o11Center_left, o11Center_left, dist_o11Left, dist_latticePoint_sq]
  norm_num [o11Sites, eNorm]

/-- `|HY|² = 12`. -/
theorem o11_dist_sq_five_six : dist (o11.center 5) (o11.center 6) ^ 2 = 12 := by
  change dist (o11Center (o11RightIdx 5)) (o11Center (o11RightIdx 0)) ^ 2 = 12
  rw [o11Center_right, o11Center_right, dist_o11Right, dist_latticePoint_sq]
  norm_num [o11Sites, eNorm]

/-- **The hinge angle.** The angle `X H Y` between the two chevrons at the hinge is
`arccos (5 / 6) ≈ 33.56°`: the triangle `X H Y` has sides `2 √3, 2 √3, 2`. -/
theorem o11_angle_hinge :
    EuclideanGeometry.angle (o11.center 0) (o11.center 5) (o11.center 6) =
      Real.arccos (5 / 6) := by
  have hX : o11.center 0 = 0 := o11Left_zero
  have hH : o11.center 5 = ⟨1, Real.sqrt 11⟩ := o11Left_five
  have hY : o11.center 6 = 2 := o11Right_zero
  have hn : ‖o11.center 0 - o11.center 5‖ * ‖o11.center 6 - o11.center 5‖ = 12 := by
    have h1 := o11_dist_sq_five_zero
    have h2 := o11_dist_sq_five_six
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm, dist_comm (o11.center 6)]
    have he := (sq_eq_sq₀ dist_nonneg dist_nonneg).1 (h1.trans h2.symm)
    rw [← he, ← sq, h1]
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle, vsub_eq_sub, vsub_eq_sub, hn,
    Complex.inner, hX, hH, hY]
  have h11 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 11 by norm_num)
  congr 1
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.zero_re, Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat]
  linear_combination h11 / 12

end Arrangement

/-! ### `O11` is not on the lattice -/

/-- The six lattice vectors of Eisenstein norm `3`, i.e. of length `2 √3`. -/
private def eNormThreeList : List (ℤ × ℤ) :=
  [(1, 1), (2, -1), (1, -2), (-1, -1), (-2, 1), (-1, 2)]

private theorem mem_eNormThreeList {v : ℤ × ℤ} (h : eNorm v = 3) : v ∈ eNormThreeList := by
  obtain ⟨a, b⟩ := v
  simp only [eNorm] at h
  have ha1 : a ≤ 2 := by nlinarith [sq_nonneg (a + 2 * b)]
  have ha2 : -2 ≤ a := by nlinarith [sq_nonneg (a + 2 * b)]
  have hb1 : b ≤ 2 := by nlinarith [sq_nonneg (2 * a + b)]
  have hb2 : -2 ≤ b := by nlinarith [sq_nonneg (2 * a + b)]
  revert h
  interval_cases a <;> interval_cases b <;> decide

/-- **Two lattice vectors of length `2 √3` are never `2` apart.** The lattice vectors of
Eisenstein norm `3` are the six vectors `±(1, 1)`, `±(2, -1)`, `±(1, -2)`, and the difference
of two of them has norm `0`, `3`, `9` or `12`, never `1`. (Conceptually:
`a² + ab + b² ≡ (a - b)² mod 3`, so the vectors of norm `3` have `a ≡ b mod 3`; then so does
their difference, whose norm is therefore divisible by `3`.) -/
theorem eNorm_sub_ne_one_of_eNorm_eq_three {v w : ℤ × ℤ} (hv : eNorm v = 3)
    (hw : eNorm w = 3) : eNorm (v - w) ≠ 1 := by
  have key : ∀ v ∈ eNormThreeList, ∀ w ∈ eNormThreeList, eNorm (v - w) ≠ 1 := by
    decide
  exact key v (mem_eNormThreeList hv) w (mem_eNormThreeList hw)

namespace Arrangement

/-- **`O11` is not on the triangular lattice**, in any position. An isometry carrying `O11`
into the lattice would carry the hinge `H` and the far ends `X`, `Y` to lattice points with
`|HX| = |HY| = 2 √3` and `|XY| = 2`, which `eNorm_sub_ne_one_of_eNorm_eq_three` rules out. -/
theorem o11_not_isLattice : ¬ o11.IsLattice := by
  rintro ⟨g, f, hf⟩
  have hd : ∀ i j, dist (latticePoint (f i)) (latticePoint (f j)) =
      dist (o11.center i) (o11.center j) := fun i j => by
    rw [← hf, ← hf, g.dist_map]
  have e3 : ∀ j, dist (o11.center 5) (o11.center j) ^ 2 = 12 → eNorm (f 5 - f j) = 3 := by
    intro j hj
    have := dist_latticePoint_sq (f 5) (f j)
    rw [hd, hj] at this
    exact_mod_cast (by linarith : ((eNorm (f 5 - f j) : ℤ) : ℝ) = 3)
  have e1 : eNorm (f 0 - f 6) = 1 :=
    (tangent_latticePoint_iff _ _).1 ((hd 0 6).trans o11_tangent_zero_six)
  have := eNorm_sub_ne_one_of_eNorm_eq_three (e3 6 o11_dist_sq_five_six)
    (e3 0 o11_dist_sq_five_zero)
  rw [show f 5 - f 6 - (f 5 - f 0) = f 0 - f 6 by abel] at this
  exact this e1

/-- An arrangement isomorphic to one on the lattice is on the lattice. -/
theorem IsLattice.of_iso {ι κ : Type*} [Finite ι] {A : Arrangement ι} {B : Arrangement κ}
    (h : A.Iso B) (hB : B.IsLattice) : A.IsLattice := by
  obtain ⟨e, g, hg⟩ := iso_iff_exists_isometry.mp h
  obtain ⟨g', f, hf⟩ := hB
  exact ⟨g.trans g', f ∘ e, fun i => by simp [← hg, hf]⟩

/-- **Being on the lattice is invariant under isomorphism.** -/
theorem Iso.isLattice_iff {ι κ : Type*} [Finite ι] {A : Arrangement ι} {B : Arrangement κ}
    (h : A.Iso B) : A.IsLattice ↔ B.IsLattice := by
  have : Finite κ := Finite.of_equiv ι h.choose
  exact ⟨IsLattice.of_iso h.symm, IsLattice.of_iso h⟩

/-- Arrangements built from lattice points are on the lattice. -/
theorem isLattice_ofLattice (l : List (ℤ × ℤ)) (hl : l.Nodup) : (ofLattice l hl).IsLattice :=
  ⟨AffineIsometryEquiv.refl ℝ Plane, l.get, fun _ => rfl⟩

/-- **`O11` is not isomorphic to any arrangement on the lattice.** -/
theorem o11_not_iso_of_isLattice {κ : Type*} {B : Arrangement κ} (hB : B.IsLattice) :
    ¬ o11.Iso B := fun h => o11_not_isLattice (IsLattice.of_iso h hB)

/-- In particular `O11` is isomorphic to no arrangement `ofLattice l`. -/
theorem o11_not_iso_ofLattice (l : List (ℤ × ℤ)) (hl : l.Nodup) : ¬ o11.Iso (ofLattice l hl) :=
  o11_not_iso_of_isLattice (isLattice_ofLattice l hl)

/-! ### The contacts of `O11` -/

/-- **The contacts of `O11`.** Two circles touch exactly when they belong to the same chevron
and sit at adjacent lattice sites of it, or they are the far ends `X` and `Y`. Every other pair
across the two chevrons is more than `2` apart, because the chevrons lie in the half-planes
`Re z ≤ 0` and `Re z ≥ 2`, touching these lines only at `X = 0` and `Y = 2` (and at the shared
hinge). -/
theorem o11_tangent_iff (i j : Fin 11) : Tangent o11.center i j ↔ o11Contact i j := by
  have hL : ∀ a b, Tangent o11.center (o11LeftIdx a) (o11LeftIdx b) ↔
      eNorm (o11Sites a - o11Sites b) = 1 := fun a b => by
    change dist (o11Center _) (o11Center _) = 2 ↔ _
    rw [o11Center_left, o11Center_left, dist_o11Left, tangent_latticePoint_iff]
  have hR : ∀ a b, Tangent o11.center (o11RightIdx a) (o11RightIdx b) ↔
      eNorm (o11Sites a - o11Sites b) = 1 := fun a b => by
    change dist (o11Center _) (o11Center _) = 2 ↔ _
    rw [o11Center_right, o11Center_right, dist_o11Right, tangent_latticePoint_iff]
  have h5 : o11LeftIdx (Fin.last 5) = o11RightIdx (Fin.last 5) := by decide
  -- across the chevrons, away from the hinge, only `X` and `Y` touch
  have hLR : ∀ a b : Fin 5, Tangent o11.center (o11LeftIdx a.castSucc) (o11RightIdx b.castSucc) →
      a = 0 ∧ b = 0 := by
    intro a b hab
    change dist (o11Center _) (o11Center _) = 2 at hab
    rw [o11Center_left, o11Center_right] at hab
    by_contra hne
    have key := re_sub_re_le_dist (o11Left a.castSucc) (o11Right b.castSucc)
    rcases not_and_or.mp hne with ha | hb
    · linarith [o11Left_re_neg ha, two_le_o11Right_re b]
    · linarith [o11Left_re_nonpos a, two_lt_o11Right_re hb]
  constructor
  · intro hij
    rcases o11Idx_cover i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases o11Idx_cover j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact Or.inl ⟨a, b, rfl, rfl, (hL a b).1 hij⟩
    · induction a using Fin.lastCases with
      | last =>
        rw [h5] at hij
        exact Or.inr (Or.inl ⟨_, b, h5.symm, rfl, (hR _ b).1 hij⟩)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          rw [← h5] at hij
          exact Or.inl ⟨_, _, rfl, h5, (hL _ _).1 hij⟩
        | cast b =>
          obtain ⟨rfl, rfl⟩ := hLR a b hij
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · induction b using Fin.lastCases with
      | last =>
        rw [h5] at hij
        exact Or.inr (Or.inl ⟨a, _, rfl, h5.symm, (hR a _).1 hij⟩)
      | cast b =>
        induction a using Fin.lastCases with
        | last =>
          rw [← h5] at hij
          exact Or.inl ⟨_, _, h5, rfl, (hL _ _).1 hij⟩
        | cast a =>
          obtain ⟨rfl, rfl⟩ := hLR b a (tangent_comm.mp hij)
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨a, b, rfl, rfl, (hR a b).1 hij⟩)
  · rintro (⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (hL a b).2 h
    · exact (hR a b).2 h
    · exact o11_tangent_zero_six
    · exact tangent_comm.mp o11_tangent_zero_six

/-- Three neighbours of each circle of `O11`. -/
private def o11Nbr : Fin 11 → Fin 3 → Fin 11 :=
  ![![1, 2, 6], ![0, 2, 3], ![0, 1, 3], ![1, 2, 4], ![2, 3, 5], ![2, 4, 10],
    ![0, 7, 8], ![6, 8, 9], ![6, 7, 9], ![7, 8, 10], ![5, 8, 9]]

/-- **Every circle of `O11` touches at least three others.** -/
theorem o11_three_le_contacts (w : Fin 11) : ∃ u v t : Fin 11, u ≠ v ∧ u ≠ t ∧ v ≠ t ∧
    o11.contactGraph.Adj w u ∧ o11.contactGraph.Adj w v ∧ o11.contactGraph.Adj w t := by
  have hn : ∀ w k, w ≠ o11Nbr w k ∧ o11Contact w (o11Nbr w k) := by decide
  have hd : ∀ w, o11Nbr w 0 ≠ o11Nbr w 1 ∧ o11Nbr w 0 ≠ o11Nbr w 2 ∧
      o11Nbr w 1 ≠ o11Nbr w 2 := by decide
  have ha : ∀ k, o11.contactGraph.Adj w (o11Nbr w k) := fun k =>
    ⟨(hn w k).1, (o11_tangent_iff _ _).2 (hn w k).2⟩
  exact ⟨_, _, _, (hd w).1, (hd w).2.1, (hd w).2.2, ha 0, ha 1, ha 2⟩

/-- **`O11` is a core**: no circle touches exactly two others, so no circle can be removed by a
reverse Henneberg step. `O11` is not obtained from a smaller rigid arrangement by adding one
circle that touches two. -/
theorem o11_isCore : o11.IsCore := by
  rintro w ⟨u, v, -, hadj, -⟩
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := o11_three_le_contacts w
  rcases (hadj a).1 ha with rfl | rfl <;> rcases (hadj b).1 hb with rfl | rfl <;>
    rcases (hadj c).1 hc with rfl | rfl <;> simp_all

end Arrangement

/-- A rigid core with `11` circles: `NoCoresBetween a b` fails whenever `a ≤ 11 ≤ b`. -/
theorem o11_not_noCoresBetween {a b : ℕ} (ha : a ≤ 11) (hb : 11 ≤ b) : ¬ NoCoresBetween a b :=
  fun h => by
    obtain ⟨w, hw⟩ := h 11 Arrangement.o11 ha hb Arrangement.o11_isRigid
    exact Arrangement.o11_isCore w hw

namespace Arrangement

/-! ### The mirror symmetry of `O11` -/

/-- **`O11` is mirror-symmetric.** The reflection `o11Mirror` in the line `Re z = 1` carries
circle `i` to circle `o11Swap i`: it swaps the two chevrons and fixes the hinge. -/
theorem o11_center_swap (i : Fin 11) : o11.center (o11Swap i) = o11Mirror (o11.center i) := by
  rcases o11Idx_cover i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · change o11Center _ = o11Mirror (o11Center _)
    rw [o11Swap_left, o11Center_left, o11Center_right, o11Right]
  · change o11Center _ = o11Mirror (o11Center _)
    rw [o11Swap_right, o11Center_left, o11Center_right, o11Right, o11Mirror_o11Mirror]

end Arrangement

end RigidArrangements
