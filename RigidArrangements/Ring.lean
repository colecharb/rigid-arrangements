import RigidArrangements.OffLatticeExamples
import RigidArrangements.Cluster

/-!
# `R14`, the first lattice hinge-and-bar core, and the arithmetic of a three-body ring

`RigidArrangements/OffLatticeExamples.lean` glues two lattice bodies at a hinge and locks them
with a bar, at the angle the bar forces. That construction does not care whether the resulting
angle is a lattice angle. This file uses it in the one case where the angle *is* a lattice
angle, which produces an arrangement that lies on a single lattice and is nevertheless not
built by Henneberg steps: the core `R14` of `docs/formula-plan.md`. It then sets out the
arithmetic a three-body *ring* needs, and settles the question of whether a ring can be
certified by a single decidable test.

## `R14`

The port norms are `(p, q) = (3, 4)`, so `D = 4 · 3 · 4 - (3 + 4 - 1)² = 12` and the hinge
angle is `arccos (6 / (2 √12)) = 30°`. By `docs/offlattice.md` §4.3, `(3, 4)` is one of the
three pairs for which *every* realization lies on a lattice, and indeed the turn of body 2
comes out as `hbAlpha (1, 1) (0, 2) 1 = 1` (`r14_turn`): the constructor leaves body 2 exactly
where it stood. So `R14` is the arrangement `hbArr` of two lattice bodies

* body 1: the six-circle chevron `r14L₁`, hinge at `0`, bar end `u = (1, 1)` at norm `3`;
* body 2: the nine-circle body `0 :: r14L₂`, bar end `v = (0, 2)` at norm `4`,

with every centre at a lattice point (`r14_center_eq`, `r14_isLattice`).

`R14` and `Q13` are the same construction with one body changed, as `docs/offlattice.md` says
("the same 9-circle body with arms (3, 4) instead of (4, 4)"), and in this normalization they
share body 2 *on the nose*: `r14L₂` is the list `ex13L₂` reordered into a build order, and the
bar end `v = (0, 2)` is the same. Only body 1 changes, from the five-circle trapezoid `ex13L₁`
with arm norm `4` to the six-circle chevron `r14L₁` with arm norm `3`. That drops `D` from `15`
to `12 = 3 · 2²`, which is what turns a type-I off-lattice angle into a lattice one, and raises
`n` from `13` to `14`.

The numbers, all checked by the kernel on the site list `r14Sites`:

| | |
|---|---|
| circles | `14 = 6 + 9 - 1` |
| contacts | `25 = 9 + 15 + 1 = 2 · 14 - 3`, so isostatic (`r14Sites_contacts`) |
| triangles | `11 = 4 + 7` |
| minimum degree | `3` (`r14Sites_degree`) |
| contacts across the two bodies | exactly one, the bar (`r14_cross_contact`) |
| triangles containing the bar | none (`r14_bar_no_triangle`) |

Two consequences of the degree bound are what make `R14` interesting.

* **`R14` is a core** (`r14_isCore`): a removable circle touches exactly two others, and here
  every circle touches at least three.
* **`R14` is not reachable by Henneberg steps in any order.** A build order starts from two
  touching circles (one contact) and adds `n - 2` circles, each touching at least two earlier
  ones, so it realizes at least `1 + 2 (n - 2) = 2 n - 3` contacts. `R14` has exactly `2 n - 3`,
  so every step would have to add exactly two contacts, and the last circle added would have
  degree exactly `2`. There is none. (So `latticeBuilt r14Sites = false` is not an accident of
  the order chosen. The argument itself is prose here, not Lean: the repository has no
  predicate for "lies in the Henneberg closure".)

`R14` therefore needs a gluing certificate rather than a build certificate, and it has one in
two forms: `r14_isRigid`, straight from the hinge-and-bar lemma through `hbArr_isRigid`, and
`r14_isRigid_of_cluster`, assembled from the merging calculus of
`RigidArrangements/Cluster.lean` by a single application of **R2**
(`Arrangement.RigidIn.union_of_ring`) to the two bodies and the bar. The second form is the one
that says `R14` is *constructible*: it is a merge of three clusters sharing three distinct
circles, with no geometry beyond that.

## Three bodies in a ring

A ring has three bodies `B₁`, `B₂`, `B₃` pairwise sharing one hinge and no bar. Normalize
`B₁`'s frame, put `H₁₂` at `0` and `H₁₃` at `eis α`, and let `a = N α`, `b = N (H₂₃ - H₁₂)` and
`c = N (H₂₃ - H₁₃)` be the three hinge norms. Then `D = ringD a b c` is sixteen times the
squared area of the hinge triangle, and the third hinge sits at `ringApex = τ · eis α / a`,
where `τ = ringTau a b c σ = ((a + b - c) + σ i √D) / 2`.

The question is whether the no-overlap test for a ring reduces, as it does for a hinge and a
bar (`hbCheck`), to one decidable sign test on numbers `A + B √M` with `A`, `B` rational and `M`
a fixed integer. The worry is that a ring can need two independent square roots: `T14` has
`D = 32`, so `√D = 4 √2`, and its coordinates live in `ℚ(√2, √3)`.

**It does reduce, and the two radicals never meet.** The reason is the pivot identity

* `conj_ringApex_mul`: `conj H₂₃ · (H₂₃ - H₁₃) = ringTau b c a σ`,

which says that the relative turn of `B₂` and `B₃` is *again* a ring turn, for the same `D`
with the hinge norms rotated to `(b, c, a)`. Explicitly, the turn of `B₂` relative to `B₁` is
`H₂₃ / eis β` and the turn of `B₃` relative to `B₁` is `(H₂₃ - H₁₃) / eis γ`, so the turn of
`B₃` relative to `B₂` is `ringTau b c a σ · eis β · conj (eis γ) / (b c)` — the same shape, and
`ringD` is symmetric (`ringD_rotate`, `ringD_swap`), so the same radical. Feeding such a number
an Eisenstein integer and taking a real part gives

* `ringTau_mul_eis_re`: `(τ · eis z).re = ((a + b - c) (2 z.1 + z.2)) / 4 - σ z.2 √(3 D) / 4`,

a rational number plus a rational multiple of the *single* radical `√(3 D)`. Every squared
distance in a ring is built from such real parts, so every squared distance lies in `ℚ(√(3D))`
and `nonnegSqrt _ _ (3 * ringD a b c)` decides it, exactly as in `hbCheck`. For `T14`,
`3 D = 96` and `√96 = 4 √6`: the coordinates need `√2` and `√3` separately, but the squared
distances need only `√6`. (Check against the coordinates in `docs/offlattice.md`: `c₀ = (0, 0)`
and `c₈ = (4 + √6, √2)` are `24 + 8 √6` apart squared, and `c₈` and
`c₁₀ = (4 + 2√6/3, -2√3/3 - 2√2)` are `20 + 4 √6` apart squared — both in `ℚ(√6)`, and the
second is a `B₂`–`B₃` pair.)

Hinge-and-bar is the degenerate ring whose third body is the two-circle rod, and the
discriminants agree on the nose: `ringD_one_eq_hbD`.

What is **not** here: the ring constructor itself. Building `ringCheck` / `ringArr` to match
`hbCheck` / `hbArr` needs the two turns as definitions, their unit-modulus proofs, three
distance formulas and a soundness proof for the assembled arrangement, whose rigidity would
come from R2; and `T14` itself needs that constructor (or fourteen explicit coordinates in
`ℚ(√2, √3)`). This file stops at the arithmetic, which is the part that was in doubt.

## Main results

* `r14L₁`, `r14L₂`, `r14Sites`, `r14Check`, `Arrangement.r14`, `Arrangement.r14_isRigid`.
* `r14_turn`, `Arrangement.r14_center_eq`, `Arrangement.r14_isLattice`,
  `Arrangement.r14_tangent_iff`.
* `r14Sites_contacts`, `r14Sites_degree`, `Arrangement.r14_isCore`, `Arrangement.r14_bar`,
  `Arrangement.r14_cross_contact`, `Arrangement.r14_bar_no_triangle`,
  `Arrangement.r14_no_cross_triangle`.
* `Arrangement.r14_body1_isRigid`, `Arrangement.r14_body2_isRigid`,
  `Arrangement.r14_isRigid_of_cluster`.
* `ringD`, `ringD_eq_four_mul_sub`, `ringD_rotate`, `ringD_swap`, `ringD_one_eq_hbD`,
  `t14_ringD`, `ring15_ringD`.
* `ringTau`, `normSq_ringTau`, `ringTau_sub_eq`, `normSq_ringTau_sub`, `ringTau_conj_mul`,
  `ringTau_mul_eis_re`.
* `ringApex`, `normSq_ringApex`, `normSq_ringApex_sub`, `conj_ringApex_mul`.
-/

open ComplexConjugate

namespace RigidArrangements

/-! ## `R14`: two lattice bodies, a hinge and a bar, all on one lattice -/

/-- Body 1 of `R14`: a six-circle chevron in build order, hinge at `0`, bar end `(1, 1)` at
norm `3`. It is the chevron `o11L₁` of `O11` under the lattice isometry `(a, b) ↦ (a, -a-b)`. -/
def r14L₁ : List (ℤ × ℤ) := [(0, 0), (1, 0), (1, -1), (2, -1), (2, 0), (1, 1)]

/-- Body 2 of `R14` without its hinge, in build order. It is exactly the `ex13L₂` of
`RigidArrangements/OffLatticeExamples.lean` — the nine-circle body of `Q13`, hinge `0` not
listed — reordered to start at `(-1, 0)`; its bar end `(0, 2)` is at norm `4`, the same `v` as
in `ex13Check`. -/
def r14L₂ : List (ℤ × ℤ) :=
  [(-1, 0), (-1, 1), (-2, 1), (-2, 2), (-1, 2), (-2, 3), (-1, 3), (0, 2)]

/-- All fourteen sites of `R14`: body 1, then body 2 without the shared hinge. -/
def r14Sites : List (ℤ × ℤ) := r14L₁ ++ r14L₂

theorem r14L₁_nodup : r14L₁.Nodup := by decide

theorem r14L₂_cons_nodup : ((0 : ℤ × ℤ) :: r14L₂).Nodup := by decide

theorem r14Sites_nodup : r14Sites.Nodup := by decide

theorem r14Sites_length : r14Sites.length = 14 := by rfl

/-- The hinge-and-bar check passes for `R14`: both bodies have build certificates, the bar
closes (`D = 12 ≥ 0`), and no two circles overlap. -/
theorem r14Check : hbCheck r14L₁ r14L₂ (1, 1) (0, 2) 1 = true := by decide +kernel

/-- `D = 12` for `R14`: the hinge triangle has sides `2√3`, `4`, `2`. -/
theorem r14_hbD : hbD (1, 1) (0, 2) = 12 := by decide

namespace Arrangement

/-- **`R14`**: two lattice bodies — a six-circle chevron and the nine-circle body of `Q13` —
sharing the hinge at the lattice origin and locked by the bar from `(1, 1)` to `(0, 2)`.
Fourteen circles, twenty-five contacts, and, unlike `O11` and `Q13`, on the lattice: the port
norms `(3, 4)` force a lattice turn. -/
noncomputable def r14 : Arrangement (Fin r14L₁.length ⊕ Fin r14L₂.length) := hbArr r14Check

/-- **`R14` is rigid**, by the hinge-and-bar lemma. -/
theorem r14_isRigid : r14.IsRigid := hbArr_isRigid r14Check

end Arrangement

/-! ### The turn is trivial, so `R14` is on the lattice -/

private theorem r14_sqrt_hbD : Real.sqrt ((hbD (1, 1) (0, 2) : ℤ) : ℝ) = 2 * Real.sqrt 3 := by
  rw [show ((hbD (1, 1) (0, 2) : ℤ) : ℝ) = 2 ^ 2 * 3 by rw [r14_hbD]; norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

private theorem r14_hbW_re : (hbW (1, 1) (0, 2) ((1 : ℤ) : ℝ)).re = 1 := by
  simp only [hbW]
  norm_num [eNorm]

private theorem r14_hbW_im : (hbW (1, 1) (0, 2) ((1 : ℤ) : ℝ)).im = Real.sqrt 3 / 3 := by
  simp only [hbW]
  rw [r14_sqrt_hbD, show ((eNorm ((1 : ℤ), (1 : ℤ)) : ℤ) : ℝ) = 3 by norm_num [eNorm]]
  push_cast
  ring

private theorem r14_hbW : hbW (1, 1) (0, 2) ((1 : ℤ) : ℝ) = 2 * (1 + rho) / 3 := by
  refine Complex.ext ?_ ?_
  · rw [r14_hbW_re]
    simp
    norm_num
  · rw [r14_hbW_im]
    simp
    ring

/-- **The turn of body 2 is the identity.** With port norms `(3, 4)` and `σ = 1` the closing
formula returns `α = 1`: body 2 is not moved at all, so `R14` stays on the lattice body 1 lives
on. This is the `(3, 4)` entry of the "every realization is on a lattice" list of
`docs/offlattice.md` §4.3, made explicit. -/
theorem r14_turn : hbAlpha (1, 1) (0, 2) ((1 : ℤ) : ℝ) = 1 := by
  have h4 : ((eNorm ((0 : ℤ), (2 : ℤ)) : ℤ) : ℂ) = 4 := by norm_num [eNorm]
  have hu : eis (1, 1) = 1 + rho := by norm_num [eis]
  have hv : eis (0, 2) = 2 * rho := by norm_num [eis]
  have hc : conj (eis ((0 : ℤ), (2 : ℤ))) = 2 * (1 - rho) := by
    rw [hv, map_mul, map_ofNat, conj_rho_eq_one_sub]
  simp only [hbAlpha]
  rw [hu, hc, h4, r14_hbW]
  linear_combination ((-rho - 2) / 3) * rho_sq

namespace Arrangement

/-- The lattice site of each circle of `R14`. -/
def r14Site : Fin r14L₁.length ⊕ Fin r14L₂.length → ℤ × ℤ
  | .inl i => r14L₁.get i
  | .inr j => r14L₂.get j

/-- The hinge of `R14`: the circle shared by the two bodies, at the lattice origin. -/
def r14Hinge : Fin r14L₁.length ⊕ Fin r14L₂.length := Sum.inl ⟨0, by decide⟩

/-- The near end of the bar: the far end of body 1's chevron, at norm `3` from the hinge. -/
def r14BarL : Fin r14L₁.length ⊕ Fin r14L₂.length := Sum.inl ⟨5, by decide⟩

/-- The far end of the bar, in body 2, at norm `4` from the hinge. -/
def r14BarR : Fin r14L₁.length ⊕ Fin r14L₂.length := Sum.inr ⟨7, by decide⟩

/-- **Every circle of `R14` sits at a lattice point**, since the turn of body 2 is the
identity. -/
theorem r14_center_eq (i : Fin r14L₁.length ⊕ Fin r14L₂.length) :
    r14.center i = latticePoint (r14Site i) := by
  rcases i with i | j
  · rfl
  · change hbAlpha (1, 1) (0, 2) ((1 : ℤ) : ℝ) * latticePoint (r14L₂.get j) = _
    rw [r14_turn, one_mul]
    rfl

/-- **`R14` is on the lattice.** Unlike `O11`, `Q13`, `ex15` and `ex17`, the hinge-and-bar
arrangement with port norms `(3, 4)` needs no isometry at all: its centres already are lattice
points. -/
theorem r14_isLattice : r14.IsLattice :=
  ⟨AffineIsometryEquiv.refl ℝ Plane, r14Site, fun i => r14_center_eq i⟩

/-- Tangency in `R14`, in lattice coordinates. -/
theorem r14_tangent_iff (i j : Fin r14L₁.length ⊕ Fin r14L₂.length) :
    Tangent r14.center i j ↔ eNorm (r14Site i - r14Site j) = 1 := by
  change dist (r14.center i) (r14.center j) = 2 ↔ _
  rw [r14_center_eq, r14_center_eq]
  exact tangent_latticePoint_iff _ _

end Arrangement

/-! ### The combinatorics of `R14`, checked on the site list -/

/-- **`R14` has `25` contacts**, counted here as `50` ordered pairs. Since `25 = 2 · 14 - 3`,
the arrangement is isostatic: exactly as many contacts as a rigid arrangement of `14` circles
must have. Body 1 contributes `9`, body 2 contributes `15`, and the bar `1`. -/
theorem r14Sites_contacts :
    (r14Sites.map fun a => r14Sites.countP fun b => eNorm (a - b) == 1).sum = 50 := by
  decide +kernel

/-- Body 1 on its own has `9` contacts. -/
theorem r14L₁_contacts :
    (r14L₁.map fun a => r14L₁.countP fun b => eNorm (a - b) == 1).sum = 18 := by
  decide +kernel

/-- Body 2, with the hinge, has `15` contacts. -/
theorem r14L₂_contacts :
    (((0 : ℤ × ℤ) :: r14L₂).map fun a =>
      ((0 : ℤ × ℤ) :: r14L₂).countP fun b => eNorm (a - b) == 1).sum = 30 := by
  decide +kernel

/-- **Every circle of `R14` touches at least three others.** Hence no circle is removable, and
(by the counting argument in the module docstring) no Henneberg build order exists. -/
theorem r14Sites_degree :
    r14Sites.all (fun a => 3 ≤ r14Sites.countP fun b => eNorm (a - b) == 1) = true := by
  decide +kernel

/-- `R14` has no build certificate in the order it is written: it is not assembled by Henneberg
steps. -/
theorem r14Sites_not_latticeBuilt : latticeBuilt r14Sites = false := by decide +kernel

namespace Arrangement

private theorem r14_three_neighbours :
    ∀ w : Fin r14L₁.length ⊕ Fin r14L₂.length,
      ∃ x y z : Fin r14L₁.length ⊕ Fin r14L₂.length, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        eNorm (r14Site w - r14Site x) = 1 ∧ eNorm (r14Site w - r14Site y) = 1 ∧
        eNorm (r14Site w - r14Site z) = 1 := by
  decide +kernel

/-- **`R14` is a core**: every circle touches at least three others, so none is removable.
With `r14_isRigid` this makes `R14` a rigid lattice core of `14` circles. -/
theorem r14_isCore : r14.IsCore := by
  rintro w ⟨u, v, -, hadj, -⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ := r14_three_neighbours w
  have key : ∀ t, eNorm (r14Site w - r14Site t) = 1 → t = u ∨ t = v := fun t ht =>
    (hadj t).mp ⟨fun hwt => by rw [hwt] at ht; simp [eNorm] at ht,
      (r14_tangent_iff w t).mpr ht⟩
  rcases key x hx with rfl | rfl <;> rcases key y hy with rfl | rfl <;>
    rcases key z hz with rfl | rfl <;> simp_all

/-- **The bar**: the far end of body 1 touches the far end of body 2. -/
theorem r14_bar : Tangent r14.center r14BarL r14BarR :=
  (r14_tangent_iff _ _).mpr (by decide)

/-- **The bar is the only contact between the two bodies.** Body 2 is `{hinge} ∪ r14L₂`, so a
contact "across" means a contact from a circle of body 1 *other than the hinge* to a circle of
`r14L₂`; there is exactly one, the bar. (Without excluding the hinge the statement is false, and
`decide` says so: the hinge touches the first two circles of `r14L₂`, inside body 2.) So the two
bodies really are joined by a hinge and a bar and nothing else. -/
theorem r14_cross_contact {i : Fin r14L₁.length} {j : Fin r14L₂.length}
    (hi : (Sum.inl i : Fin r14L₁.length ⊕ Fin r14L₂.length) ≠ r14Hinge)
    (h : Tangent r14.center (Sum.inl i) (Sum.inr j)) :
    (Sum.inl i : Fin r14L₁.length ⊕ Fin r14L₂.length) = r14BarL ∧
      (Sum.inr j : Fin r14L₁.length ⊕ Fin r14L₂.length) = r14BarR := by
  have key : ∀ (i : Fin r14L₁.length) (j : Fin r14L₂.length),
      (Sum.inl i : Fin r14L₁.length ⊕ Fin r14L₂.length) ≠ r14Hinge →
      eNorm (r14Site (Sum.inl i) - r14Site (Sum.inr j)) = 1 →
        (Sum.inl i : Fin r14L₁.length ⊕ Fin r14L₂.length) = r14BarL ∧
          (Sum.inr j : Fin r14L₁.length ⊕ Fin r14L₂.length) = r14BarR := by decide
  exact key i j hi ((r14_tangent_iff _ _).mp h)

/-- **The bar lies in no triangle**: no circle touches both of its ends. So the bar is a bar in
the sense of `docs/offlattice.md` §2, not an edge of a body. -/
theorem r14_bar_no_triangle (k : Fin r14L₁.length ⊕ Fin r14L₂.length) :
    ¬ (Tangent r14.center r14BarL k ∧ Tangent r14.center r14BarR k) := by
  have key : ∀ k : Fin r14L₁.length ⊕ Fin r14L₂.length,
      ¬ (eNorm (r14Site r14BarL - r14Site k) = 1 ∧
        eNorm (r14Site r14BarR - r14Site k) = 1) := by decide
  exact fun ⟨h₁, h₂⟩ =>
    key k ⟨(r14_tangent_iff _ _).mp h₁, (r14_tangent_iff _ _).mp h₂⟩

/-- **No triangle joins the two bodies.** A triangle with one circle in each body would need a
contact across, hence the bar, and the bar lies in no triangle. So the eleven triangles of `R14`
split into the four of body 1 and the seven of body 2: the triangle-adjacency graph has exactly
two components, which is what makes `R14` a two-body arrangement. -/
theorem r14_no_cross_triangle {i : Fin r14L₁.length} {j : Fin r14L₂.length}
    {k : Fin r14L₁.length ⊕ Fin r14L₂.length}
    (hi : (Sum.inl i : Fin r14L₁.length ⊕ Fin r14L₂.length) ≠ r14Hinge)
    (h : Tangent r14.center (Sum.inl i) (Sum.inr j)) :
    ¬ (Tangent r14.center (Sum.inl i) k ∧ Tangent r14.center (Sum.inr j) k) := by
  obtain ⟨hL, hR⟩ := r14_cross_contact hi h
  rw [hL, hR]
  exact r14_bar_no_triangle k

/-! ### `R14` re-certified by the merging calculus -/

/-- Body 2 of `R14` together with the hinge: index `0` is the hinge, a circle of body 1. -/
def r14F₂ : Fin ((0 : ℤ × ℤ) :: r14L₂).length → Fin r14L₁.length ⊕ Fin r14L₂.length :=
  Fin.cases r14Hinge Sum.inr

theorem r14F₂_injective : Function.Injective r14F₂ := by
  have h : ∀ i j : Fin ((0 : ℤ × ℤ) :: r14L₂).length, r14F₂ i = r14F₂ j → i = j := by decide
  exact fun {i j} hij => h i j hij

/-- **Body 1 is rigid**: it is the lattice chevron `r14L₁`, which has a build certificate. -/
theorem r14_body1_isRigid : (r14.comap Sum.inl Sum.inl_injective).IsRigid := by
  have h : (r14.comap Sum.inl Sum.inl_injective).center = (ofLattice r14L₁ r14L₁_nodup).center :=
    funext fun _ => rfl
  change IsLocallyRigid _
  rw [h]
  exact isRigid_ofLattice_of_latticeBuilt r14L₁_nodup (by decide)

/-- **Body 2 is rigid**: with the hinge it is the nine-circle lattice body `0 :: r14L₂`, which
has a build certificate. The turn being trivial (`r14_turn`) is what lets the body be read off
the lattice directly. -/
theorem r14_body2_isRigid : (r14.comap r14F₂ r14F₂_injective).IsRigid := by
  have h : (r14.comap r14F₂ r14F₂_injective).center =
      (ofLattice ((0 : ℤ × ℤ) :: r14L₂) r14L₂_cons_nodup).center := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change hbAlpha (1, 1) (0, 2) ((1 : ℤ) : ℝ) * latticePoint (r14L₂.get j) = _
      rw [r14_turn, one_mul]
      rfl
  change IsLocallyRigid _
  rw [h]
  exact isRigid_ofLattice_of_latticeBuilt r14L₂_cons_nodup (by decide)

/-- **`R14` is rigid, by the merging calculus** — so `R14` is *constructible* in the sense of
`RigidArrangements/Cluster.lean`.

Three clusters: body 1 and body 2, each a rigid lattice body fed in by
`Arrangement.rigidIn_of_comap`, and the bar, an atom fed in by `Arrangement.rigidIn_pair`. They
pairwise share the hinge (body 1 and body 2), the far bar end (body 2 and the bar) and the near
bar end (body 1 and the bar), and those three circles are distinct, so **R2**
(`Arrangement.RigidIn.union_of_ring`) merges all three in one step. The union is everything, and
`Arrangement.rigidIn_univ_iff` cashes that in.

Here the triangle of shared circles has squared sides `12`, `16`, `4` — the hinge triangle of
the construction — so it is not degenerate; but R2 would not have cared if it were. Compare
`r14_isRigid`, which calls `hbArr_isRigid` and hence the hinge-and-bar lemma directly. -/
theorem r14_isRigid_of_cluster : r14.IsRigid := by
  rw [← rigidIn_univ_iff]
  have h₁ : r14.RigidIn (Set.range (Sum.inl : Fin r14L₁.length → _)) :=
    r14.rigidIn_of_comap Sum.inl Sum.inl_injective r14_body1_isRigid
  have h₂ : r14.RigidIn (Set.range r14F₂) :=
    r14.rigidIn_of_comap r14F₂ r14F₂_injective r14_body2_isRigid
  have h₃ : r14.RigidIn {r14BarL, r14BarR} := rigidIn_pair r14_bar
  refine (h₁.union_of_ring h₂ h₃ (c₁ := r14BarR) (c₂ := r14BarL) (c₃ := r14Hinge)
    ⟨⟨⟨0, by decide⟩, rfl⟩, ⟨⟨0, by decide⟩, rfl⟩⟩ ⟨⟨⟨8, by decide⟩, rfl⟩, by simp⟩
    ⟨⟨⟨5, by decide⟩, rfl⟩, by simp⟩ (by decide) (by decide) (by decide)).mono ?_
  rintro (i | j) -
  · exact Or.inl (Or.inl ⟨i, rfl⟩)
  · exact Or.inl (Or.inr ⟨j.succ, rfl⟩)

end Arrangement

/-! ## Three bodies in a ring: the arithmetic of the hinge triangle -/

/-- **The discriminant of a ring of three bodies.** If the hinge triangle has squared sides
`4a`, `4b`, `4c`, then `ringD a b c` is sixteen times its squared area, so `0 ≤ ringD a b c` is
exactly the condition that the three hinge distances close. It is symmetric in `a`, `b`, `c`. -/
def ringD (a b c : ℤ) : ℤ := 2 * a * b + 2 * b * c + 2 * c * a - a ^ 2 - b ^ 2 - c ^ 2

theorem ringD_eq_four_mul_sub (a b c : ℤ) : ringD a b c = 4 * a * b - (a + b - c) ^ 2 := by
  simp only [ringD]; ring

theorem ringD_rotate (a b c : ℤ) : ringD a b c = ringD b c a := by simp only [ringD]; ring

theorem ringD_swap (a b c : ℤ) : ringD a b c = ringD a c b := by simp only [ringD]; ring

/-- **Hinge-and-bar is the ring whose third body is the two-circle rod.** Taking `c = 1` — the
two bar ends are tangent, so one unit apart in half-scale — turns `ringD` into the `hbD` of
`RigidArrangements/OffLatticeExamples.lean`. -/
theorem ringD_one_eq_hbD (u v : ℤ × ℤ) : ringD (eNorm u) (eNorm v) 1 = hbD u v := by
  simp only [ringD, hbD]; ring

/-- `T14`'s hinge triangle has squared sides `12, 16, 12`, so hinge norms `(3, 4, 3)`. Then
`√D = √32 = 4√2`, which is why `T14`'s coordinates live in `ℚ(√2, √3)`; but
`√(3D) = √96 = 4√6`, so its squared distances live in `ℚ(√6)`. -/
theorem t14_ringD : ringD 3 4 3 = 32 := by decide

/-- `Ring15`'s hinge triangle has hinge norms `(4, 4, 7)`, so `D = 63` and
`√(3D) = √189 = 3√21` — the `√21` that appears in every one of `Ring15`'s coordinates in
`docs/offlattice.md`. -/
theorem ring15_ringD : ringD 4 4 7 = 63 := by decide

variable {a b c : ℤ} {σ : ℝ}

/-- **The hinge-triangle parameter.** `τ = ((a + b - c) + σ i √D) / 2`, with `σ = ±1` choosing
the side. It is `H₂₃ · conj H₁₃` in body 1's frame: `Re τ = (a + b - c) / 2` is forced by the
law of cosines, and `|τ|² = a b` (`normSq_ringTau`). -/
noncomputable def ringTau (a b c : ℤ) (σ : ℝ) : ℂ :=
  ⟨((a + b - c : ℤ) : ℝ) / 2, σ * Real.sqrt ((ringD a b c : ℤ) : ℝ) / 2⟩

@[simp] theorem ringTau_re : (ringTau a b c σ).re = ((a + b - c : ℤ) : ℝ) / 2 := rfl

@[simp] theorem ringTau_im :
    (ringTau a b c σ).im = σ * Real.sqrt ((ringD a b c : ℤ) : ℝ) / 2 := rfl

private theorem sq_sigma_sqrt (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) :
    (σ * Real.sqrt ((ringD a b c : ℤ) : ℝ)) ^ 2 =
      2 * (a : ℝ) * b + 2 * (b : ℝ) * c + 2 * (c : ℝ) * a - (a : ℝ) ^ 2 - (b : ℝ) ^ 2
        - (c : ℝ) ^ 2 := by
  rw [mul_pow, hσ, one_mul, Real.sq_sqrt (by exact_mod_cast h)]
  simp only [ringD]
  push_cast
  ring

/-- `|τ|² = a b`: the third hinge is at the prescribed distance from the first. -/
theorem normSq_ringTau (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) :
    Complex.normSq (ringTau a b c σ) = (a : ℝ) * b := by
  have hs := sq_sigma_sqrt h hσ
  rw [Complex.normSq_apply, ringTau_re, ringTau_im]
  push_cast
  linear_combination hs / 4

/-- `τ - a = -conj τ'`, with `τ'` the `τ` of `(a, c, b)`: the mirror symmetry of the hinge
triangle about the bisector at `H₁₃`. -/
theorem ringTau_sub_eq (a b c : ℤ) (σ : ℝ) :
    ringTau a b c σ - (a : ℂ) = - conj (ringTau a c b σ) := by
  have hrot : ringD a c b = ringD a b c := (ringD_swap a b c).symm
  refine Complex.ext ?_ ?_
  · simp only [Complex.sub_re, Complex.neg_re, Complex.conj_re, ringTau_re, Complex.intCast_re]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.neg_im, Complex.conj_im, ringTau_im, Complex.intCast_im,
      hrot]
    ring

/-- `|τ - a|² = a c`: the third hinge is at the prescribed distance from the second. -/
theorem normSq_ringTau_sub (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) :
    Complex.normSq (ringTau a b c σ - (a : ℂ)) = (a : ℝ) * c := by
  rw [ringTau_sub_eq, Complex.normSq_neg, Complex.normSq_conj,
    normSq_ringTau (by rw [← ringD_swap a b c]; exact h) hσ]

/-- **The pivot identity**, in its bare form: `conj τ · (τ - a) = a · τ'`, where `τ'` is `τ`
with the hinge norms rotated from `(a, b, c)` to `(b, c, a)`. Since `ringD` is symmetric, `τ'`
carries the *same* `√D`. This is the algebraic reason a three-body ring needs only one
radical. -/
theorem ringTau_conj_mul (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) :
    conj (ringTau a b c σ) * (ringTau a b c σ - (a : ℂ)) = (a : ℂ) * ringTau b c a σ := by
  have hs := sq_sigma_sqrt h hσ
  have hrot : ringD b c a = ringD a b c := (ringD_rotate a b c).symm
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      ringTau_re, ringTau_im, Complex.intCast_re, Complex.intCast_im, hrot]
    push_cast
    linear_combination hs / 4
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      ringTau_re, ringTau_im, Complex.intCast_re, Complex.intCast_im, hrot]
    push_cast
    ring

/-- **One radical suffices.** For an Eisenstein integer `z`, the real part of `τ · eis z` — the
only irrational ingredient of any squared distance in a ring — is a rational number plus a
rational multiple of `√(3 D)`. Compare `crossAB` and `dist_sq_cross`, where the same thing
happens for a hinge and a bar with `3 D = 3 · hbD`. -/
theorem ringTau_mul_eis_re (a b c : ℤ) (σ : ℝ) (z : ℤ × ℤ) :
    (ringTau a b c σ * eis z).re =
      (((a + b - c) * (2 * z.1 + z.2) : ℤ) : ℝ) / 4 -
        σ * (z.2 : ℝ) * Real.sqrt ((3 * ringD a b c : ℤ) : ℝ) / 4 := by
  have h3 : Real.sqrt ((3 * ringD a b c : ℤ) : ℝ) =
      Real.sqrt 3 * Real.sqrt ((ringD a b c : ℤ) : ℝ) := by
    push_cast
    exact Real.sqrt_mul (by norm_num) _
  rw [Complex.mul_re, ringTau_re, ringTau_im, eis_re, eis_im, h3]
  push_cast
  ring

/-- **The third hinge, in body 1's frame.** With `H₁₂` at the origin and `H₁₃` at `eis al`
(`N al = a`), the hinge `H₂₃` shared by bodies 2 and 3 is at `τ · eis al / a`. -/
noncomputable def ringApex (a b c : ℤ) (σ : ℝ) (al : ℤ × ℤ) : ℂ :=
  ringTau a b c σ * eis al / (a : ℂ)

section Apex

variable {al : ℤ × ℤ}

private theorem ringApex_cast_ne_zero (hal : al ≠ 0) (ha : eNorm al = a) : (a : ℂ) ≠ 0 := by
  refine Int.cast_ne_zero.mpr ?_
  rw [← ha]
  exact fun hz => hal ((eNorm_eq_zero_iff al).1 hz)

private theorem ringApex_cast_pos (hal : al ≠ 0) (ha : eNorm al = a) : (0 : ℝ) < (a : ℝ) := by
  rw [← ha]; exact eNorm_pos hal

private theorem normSq_intCast_self : Complex.normSq ((a : ℂ)) = (a : ℝ) * (a : ℝ) := by
  rw [Complex.normSq_apply, Complex.intCast_re, Complex.intCast_im]
  ring

/-- `a · H₂₃ = τ · eis al`: the defining identity of `ringApex`, cleared of its denominator. -/
theorem mul_ringApex (hal : al ≠ 0) (ha : eNorm al = a) :
    (a : ℂ) * ringApex a b c σ al = ringTau a b c σ * eis al := by
  have hane := ringApex_cast_ne_zero hal ha
  change (a : ℂ) * (ringTau a b c σ * eis al / (a : ℂ)) = _
  field_simp

/-- `a · (H₂₃ - H₁₃) = (τ - a) · eis al`. -/
theorem mul_ringApex_sub (hal : al ≠ 0) (ha : eNorm al = a) :
    (a : ℂ) * (ringApex a b c σ al - eis al) = (ringTau a b c σ - (a : ℂ)) * eis al := by
  linear_combination mul_ringApex (b := b) (c := c) (σ := σ) hal ha

/-- `|H₂₃ - H₁₂|² = b`: the third hinge is the right distance from the first hinge. -/
theorem normSq_ringApex (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) (hal : al ≠ 0)
    (ha : eNorm al = a) : Complex.normSq (ringApex a b c σ al) = (b : ℝ) := by
  have ha0 := ringApex_cast_pos hal ha
  have hne : (a : ℝ) * (a : ℝ) ≠ 0 := by positivity
  have hq := congrArg Complex.normSq (mul_ringApex (b := b) (c := c) (σ := σ) hal ha)
  rw [map_mul, map_mul, normSq_intCast_self, normSq_ringTau h hσ, normSq_eis, ha] at hq
  refine mul_left_cancel₀ hne ?_
  linear_combination hq

/-- `|H₂₃ - H₁₃|² = c`: the third hinge is the right distance from the second hinge. -/
theorem normSq_ringApex_sub (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) (hal : al ≠ 0)
    (ha : eNorm al = a) : Complex.normSq (ringApex a b c σ al - eis al) = (c : ℝ) := by
  have ha0 := ringApex_cast_pos hal ha
  have hne : (a : ℝ) * (a : ℝ) ≠ 0 := by positivity
  have hq := congrArg Complex.normSq (mul_ringApex_sub (b := b) (c := c) (σ := σ) hal ha)
  rw [map_mul, map_mul, normSq_intCast_self, normSq_ringTau_sub h hσ, normSq_eis, ha] at hq
  refine mul_left_cancel₀ hne ?_
  linear_combination hq

/-- **The pivot of the ring.** `conj H₂₃ · (H₂₃ - H₁₃) = τ'`, the hinge-triangle parameter of
the rotated data `(b, c, a)`.

This answers the question the module docstring poses. The turn of body 2 relative to body 1 is
`H₂₃ / eis β` and the turn of body 3 relative to body 1 is `(H₂₃ - H₁₃) / eis γ`, so the turn of
body 3 relative to body 2 is

`conj (H₂₃ / eis β) · (H₂₃ - H₁₃) / eis γ = ringTau b c a σ · eis β · conj (eis γ) / (b c)`:

again a ring turn, with the same `√D`, for the cyclically shifted hinge norms. By
`ringTau_mul_eis_re` every squared distance in the ring — within a body, or across any of the
three pairs of bodies — therefore has the form `A + B √(3 D)` with `A`, `B` rational, so a
single `nonnegSqrt _ _ (3 * ringD a b c)` test decides them all, exactly as `hbCheck` does for a
hinge and a bar. The two radicals of `T14`'s coordinate field `ℚ(√2, √3)` never appear together
in a distance. -/
theorem conj_ringApex_mul (h : 0 ≤ ringD a b c) (hσ : σ ^ 2 = 1) (hal : al ≠ 0)
    (ha : eNorm al = a) :
    conj (ringApex a b c σ al) * (ringApex a b c σ al - eis al) = ringTau b c a σ := by
  have hane := ringApex_cast_ne_zero hal ha
  have hA : conj ((a : ℂ)) = (a : ℂ) := map_intCast (starRingEnd ℂ) a
  have hconj : conj (eis al) * eis al = (a : ℂ) := by
    rw [mul_comm, Complex.mul_conj, normSq_eis, ha]
    push_cast
    rfl
  have hap := mul_ringApex (b := b) (c := c) (σ := σ) hal ha
  have hapc : (a : ℂ) * conj (ringApex a b c σ al) =
      conj (ringTau a b c σ) * conj (eis al) := by
    have hcg := congrArg (starRingEnd ℂ) hap
    rwa [map_mul, map_mul, hA] at hcg
  have hP := ringTau_conj_mul (σ := σ) h hσ
  refine mul_right_cancel₀ (mul_ne_zero hane hane) ?_
  have hrw : conj (ringApex a b c σ al) * (ringApex a b c σ al - eis al) * ((a : ℂ) * (a : ℂ)) =
      ((a : ℂ) * conj (ringApex a b c σ al)) *
        ((a : ℂ) * ringApex a b c σ al - (a : ℂ) * eis al) := by ring
  rw [hrw, hapc, hap]
  linear_combination (conj (eis al) * eis al) * hP + ((a : ℂ) * ringTau b c a σ) * hconj

end Apex

end RigidArrangements
