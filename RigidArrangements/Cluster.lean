import RigidArrangements.OffLattice

/-!
# Clusters and the merging calculus

Rigidity of an arrangement is an all-or-nothing property of the whole placement. In practice a
rigid arrangement is built out of pieces: a few circles that are already known not to move
relative to one another, glued together along shared circles and extra contacts. This file makes
"does not move relative to one another" into a first-class notion and proves the gluing rules.

## Relative rigidity

For a set `S` of circles of an arrangement `A`, the predicate `Arrangement.RigidIn A S` says
that `S` *moves rigidly*: every placement `q` close enough to the centers of `A` that keeps all
the contacts of `A` has the same distance between any two circles of `S` as `A` does. The set
`S` may flex relative to the rest of the arrangement; what is forbidden is a change of shape
*inside* `S`. We call such an `S` a **cluster**.

The definition is stated with the neighbourhood filter `𝓝 A.center`, exactly as
`IsLocallyRigid` is, and this is essential rather than cosmetic: the whole calculus below rests
on combining several clusters, which is `Filter.Eventually.and`. An equivalent `ε`-form exists
(for finitely many circles, by `isLocallyRigid_iff_eps`) but does not combine, because three
clusters come with three unrelated `ε`'s and nothing says the small motions they describe are
the same ones.

Clusters enter the calculus in two ways.

* A single contact is a cluster (`Arrangement.rigidIn_pair`): keeping the contact *is* keeping
  the one distance involved. This is the atom of the calculus; it needs no neighbourhood at all.
* A rigid sub-arrangement is a cluster (`Arrangement.rigidIn_of_comap`). This is how a *body* —
  a chevron, a lattice patch, anything already certified rigid on its own — is fed in.

At the other end, `Arrangement.rigidIn_univ_iff` says that the set of *all* circles is a cluster
exactly when the arrangement is rigid. So a rigidity certificate becomes: list some atoms and
bodies, merge them until one cluster contains everything, conclude.

## The pinning engine

Everything rests on one lemma, `Arrangement.rigidIn_of_dist_two`. Suppose two circles `a` and
`b` have distinct centers and every circle of a set `T` keeps its distances to both `a` and `b`
along small contact-keeping motions. Then `T` is a cluster.

The proof is the normalisation argument of `IsLocallyRigid.of_hinge` with its last step removed.
Given a small motion `q`, move everything back by the rotation and translation `Φ q` that
returns `q a` to `A.center a` and the direction of `q b - q a` to that of `A.center b -
A.center a`. This is a rigid motion of the plane (`a` and `b` stay a fixed distance apart, so
the complex factor has modulus one), it fixes `a` and `b`, and it is continuous at
`A.center`. Each circle `k` of `T` then has its two original distances to the two fixed points
`A.center a` and `A.center b`, so it lies at `A.center k` or at its mirror image in the line
through them; the mirror image is either the same point or a fixed positive distance away, and
for `q` close enough that is excluded (`eventually_eq_of_dist_eq_of_dist_eq`). So `Φ q` is the
identity on `T`, and `Φ q` preserves all distances, whence `q` does too on `T`.

`IsLocallyRigid.of_hinge` is the special case where `a` is a hinge, `b` the near end of a bar,
and one extra pinning step carries the far end of the bar; here that step is not built in, which
is what makes the lemma reusable.

## The three merging rules

* **R1** (`Arrangement.RigidIn.union_of_two`): two clusters sharing *two* distinct circles merge.
  The two shared circles are the `a` and `b` of the engine, and every circle of either cluster
  keeps its distances to both.
* **R2** (`Arrangement.RigidIn.union_of_ring`): three clusters that pairwise share a circle, the
  three shared circles being distinct, merge. Note what is *not* needed: no non-degeneracy
  whatsoever. Each of the three sides of the triangle formed by the shared circles lies inside
  one of the three clusters, so all three side lengths are preserved, so the triple of shared
  circles is itself a cluster — by `Filter.Eventually.and` alone, with no geometry. Then R1
  merges it with each of the three in turn. A *collinear* triangle of shared circles is
  therefore fine: relative rigidity is a statement about distances, and a flat triangle is
  determined by its side lengths just as a fat one is. (R2 subsumes a Henneberg step, where two
  of the three clusters are atoms, and the hinge-and-bar lemma, where one is.)
* **R3** (`Arrangement.RigidIn.union_chain`): if two circles `u`, `v` of a cluster are at
  distance exactly `2k` and are joined by a chain of `k` contacts, the chain merges into the
  cluster. The chain is taut: `k` steps of length `2` spanning `2k` leave no slack, so by the
  iterated triangle inequality (`chain_dist`, true in any pseudometric space) the `i`-th circle
  of the chain is at distance exactly `2i` from `u` and `2(k - i)` from `v`. Those two distances
  hold both before and after the motion, so the engine pins the chain with `a = u`, `b = v`, and
  the same engine call also fixes the distances from a chain circle to every circle of the
  cluster. Again no collinearity, no `Wbtw`, no convexity of the ambient space is needed: the
  chain circles *are* collinear, but we never have to say so.

## A worked example

`Arrangement.o11_isRigid_of_cluster` re-proves that the off-lattice arrangement `O11` is rigid
using nothing but the calculus: the two chevrons are clusters by `rigidIn_of_comap`, the bar
`X Y` is a cluster by `rigidIn_pair`, one application of R2 with the triangle `H`, `Y`, `X` of
shared circles merges all three, and `rigidIn_univ_iff` finishes. This is the same mathematics
as `Arrangement.o11_isRigid`, which calls the hinge-and-bar lemma directly, but assembled from
the general rules.
-/

open Filter Topology

namespace RigidArrangements

/-! ### Taut chains in a pseudometric space -/

/-- **A taut chain has no slack.** If `w 0, w 1, …, w k` are points with consecutive distances
`2` and with `w 0` and `w k` at distance exactly `2k`, then every intermediate point sits at
distance exactly `2i` from `w 0` and `2 (k - i)` from `w k`.

This is the equality case of the iterated triangle inequality, and it holds in any pseudometric
space: no collinearity, betweenness or convexity is involved. (In the plane the points are of
course collinear, but we never need to say so.) -/
theorem chain_dist {k : ℕ} {P : Type*} [PseudoMetricSpace P] (w : ℕ → P)
    (hstep : ∀ i < k, dist (w i) (w (i + 1)) = 2)
    (hend : dist (w 0) (w k) = 2 * k) :
    ∀ i ≤ k, dist (w 0) (w i) = 2 * i ∧ dist (w i) (w k) = 2 * (k - i) := by
  -- walking from `w a` to `w b` costs at most `2 (b - a)`
  have hup : ∀ a b, a ≤ b → b ≤ k → dist (w a) (w b) ≤ 2 * (b - a) := by
    intro a b hab hbk
    induction b with
    | zero => simp_all
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · simp
      · have hb : a ≤ b := Nat.lt_succ_iff.mp hlt
        have h1 := ih hb (Nat.le_of_succ_le hbk)
        have h2 := hstep b (Nat.lt_of_succ_le hbk)
        have := dist_triangle (w a) (w b) (w (b + 1))
        have hcast : ((b + 1 : ℕ) : ℝ) - a = ((b : ℝ) - a) + 1 := by push_cast; ring
        rw [hcast]
        linarith
  intro i hik
  have h1 := hup 0 i (Nat.zero_le i) hik
  have h2 := hup i k hik le_rfl
  have h3 := dist_triangle (w 0) (w i) (w k)
  have hik' : (i : ℝ) ≤ k := Nat.cast_le.mpr hik
  rw [hend] at h3
  simp only [Nat.cast_zero, sub_zero] at h1
  refine ⟨?_, ?_⟩ <;>
    nlinarith [dist_nonneg (x := w 0) (y := w i), dist_nonneg (x := w i) (y := w k)]

namespace Arrangement

variable {ι : Type*}

/-! ### Relative rigidity -/

/-- **A cluster.** The circles of `S` move rigidly: every placement close enough to `A` that
keeps all the contacts of `A` has the same distance between any two circles of `S` as `A` does.
The set `S` may still flex relative to the rest of the arrangement.

As with `IsLocallyRigid`, "close enough" is the neighbourhood filter `𝓝 A.center` rather than an
explicit `ε`. This is what lets several clusters be combined with `Filter.Eventually.and`, the
basic move of the merging calculus below. -/
def RigidIn (A : Arrangement ι) (S : Set ι) : Prop :=
  ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q →
    ∀ i ∈ S, ∀ j ∈ S, dist (q i) (q j) = dist (A.center i) (A.center j)

/-! ### Structural lemmas -/

/-- A subset of a cluster is a cluster. -/
theorem RigidIn.mono {A : Arrangement ι} {S T : Set ι} (h : A.RigidIn S) (hTS : T ⊆ S) :
    A.RigidIn T := by
  filter_upwards [h] with q hq hk i hi j hj using hq hk i (hTS hi) j (hTS hj)

/-- A set of at most one circle is a cluster: there is nothing to preserve. -/
theorem rigidIn_of_subsingleton {A : Arrangement ι} {S : Set ι} (hS : S.Subsingleton) :
    A.RigidIn S := by
  refine Eventually.of_forall fun q _ i hi j hj => ?_
  rw [hS hi hj, dist_self, dist_self]

/-- **The atom of the calculus.** Two tangent circles form a cluster. Keeping the contact *is*
keeping the only distance in question, so no neighbourhood of `A.center` is needed. -/
theorem rigidIn_pair {A : Arrangement ι} {x y : ι} (hxy : Tangent A.center x y) :
    A.RigidIn {x, y} := by
  refine Eventually.of_forall fun q hk i hi j hj => ?_
  have hyx : Tangent A.center y x := tangent_comm.mp hxy
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rw [dist_self, dist_self]
  · rw [hk _ _ hxy, hxy]
  · rw [hk _ _ hyx, hyx]
  · rw [dist_self, dist_self]

/-- **Clusters certify rigidity.** The set of all circles is a cluster exactly when the
arrangement is rigid. This is how a chain of merges is cashed in. -/
theorem rigidIn_univ_iff (A : Arrangement ι) : A.RigidIn Set.univ ↔ A.IsRigid := by
  unfold RigidIn IsRigid IsLocallyRigid
  constructor <;> intro h <;> filter_upwards [h] with q hq hk
  · rw [congruent_iff_dist_eq]
    exact fun i j => hq hk i (Set.mem_univ i) j (Set.mem_univ j)
  · exact fun i _ j _ => congruent_iff_dist_eq.mp (hq hk) i j

/-- **Bodies enter the calculus.** If the sub-arrangement on the circles `f k` is rigid in its
own right, then the set of those circles is a cluster of the ambient arrangement. -/
theorem rigidIn_of_comap (A : Arrangement ι) {κ : Type*} (f : κ → ι)
    (hf : Function.Injective f) (h : (A.comap f hf).IsRigid) : A.RigidIn (Set.range f) := by
  filter_upwards [IsLocallyRigid.eventually_comp (p := A.center) (f := f) h] with q hq hk
  rintro i ⟨a, rfl⟩ j ⟨b, rfl⟩
  exact congruent_iff_dist_eq.mp (hq fun u v huv => hk (f u) (f v) huv) a b

/-! ### The pinning engine -/

/-- **The pinning engine.** Let `a` and `b` be circles with distinct centers, with `b` in the
set `T`, and suppose that along small contact-keeping motions every circle of `T` keeps its
distances to both `a` and `b`. Then `T` is a cluster.

This is the engine behind all three merging rules. The proof is the normalisation argument of
`IsLocallyRigid.of_hinge` with its bar step removed: move the motion back by the rigid motion
`Φ q` of the plane that restores `a` and the direction from `a` to `b`, note that each circle of
`T` then has its two original distances to the two restored points, and conclude by
`eventually_forall_eq_of_dist_eq_of_dist_eq` that `Φ q` is the identity on `T`. Since `Φ q`
preserves all distances, so does `q` on `T`.

Only `b ∈ T` is required: the distances from `a` are used as a hypothesis, never as part of the
conclusion. -/
theorem rigidIn_of_dist_two [Finite ι] {A : Arrangement ι} {T : Set ι} {a b : ι}
    (hne : A.center a ≠ A.center b) (hbT : b ∈ T)
    (h : ∀ᶠ q in 𝓝 A.center, KeepsContacts A.center q → ∀ k ∈ T,
      dist (q k) (q a) = dist (A.center k) (A.center a) ∧
      dist (q k) (q b) = dist (A.center k) (A.center b)) :
    A.RigidIn T := by
  have := Fintype.ofFinite ι
  set p := A.center with hp
  have hd : p b - p a ≠ 0 := sub_ne_zero.mpr hne.symm
  -- `Φ q` is `q` moved by the rotation and translation taking `q a` to `p a` and the direction
  -- of `q b` to that of `p b`.
  let Φ : (ι → Plane) → (ι → Plane) := fun q k =>
    p a + (p b - p a) / (q b - q a) * (q k - q a)
  have hΦp : Φ p = p := by
    funext k
    simp only [Φ]
    field_simp
    ring
  have hΦc : ContinuousAt Φ p := by
    refine continuousAt_pi.2 fun k => ?_
    have hden : (fun q : ι → Plane => q b - q a) p ≠ 0 := hd
    have c1 : ContinuousAt (fun q : ι → Plane => q b - q a) p := by fun_prop
    have c2 : ContinuousAt (fun q : ι → Plane => q k - q a) p := by fun_prop
    exact continuousAt_const.add ((continuousAt_const.div c1 hden).mul c2)
  have hTend : Tendsto Φ (𝓝 p) (𝓝 p) := by
    have := hΦc.tendsto
    rwa [hΦp] at this
  have hpin := hTend.eventually (eventually_forall_eq_of_dist_eq_of_dist_eq (p := p) hne)
  filter_upwards [hpin, h] with q hq hr hk
  have hc := hr hk
  have hqab : dist (q b) (q a) = dist (p b) (p a) := (hc b hbT).1
  have hq0 : q b - q a ≠ 0 := by
    intro h0
    rw [dist_eq_norm, h0, norm_zero, eq_comm, dist_eq_zero] at hqab
    exact hne hqab.symm
  have hρn : ‖(p b - p a) / (q b - q a)‖ = 1 := by
    rw [norm_div, ← dist_eq_norm, ← dist_eq_norm, hqab, div_self]
    exact dist_ne_zero.mpr hne.symm
  have hΦdist : ∀ k l, dist (Φ q k) (Φ q l) = dist (q k) (q l) := by
    intro k l
    simp only [Φ, dist_eq_norm]
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hρn, one_mul, sub_sub_sub_cancel_right]
  have hΦa : Φ q a = p a := by simp [Φ]
  have hΦb : Φ q b = p b := by
    simp only [Φ]
    field_simp
    ring
  -- distances to a center that is already back in place
  have hfix : ∀ k l, Φ q l = p l → dist (Φ q k) (p l) = dist (q k) (q l) := fun k l hl => by
    rw [← hl, hΦdist]
  have pin : ∀ k ∈ T, Φ q k = p k := fun k hkT =>
    hq k (by rw [hfix _ _ hΦa]; exact (hc k hkT).1) (by rw [hfix _ _ hΦb]; exact (hc k hkT).2)
  intro i hi j hj
  rw [← hΦdist, pin i hi, pin j hj]

/-! ### R1: two clusters sharing two circles -/

/-- **Rule R1.** Two clusters that share two distinct circles merge into one.

The two shared circles `a`, `b` feed the pinning engine: every circle of `S` keeps its distances
to both because `a, b ∈ S`, and likewise for `T`. The only non-degeneracy, that `a` and `b` have
distinct centers, is automatic from `Arrangement.center_injective`. -/
theorem RigidIn.union_of_two [Finite ι] {A : Arrangement ι} {S T : Set ι}
    (h₁ : A.RigidIn S) (h₂ : A.RigidIn T) {a b : ι}
    (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) (hab : a ≠ b) :
    A.RigidIn (S ∪ T) := by
  refine rigidIn_of_dist_two (A.center_injective.ne hab) (Or.inl hbS) ?_
  filter_upwards [h₁, h₂] with q hr₁ hr₂ hk k hkST
  rcases hkST with hkS | hkT
  · exact ⟨hr₁ hk k hkS a haS, hr₁ hk k hkS b hbS⟩
  · exact ⟨hr₂ hk k hkT a haT, hr₂ hk k hkT b hbT⟩

/-! ### R2: a ring of three clusters -/

/-- **Rule R2.** Three clusters that pairwise share a circle, the three shared circles `c₁`,
`c₂`, `c₃` being distinct, merge into one.

**There is no degenerate case.** It is tempting to expect a side condition saying that `c₁`,
`c₂`, `c₃` are not collinear, and a separate argument when they are. None is needed here, and
none appears in the statement. The reason is that each side of the triangle `c₁ c₂ c₃` lies
inside one of the three clusters — `c₂ c₃` in `S₁`, `c₁ c₃` in `S₂`, `c₁ c₂` in `S₃` — so all
three side lengths are preserved along any small contact-keeping motion, which makes
`{c₁, c₂, c₃}` itself a cluster. That step is `Filter.Eventually.and` and a case split on three
elements; it uses no geometry at all. Relative rigidity is a statement about distances, and a
flat triangle is pinned down by its side lengths exactly as a fat one is. If an argument here
seems to need non-collinearity, it is recovering *positions* rather than *distances*.

Three applications of R1 then merge the triple with `S₁`, `S₂` and `S₃` in turn.

R2 subsumes several familiar gluing steps: a Henneberg step (take two of the clusters to be
single contacts), the hinge-and-bar lemma (take one of them to be the bar) and a ring of three
rigid bodies. -/
theorem RigidIn.union_of_ring [Finite ι] {A : Arrangement ι} {S₁ S₂ S₃ : Set ι}
    (h₁ : A.RigidIn S₁) (h₂ : A.RigidIn S₂) (h₃ : A.RigidIn S₃) {c₁ c₂ c₃ : ι}
    (h12 : c₃ ∈ S₁ ∩ S₂) (h23 : c₁ ∈ S₂ ∩ S₃) (h13 : c₂ ∈ S₁ ∩ S₃)
    (h₁₂ : c₁ ≠ c₂) (h₁₃ : c₁ ≠ c₃) (h₂₃ : c₂ ≠ c₃) :
    A.RigidIn (S₁ ∪ S₂ ∪ S₃) := by
  -- the triangle of shared circles is a cluster: each of its sides lies in one of the three
  have htri : A.RigidIn ({c₁, c₂, c₃} : Set ι) := by
    filter_upwards [h₁, h₂, h₃] with q hr₁ hr₂ hr₃ hk i hi j hj
    have e₂₃ : dist (q c₂) (q c₃) = dist (A.center c₂) (A.center c₃) := hr₁ hk c₂ h13.1 c₃ h12.1
    have e₁₃ : dist (q c₁) (q c₃) = dist (A.center c₁) (A.center c₃) := hr₂ hk c₁ h23.1 c₃ h12.2
    have e₁₂ : dist (q c₁) (q c₂) = dist (A.center c₁) (A.center c₂) := hr₃ hk c₁ h23.2 c₂ h13.2
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp_all [dist_comm]
  have m₁ : A.RigidIn (({c₁, c₂, c₃} : Set ι) ∪ S₁) :=
    htri.union_of_two h₁ (by simp) h13.1 (by simp) h12.1 h₂₃
  have m₂ : A.RigidIn ((({c₁, c₂, c₃} : Set ι) ∪ S₁) ∪ S₂) :=
    m₁.union_of_two h₂ (by simp) h23.1 (by simp) h12.2 h₁₃
  have m₃ : A.RigidIn (((({c₁, c₂, c₃} : Set ι) ∪ S₁) ∪ S₂) ∪ S₃) :=
    m₂.union_of_two h₃ (by simp) h23.2 (by simp) h13.2 h₁₂
  exact m₃.mono (by intro x hx; rcases hx with (hx | hx) | hx <;> simp_all)

/-! ### R3: a taut chain across a cluster -/

/-- **Rule R3.** Let `S` be a cluster containing two circles `w 0` and `w k` at distance exactly
`2 k`, joined by a chain `w 0, w 1, …, w k` of `k` contacts. Then the chain merges into `S`.

The chain is taut: `k` steps of length `2` cannot span `2 k` with any slack, so by `chain_dist`
each `w i` is at distance exactly `2 i` from `w 0` and `2 (k - i)` from `w k` — and the same
holds after any contact-keeping motion, because the motion keeps the `k` contacts of the chain
and keeps the distance from `w 0` to `w k` (both lie in `S`). So every circle of
`S ∪ w '' Set.Iic k` keeps its distances to the two anchors `w 0` and `w k`, and the pinning
engine applies. The distances from a chain circle to the rest of the cluster come out of the same
engine call; they need no separate computation.

As in `chain_dist`, no collinearity, betweenness or convexity of the plane is used, even though
the chain circles are in fact collinear. -/
theorem RigidIn.union_chain [Finite ι] {A : Arrangement ι} {S : Set ι} (h : A.RigidIn S)
    {k : ℕ} (hk : 0 < k) (w : ℕ → ι) (h0 : w 0 ∈ S) (hkS : w k ∈ S)
    (hstep : ∀ i < k, Tangent A.center (w i) (w (i + 1)))
    (hlen : dist (A.center (w 0)) (A.center (w k)) = 2 * k) :
    A.RigidIn (S ∪ w '' Set.Iic k) := by
  have hne : A.center (w 0) ≠ A.center (w k) := by
    intro he
    rw [he, dist_self] at hlen
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hp := chain_dist (fun i => A.center (w i)) hstep hlen
  refine rigidIn_of_dist_two hne (Or.inl hkS) ?_
  filter_upwards [h] with q hr hkeep c hc
  have hq : ∀ i ≤ k, dist (q (w 0)) (q (w i)) = 2 * i ∧ dist (q (w i)) (q (w k)) = 2 * (k - i) :=
    chain_dist (fun i => q (w i)) (fun i hi => hkeep _ _ (hstep i hi))
      ((hr hkeep (w 0) h0 (w k) hkS).trans hlen)
  rcases hc with hcS | ⟨i, hi, rfl⟩
  · exact ⟨hr hkeep c hcS (w 0) h0, hr hkeep c hcS (w k) hkS⟩
  · exact ⟨by rw [dist_comm, (hq i hi).1, dist_comm (A.center (w i)), (hp i hi).1],
      by rw [(hq i hi).2, (hp i hi).2]⟩

/-! ### `O11` re-certified by the calculus -/

/-- **`O11` is rigid**, proved purely by the merging calculus.

Three clusters: the left chevron and the right chevron, each a rigid body fed in by
`rigidIn_of_comap`, and the bar `X Y` (circles `0` and `6`), an atom fed in by `rigidIn_pair`.
They pairwise share the hinge `H` (circle `5`, in both chevrons), `Y` (circle `6`, in the right
chevron and in the bar) and `X` (circle `0`, in the left chevron and in the bar). One
application of R2 merges all three; the union is everything by `o11Idx_cover`; and
`rigidIn_univ_iff` turns that into rigidity.

Note that the triangle `H Y X` of shared circles has sides `2 √3`, `2`, `2 √3`, so it is not
degenerate here — but R2 would not have cared if it were. Compare `Arrangement.o11_isRigid`,
which calls the hinge-and-bar lemma directly: this is the same mathematics assembled from the
general rules. -/
theorem o11_isRigid_of_cluster : o11.IsRigid := by
  rw [← rigidIn_univ_iff]
  have hleft : o11.RigidIn (Set.range o11LeftIdx) :=
    o11.rigidIn_of_comap o11LeftIdx o11LeftIdx_injective o11_comap_left_isRigid
  have hright : o11.RigidIn (Set.range o11RightIdx) :=
    o11.rigidIn_of_comap o11RightIdx o11RightIdx_injective o11_comap_right_isRigid
  have hbar : o11.RigidIn {0, 6} := rigidIn_pair o11_tangent_zero_six
  refine (hleft.union_of_ring hright hbar (c₁ := 6) (c₂ := 0) (c₃ := 5) ?_ ?_ ?_
    (by decide) (by decide) (by decide)).mono ?_
  · exact ⟨⟨5, by decide⟩, ⟨5, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, by simp⟩
  · exact ⟨⟨0, by decide⟩, by simp⟩
  · intro i _
    rcases o11Idx_cover i with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact Or.inl (Or.inl ⟨j, hj⟩)
    · exact Or.inl (Or.inr ⟨j, hj⟩)

end Arrangement

end RigidArrangements
