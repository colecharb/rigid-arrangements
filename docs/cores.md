# Rigid cores with 7 and 8 circles

> **Status (2026-10-15).** Hand proof, not yet formalized in Lean. Merged from three
> independent drafts after refereeing (see *Provenance*). Rigidity is used only through
> `Arrangement.IsRigid.touchesTwo`. No flex and no edge count is used. Every arrangement
> other than the flower is shown to be geometrically impossible.

## Statement

Let ρ := e^{iπ/3}. The **flower** F has centres 0 and 2ρ^k for k = 0, …, 5: a hexagon of
six circles around a seventh. In lattice coordinates (`latticePoint (a, b) = 2a + b(1 + i√3)`)
it is `ofLattice [(0,0),(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]`.

**Theorem\*.** Let A be an arrangement of n circles with 7 ≤ n ≤ 8 such that

- (T) every circle touches at least two others (`TouchesTwo`), and
- (C) no circle is removable (`IsCore`).

Then n = 7, and A is congruent to F (after relabelling and an isometry of the plane).

**Corollary.**
- (C7) Every rigid core of 7 circles is congruent to the flower.
- (C8) No rigid core has 8 circles.

*Proof.* A rigid arrangement of n ≥ 3 circles satisfies (T) (`IsRigid.touchesTwo`). ∎

**Converse.** F is a rigid core.
- Rigid: build it from the triangle {0, 2, 2ρ} by Henneberg steps, adding 2ρ², …, 2ρ⁵ in
  turn, each touching 0 and the previous outer circle.
- Core: every circle has at least 3 contacts, so none is removable.

## 0. Conventions and facts used

**Circles and contacts.** Circles are identified with their centres p_i ∈ ℂ. Distinct
centres are at least 2 apart, and distinct circles have distinct centres
(`center_injective`). Write i ~ j if |p_i − p_j| = 2. N(i) is the set of neighbours of i,
and deg i = |N(i)|.

**Angles.** Angles are in degrees. Put u(θ) := e^{iθ}. The *direction* of z ≠ 0 is
arg z mod 360°. The number ρ = u(60°) satisfies ρ² = ρ − 1, ρ³ = −1, ρ⁶ = 1 and
1 − ρ + ρ² = 0.

**Two products.**
- ⟨z, w⟩ := Re(z w̄).
- cross(z, w) := Im(z̄ w) = |z||w|·sin(dir w − dir z).

**Lines and segments.** For distinct circles a, b, put f_ab(x) := cross(p_b − p_a, x − p_a).
- f_ab is real-affine in x, so it is affine along every segment.
- Its zero set is the line ℓ_ab through p_a and p_b.
- [x, y] is the closed segment and (x, y) the open segment.

**Lexicographic positivity.** LexPos(z) means: Re z > 0, or Re z = 0 and Im z > 0
(Lean `LexPos`).

**(L) Properties of LexPos.**
- If LexPos z and LexPos w, then LexPos(z + w).
- If LexPos z and t > 0, then LexPos(tz).
- LexPos 0 is false.
- LexPos z and LexPos(−z) never hold together.

**Extreme circles and corners.** Circle i is *θ-extreme* (`IsExtreme θ i`) if
LexPos((p_i − p_j)·u(−θ)) for every j ≠ i.
- In words: its centre is furthest in direction u(θ), with ties broken towards u(θ + 90°).
- Equivalently: every p_j − p_i with j ≠ i has direction in the half-open arc
  (θ + 90°, θ + 270°].

A **corner** is a circle that is θ-extreme for some θ.

### Facts used

| | Statement | Lean |
|---|---|---|
| X1 | For each θ exactly one circle is θ-extreme. Call it E(θ). | existence: `exists_isExtreme`; uniqueness from (L) (new, 3 lines) |
| X2 | Being θ-extreme depends only on θ mod 360°. | `isExtreme_add_two_pi` |
| F1 | A rigid arrangement with n ≥ 3 satisfies (T). | `IsRigid.touchesTwo` |
| F2 | Under (T) and (C), every corner touches exactly 3 circles. | `IsExtreme.touchesExactlyThree` |
| F3 | Under (T) and (C), a θ-extreme circle is not (θ+δ)-extreme for 60° ≤ δ ≤ 180°. | `IsExtreme.not_isExtreme_add` |
| F4 | Under (T) and (C), with n ≥ 1, there are distinct circles e_0, …, e_5 with e_k (60k°)-extreme. | `exists_injective_isExtreme` |
| F5 | If j ≠ l are neighbours of i with directions β_j, β_l seen from p_i, then \|p_j − p_l\|² = 8 − 8cos(β_j − β_l). Since \|p_j − p_l\| ≥ 2, the two directions are at least 60° apart mod 360°, and any two real representatives differ by at least 60°. | `norm_sub_sq_of_norm_eq_two`, `pi_div_three_le_abs_arg_sub` (**private**: expose them) |

**Consequence of F3 and X2.** If a circle is extreme in directions α and β, then
α − β ≡ γ (mod 360°) for some γ with |γ| < 60°.

*Proof.* Write α − β = γ + 360°m with γ ∈ (−180°, 180°].
- If γ ≥ 60°, the circle is β-extreme and (β+γ)-extreme, against F3.
- If γ ≤ −60°, it is α-extreme and (α−γ)-extreme, against F3. ∎

## 1. Elementary lemmas

**Lemma 1 (contact segments are empty).** If i ~ j and k ∉ {i, j}, then p_k ∉ [p_i, p_j].

*Proof.* For x = p_i + λ(p_j − p_i) with λ ∈ [0, 1], we have
|x − p_i| + |x − p_j| = 2λ + 2(1 − λ) = 2. If x = p_k, both terms are ≥ 2. ∎

**Lemma 2 (contacts do not cross).** Let i ~ j and k ~ l, where i, j, k, l are four distinct
circles. Then [p_i, p_j] ∩ [p_k, p_l] = ∅.

*Proof.*
1. Suppose q = p_i + λa = p_k + μb, where a = p_j − p_i, b = p_l − p_k and λ, μ ∈ [0, 1].
2. The triangle inequality through q gives
   - |p_i − p_k| ≤ 2λ + 2μ,
   - |p_j − p_l| ≤ 2(1−λ) + 2(1−μ),
   - |p_i − p_l| ≤ 2λ + 2(1−μ),
   - |p_j − p_k| ≤ 2(1−λ) + 2μ.
3. Every left-hand side is ≥ 2. So λ + μ ≥ 1, λ + μ ≤ 1, λ ≥ μ and μ ≥ λ. Hence
   λ = μ = 1/2.
4. Then p_k − p_i = (a − b)/2 and p_l − p_i = (a + b)/2. Both have norm ≥ 2, so
   |a − b|² + |a + b|² ≥ 32.
5. But the parallelogram law gives |a − b|² + |a + b|² = 2|a|² + 2|b|² = 16. ✗ ∎

**Lemma 3 (at most six neighbours).** Every circle has at most 6 neighbours.

*Proof.*
1. For y ∈ N(i), let φ_y ∈ (−180°, 180°] be the principal argument of p_y − p_i.
2. By F5, |φ_y − φ_{y'}| ≥ 60° for y ≠ y'.
3. The six intervals (−180° + 60°s, −120° + 60°s], s = 0, …, 5, cover (−180°, 180°].
   Two arguments in the same interval differ by less than 60°.
4. So no interval holds two neighbours, and there are at most six (pigeonhole). ∎

**Lemma 4 (corners are extreme points).** Let v be a corner, and write
p_v = Σ_j λ_j p_{c_j} with λ_j ≥ 0 and Σ_j λ_j = 1. Then λ_j = 0 whenever c_j ≠ v.

*Proof.*
1. Say v is θ-extreme, and put R(z) := z·u(−θ).
2. Then 0 = Σ_j λ_j R(p_v − p_{c_j}). The terms with c_j = v vanish.
3. Every R(p_v − p_{c_j}) with c_j ≠ v is LexPos.
4. If some such λ_j were > 0, the sum would be LexPos by (L). But it is 0. ✗ ∎

Three consequences:

- **(4a)** A corner v does not lie in the open segment (p_c, p_{c'}) for circles c, c' ≠ v.
- **(4b)** Let a ≠ b be corners and c, c' any circles. If q ∈ [p_c, p_{c'}] lies on ℓ_ab,
  then q ∈ [p_a, p_b].

  *Proof.* Write q = p_a + t(p_b − p_a).
  - If t > 1, then p_b = (1 − 1/t)p_a + (1/t)q. This is a convex combination of
    p_a, p_c, p_{c'} with weight ≥ 1 − 1/t > 0 on a ≠ b, against Lemma 4 for b.
  - If t < 0, then p_a = (1/(1−t))q + (−t/(1−t))p_b, with positive weight on b ≠ a,
    against Lemma 4 for a. ∎
- **(4c)** No three distinct corners are collinear: the middle one would contradict (4a).

**Lemma 5 (middle neighbour).** Assume (T) and (C), and let x be a corner. Its three
neighbours (F2) can be labelled y_1, y_2, y_3 so that p_{y_1} and p_{y_3} lie strictly on
opposite sides of the line through p_x and p_{y_2}.

*Proof.*
1. Let x be θ-extreme. The neighbours' directions seen from p_x lie in the arc
   (θ + 90°, θ + 270°]. Choose representatives β_1 < β_2 < β_3 in that arc.
2. Then β_3 − β_1 < 180°. By F5, β_2 − β_1 ≥ 60° and β_3 − β_2 ≥ 60°.
3. Hence cross(p_{y_2} − p_x, p_{y_1} − p_x) = 4 sin(β_1 − β_2) < 0.
4. And cross(p_{y_2} − p_x, p_{y_3} − p_x) = 4 sin(β_3 − β_2) > 0. ∎

## 2. One exceptional circle

**Lemma E.** Assume (T) and (C). Let r be a circle such that every circle other than r is a
corner. Then every circle other than r touches r.

*Proof.* Throughout, ab denotes a contact with a, b ≠ r.

*Claim 0: p_r ∉ ℓ_ab.*
- a and b are corners. If p_r ∈ ℓ_ab, then (4b) with c = c' = r gives p_r ∈ [p_a, p_b].
- That contradicts Lemma 1.

*Orientation.* Orient f := f_ab so that f(p_r) < 0. Put Σ(ab) := {c : f(p_c) > 0}, the
circles strictly on the far side of ℓ_ab from r. Note that r, a, b ∉ Σ(ab). Call ab
*good* if Σ(ab) ≠ ∅.

*Claim 1. If x ≠ r does not touch r, and y_2 is a middle neighbour of x (Lemma 5), then
x y_2 is good.*
- y_2 ≠ r, and p_r lies off the line through p_x and p_{y_2} (Claim 0).
- y_1 and y_3 lie strictly on opposite sides of that line, so one of them lies on the far
  side from r.

*Setting up a contradiction.* Suppose some x_0 ≠ r does not touch r.
1. By Claim 1, good contacts exist. Choose a good contact ab with |Σ(ab)| minimal.
2. Pick x ∈ Σ(ab). Then x ≠ r, so x is a corner with exactly three neighbours (F2).

*Claim 2: N(x) ⊆ Σ(ab) ∪ {a, b}.* Let y ∈ N(x).
- If f(p_y) > 0, then y ∈ Σ(ab).
- If f(p_y) = 0, then (4b) with c = c' = y gives p_y ∈ [p_a, p_b], so y ∈ {a, b}
  by Lemma 1.
- If f(p_y) < 0:
  1. f vanishes at some q in the open segment (p_x, p_y).
  2. (4b) with c = x, c' = y gives q ∈ [p_a, p_b].
  3. The circles x, y, a, b are distinct, because f(p_x) > 0, f(p_y) < 0 and
     f(p_a) = f(p_b) = 0.
  4. So the contact segments [p_x, p_y] and [p_a, p_b] meet, against Lemma 2.

In particular r ∉ N(x), since f(p_r) < 0. By Claim 1, the middle neighbour y of x gives a
good contact xy, with y ≠ r and y ∈ Σ(ab) ∪ {a, b}. So f(p_x) > 0 and f(p_y) ≥ 0.

*Claim 3: Σ(xy) ⊆ Σ(ab), and x ∉ Σ(xy).*
1. x ∉ Σ(xy) because p_x ∈ ℓ_xy.
2. Let z ∈ Σ(xy), and suppose f(p_z) ≤ 0.
3. Orient g := f_xy so that g(p_r) < 0 < g(p_z). Then g vanishes at some s in the open
   segment (p_z, p_r).
4. Since f(p_z) ≤ 0 and f(p_r) < 0, and f is affine on the segment, f(s) < 0.
5. By (4b), applied to the corners x and y, s ∈ [p_x, p_y].
6. On [p_x, p_y], f ≥ 0, because f(p_x) > 0 and f(p_y) ≥ 0. ✗

Therefore |Σ(xy)| < |Σ(ab)| and xy is good. This contradicts the minimality of |Σ(ab)|. ∎

## 3. Exactly six corners

**Setting S6.**
- (T) and (C) hold, and the corners are exactly the circles e_0, …, e_5 of F4.
- Indices are taken mod 6. In particular e_6 = e_0, which is 360°-extreme by X2.
- Write W_k := [60k°, 60k° + 60°].

**Lemma S.** In setting S6 there are a unit complex number ŵ and reals L_0, …, L_5 ≥ 2 with
the following properties. Write ŵ_k := ŵρ^k (so ŵ_{k+6} = ŵ_k).

- **(S-a)** e_{k+1} − e_k = L_k ŵ_k. The corners form a convex hexagon that turns by exactly
  60° at each corner.
- **(S-b)** cross(ŵ_k, p − e_k) ≥ 0 for every k and every centre p. Each side lies on a
  supporting line, with all centres on its left.
- **(S-c)** N(e_k) consists of exactly three circles, with centres e_k + 2ŵ_k,
  e_k + 2ρŵ_k and e_k + 2ρ²ŵ_k.

*Step 1 (two candidates on each arc).*
1. Let θ ∈ W_k. Then E(θ) is a corner, so E(θ) = e_j for some j.
2. By F3 (with X2), θ − 60j° is within 60° of a multiple of 360°.
3. If j ≢ k, k+1 (mod 6), then 60j° is at angular distance ≥ 60° from every point of W_k.
4. Hence E(θ) ∈ {e_k, e_{k+1}}.

*Step 2 (the switching direction).*
1. Let w_k := e_{k+1} − e_k = L_k u(ψ_k), where L_k = |w_k| ≥ 2.
2. For θ ∈ W_k, Step 1 and X1 give: E(θ) = e_k if and only if
   LexPos((e_k − e_{k+1})·u(−θ)).
   - (⇒) holds by definition.
   - (⇐): e_{k+1} cannot also be θ-extreme, by (L).
3. Since (e_k − e_{k+1})·u(−θ) = L_k u(ψ_k + 180° − θ), this holds if and only if
   ψ_k − θ ∈ (90°, 270°] mod 360°.
4. Because E(60k°) = e_k, we may choose ψ_k ∈ (60k° + 90°, 60k° + 270°].
5. For θ ∈ W_k, then ψ_k − θ ∈ (30°, 270°], and the condition reads simply
   ψ_k − θ > 90°.
6. Because E(60k° + 60°) = e_{k+1} (use X2 when k = 5), ψ_k ≤ 60k° + 150°.
7. Put t_k := ψ_k − 90° ∈ (60k°, 60k° + 60°]. Then
   - E(θ) = e_k for θ ∈ [60k°, t_k),
   - E(θ) = e_{k+1} for θ ∈ [t_k, 60k° + 60°],
   - w_k = L_k u(t_k + 90°).

*Step 3 (equal turning).*
1. For 1 ≤ k ≤ 5, Step 2 on W_{k−1} and on W_k shows that e_k is θ-extreme for every
   θ ∈ [t_{k−1}, t_k).
2. Put t_{−1} := t_5 − 360° ∈ (−60°, 0°]. By X2, e_0 is θ-extreme on [t_{−1}, 0°], and by
   Step 2 on [0°, t_0). So item 1 also holds for k = 0.
3. If t_k − t_{k−1} > 60°, then e_k is extreme at both t_{k−1} and t_{k−1} + 60°, against F3.
4. Also t_k − t_{k−1} > 0, because t_{k−1} ≤ 60k° < t_k.
5. The six differences lie in (0°, 60°] and sum to t_5 − t_{−1} = 360°. So each equals 60°.
6. Put ŵ := u(t_0 + 90°). Then u(t_k + 90°) = ŵ_k, which gives (S-a).

*Step 4 (supporting lines).* Let p be any centre.
1. e_k is t_{k−1}-extreme (Step 3), so ⟨p − e_k, u(t_{k−1})⟩ ≤ 0.
2. e_{k+1} is t_k-extreme (Step 2), and ⟨e_{k+1} − e_k, u(t_k)⟩ = 0. So
   ⟨p − e_k, u(t_k)⟩ ≤ 0.
3. Since u(t_k) = −iŵ_k and u(t_{k−1}) = −iŵ_k ρ̄, these two inequalities read
   - Im((p − e_k)·ŵ̄_k) ≥ 0, which is (S-b), and
   - Im(ρ·(p − e_k)·ŵ̄_k) ≥ 0.

*Step 5 (neighbours of a corner).*
1. Let y ∈ N(e_k) and v := (p_y − e_k)/(2ŵ_k), a unit complex number.
2. Step 4 gives Im v ≥ 0 and Im(ρv) ≥ 0. So dir v ∈ [0°, 180°] ∩ [−60°, 120°] = [0°, 120°].
3. By F2, e_k has exactly three neighbours. By F5, their values of dir v are pairwise
   ≥ 60° apart.
4. So the values are exactly 0°, 60° and 120°: v ∈ {1, ρ, ρ²}, each taken once. This is
   (S-c). ∎

**Proposition H.** In setting S6, suppose at most two circles are not corners. Then
L_0 = … = L_5 = 2. Moreover:
- O := e_k + 2ρŵ_k does not depend on k;
- O is the centre of a circle o that is not a corner;
- N(e_k) = {e_{k−1}, e_{k+1}, o} for every k;
- e_k = O + 2ζρ^k, where ζ := ρ⁴ŵ.

*(H1) Closure.*
1. Summing (S-a) over k gives ŵ·Σ_k L_k ρ^k = 0.
2. Using ρ³ = −1 and ρ² = ρ − 1,
   Σ_k L_k ρ^k = (L_0 − L_3 − L_2 + L_5) + (L_1 − L_4 + L_2 − L_5)ρ.
3. Since ρ ∉ ℝ, both coefficients vanish:
   D := L_0 − L_3 = L_2 − L_5 = L_4 − L_1.

*(H2) Long sides carry non-corners.* Suppose L_k > 2 (call side k *long*).
1. By (S-c), a_k := e_k + 2ŵ_k is the centre of a neighbour of e_k.
2. Also z_k := e_{k+1} − 2ŵ_k = e_{k+1} + 2ρ²ŵ_{k+1} is the centre of a neighbour of
   e_{k+1}.
3. Both lie in the open segment (e_k, e_{k+1}), so neither is a corner (4a).
4. Non-overlap of a_k and e_{k+1} gives L_k − 2 ≥ 2.
5. Since |a_k − z_k| = |L_k − 4|, either
   - L_k = 4, and a_k = z_k is the midpoint, or
   - L_k ≥ 6, and a_k ≠ z_k.

*(H3) Open sides are disjoint.* If a point q lies in both open sides (e_k, e_{k+1}) and
(e_m, e_{m+1}), then k = m.
1. g(x) := cross(ŵ_k, x − e_k) is ≥ 0 at every centre (S-b), and g(q) = 0.
2. Write q = (1 − s)e_m + s·e_{m+1} with 0 < s < 1. Then g(e_m) = g(e_{m+1}) = 0.
3. So e_k, e_{k+1}, e_m, e_{m+1} are collinear.
4. If m ≠ k, at least three of them are distinct corners, against (4c).

*(H4) Every side has length 2.* Suppose not.
- **If D ≠ 0.** Each of the pairs {0,3}, {2,5}, {1,4} has unequal lengths, so it contains a
  long side. The corresponding circles a_k are three non-corners, distinct by (H3). ✗
- **If D = 0.** Some long side k has L_{k+3} = L_k, so a_k ≠ a_{k+3} are two non-corners.
  - If L_k ≥ 6, then z_k is a third non-corner (it differs from a_k by H2 and from a_{k+3}
    by H3). ✗
  - If another side j ∉ {k, k+3} is long, then a_j is a third. ✗
  - Otherwise L_k = L_{k+3} = 4 and the other four sides have length 2.
    1. Relative to e_k, in units of ŵ_k, the corners e_k, …, e_{k+5} sit at
       0, 4, 4+2ρ, 2+4ρ, −2+4ρ, −2+2ρ.
    2. The circles a_k and a_{k+3} sit at 2 and 4ρ.
    3. By (S-c), X := e_k + 2ρŵ_k is the centre of a neighbour of e_k.
    4. In Cartesian form, 2ρ = 1 + i√3. The eight listed points are
       0, 4, 5+i√3, 4+2i√3, 2i√3, −1+i√3, 2, 2+2i√3, and none equals it.
    5. So X is a third non-corner. ✗

*(H5) The hub.* Now every L_k = 2.
1. Then e_k + 2ŵ_k = e_{k+1}, and e_k + 2ρ²ŵ_k = e_k − 2ŵ_{k−1} = e_{k−1}.
2. Put b_k := e_k + 2ρŵ_k. Then b_{k+1} − b_k = 2ŵ_k(1 − ρ + ρ²) = 0.
3. So all b_k equal one point O. By (S-c), O is the centre of a common neighbour o of all
   six corners, and N(e_k) = {e_{k+1}, o, e_{k−1}}.
4. |O − e_j| = 2 for every j, so o is no e_j, hence not a corner.
5. Finally e_k = O − 2ρŵ_k = O + 2ρ⁴ŵρ^k. ∎

## 4. Proof of Theorem\*

Let A satisfy (T) and (C) with 7 ≤ n ≤ 8. Fix e_0, …, e_5 as in F4.

**Case A: some corner is not among e_0, …, e_5.**
1. At least 7 circles are corners, so at most n − 7 ≤ 1 circle is not.
2. Let r be that circle if it exists, and r := e_0 otherwise.
3. By Lemma E, all n − 1 ≥ 6 other circles touch r.
4. If r is a corner, this contradicts F2 (deg r = 3).
5. Otherwise all n − 1 other circles are corners, so n − 1 ≥ 7. Then n = 8 and r has
   7 neighbours, against Lemma 3.

**Case B: the corners are exactly e_0, …, e_5.** This is setting S6, with at most
n − 6 ≤ 2 non-corners. Proposition H applies.
- **n = 8.** The eighth circle d ∉ {e_0, …, e_5, o} touches no corner, because
  N(e_k) = {e_{k±1}, o}. So N(d) ⊆ {o}, against (T).
- **n = 7.** The circles are e_0, …, e_5 and o. The map z ↦ ζ̄(z − O) is an isometry
  sending O to 0 and e_k to 2ρ^k. So A ≅ F. ∎

## 5. Remarks

1. **Only (T) and (C) are used.** The same argument also gives "(T) and (C) with
   1 ≤ n ≤ 8 imply n = 7":
   - F4 forces n ≥ 6.
   - For n = 6, Case A needs 7 corners, and in Case B Proposition H produces a non-corner o
     although there is none.

   This reproves `NoCoresBetween 3 6` without the prism flex. That is consistent: the prism
   cannot be realised by unit circles.
2. **Where the method stops.** The hexagon with sides 4, 2, 2, 4, 2, 2 from (H4) becomes the
   exploratory 10-circle lattice core once its two midpoints and the two points
   e_k + 2ρŵ_k = 1+i√3 and e_{k+3} + 2ρŵ_{k+3} = 3+i√3 are added. So "at most two
   non-corners" is exactly where the method stops.
3. **Counts.** With the `LatticeCover` machinery of `Small.lean`, (C7) and (C8) give exact
   counts:
   - 4 rigid arrangements of 7 circles;
   - 9 rigid arrangements of 8 circles;
   - and every rigid arrangement of at most 8 circles lies on the triangular lattice.

   The flower enters as a core: it has no circle with exactly two contacts, so it is not an
   extension of a 6-circle shape.

## Provenance

Three drafts were written independently and refereed:

1. a case analysis on the contact graph (17 leaf cases);
2. a convex hull polygon, a chord lemma and an equiangular hexagon;
3. extreme circles (corners), Lemma E and Lemma S.

This document follows (3), restructured. (2) reaches the same equiangular hexagon. (1) is an
independent graph-theoretic proof of the same conclusion.

Repairs made here:
- Lemma 2 is proved without strict convexity.
- The wrap-around cases use X2 explicitly.
- E(θ) is backed by the uniqueness fact X1.
- Lemma 3 is proved by pigeonhole.
- L_k ∈ {2, 4} ∪ [6, ∞) is made explicit.
- Claim 3 of Lemma E is shortened.
- The n = 7 case goes through Proposition H.
