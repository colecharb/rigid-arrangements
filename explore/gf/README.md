# Strips of bounded width: brute force, transfer matrices, generating functions

Two self-contained exploratory programs. Plain Lean 4 plus `Std` — no Mathlib, so they compile in a
few seconds. Everything they produce is **[computed]**: these are programs, not proofs, and they use
no `sorry` and no `native_decide` because they contain no theorems at all.

| file | contents |
| --- | --- |
| `Strip.lean` | brute force over strips: exact and mod-p rank, flex certificates, the second-order criterion, an independent R1–R4 classifier, generating-function series arithmetic, and the published width-3 structural rule as a predicate |
| `Transfer.lean` | line-sum transfer matrix, state-set closure, layered dynamic programming over columns, linear-recurrence fitting, growth constants |

Build and run as for the other `explore/` programs:

```bash
lake env lean -c /tmp/strip.c explore/gf/Strip.lean && lake env leanc -O3 /tmp/strip.c -o /tmp/strip
```

## The local criterion the transfer matrix rests on

A *line* is a maximal straight run of the set in one of the three lattice directions. With `L` lines
and `E` contacts, counting contacts along lines gives the identity

    e(S) = 3|S| − R₁(S) − R₂(S) − R₃(S),    L = R₁ + R₂ + R₃,

and because the three plane directions satisfy u₀ − u₁ + u₂ = 0, an infinitesimal flex is exactly one
scalar per line subject to `x_{l₀} − x_{l₁} + x_{l₂} = 0` at every site. So the nullity is `L − rank`
and infinitesimal rigidity is nullity 3. Scanning by columns, only `2W − 1` lines can still grow, so a
transfer-matrix state is (column mask, the subspace of admissible restrictions to the open slots, the
dimension of partial solutions vanishing on all of them). This is the same identity that drives the
case-(b) search in `explore/caseb/`.

## What was found

| width | status | growth per circle | generating function |
|---:|---|---:|---|
| 3 | state set closes | 1.429108 | rational, denominator (1−x)(1−x²−x³−x⁵); series to n = 2000 |
| 4 | closes: 91 states, BFS depth 6 | 1.709227 | rational, order 27, recurrence valid from n = 33, validated over 1200 terms |
| 5 | does **not** close; layered DP instead | 1.884269 (300 exact terms) | no linear recurrence of order ≤ 70 fits |
| 6 | layered DP, n ≤ 52 | ≈ 2.019, still falling | — |

- **The published width-3 numbers are confirmed three independent ways** — expanding the generating
  function of `docs/offlattice.md` §5, brute force, and the transfer matrix — and extended by two
  terms: C₃(31) = 26205, C₃(32) = 37340. One caveat for readers of that formula: the corrections must
  be applied *after* the quarter, `C₃ = (T₃+V+R+H)/4 − x⁴ − x⁵ − 2x⁶ − 2x⁷`, or the n = 6, 7 terms come
  out as 3, 4 instead of 2, 3.
- The §5 *structural* rule, which was never machine-checked, agrees with exact rank on all 5 505 626
  connected min-degree-2 three-row sets up to n = 19, with zero discrepancies either way.
- **Bounded width makes infinitesimal rigidity local, but not rigidity.** For width ≤ 4 and n ≤ 17 the
  two coincide (checked unconditionally: all 6.2 M non-infinitesimally-rigid candidates at n = 17 were
  certified flexible). From n = 18 they separate, so the smallest singular rigid lattice arrangement
  has width exactly 4.
- **Width 5 fails diagnostically.** New states keep appearing at ~113 per column, and the subspace
  denominators grow *linearly* — exactly `6⌊d/2⌋ − 11` at every depth d from 8 to 352, still matching
  at depths 405, 485, 616, 792. Linear rather than exponential growth is the signature of a parabolic
  recursion: a projective hinge point that drifts by a fixed map per repeated column and never
  returns. That is the same concurrency degeneracy that makes S20 emergent, and S20 has width 5.
- **Constructibility by width:** every rigid width-3 class to n = 32 is constructible under R1+R2;
  every infinitesimally rigid width-4 class to n = 23 is constructible under R1+R2+R4, with R3 never
  needed. Independently, all 112 emergent classes of the census have minimum width 5 (61) or 6 (51).
  So emergence begins at width 5.

See `docs/emergent.md` §8 and `docs/constructible-plan.md` §4 for what this means for counting.
