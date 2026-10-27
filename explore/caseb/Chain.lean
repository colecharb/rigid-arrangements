namespace CaseB

/-!
# E30-type taut chains, exactly

A body holds two of its circles `P`, `Q` exactly `2(k+1)` apart and a straight chain of `k`
free circles runs between them; `k+1` links of length 2 spanning `2(k+1)` must be collinear and
in order, so the arrangement is rigid (but never *infinitesimally* rigid — each chain circle has
two neighbours exactly 4 apart, `Arrangement.not_isInfRigid_of_taut`).

`docs/offlattice.md` §8: the anchor vector must have norm `(k+1)²` without being `(k+1)` times a
unit, which needs `k+1` divisible by a prime `≡ 1 mod 3`; so `k+1 ≥ 7`, `k ≥ 6`.  Larger `k+1`
means both a longer chain and a longer span, hence a bigger body, so `k+1 = 7` is the only case
worth searching.  Of the 18 lattice vectors of `eN = 49`, six are `7 ×` a unit (those give an
on-lattice chain) and the other twelve form a single orbit under the 12 lattice symmetries, so
**up to symmetry the only choice is `Q − P = (3,5)`** — the one E30 uses.

Everything here is exact integer arithmetic: with `P = (0,0)`, `Q = (3,5)` and chain points
`c_j = (j/7)·(11, 5√3)`, the squared distance from lattice site `(a,b)` to `c_j` scaled by 49 is

    49 d² = (14a + 7b − 11j)² + 3(7b − 5j)²,

an integer, and the contact condition `d = 2` is `49 d² = 196`.  Likewise, scaled by 49, the
squared perpendicular distance from `(a,b)` to the line `PQ` is `3(5a − 3b)²` and the coordinate
along `PQ` is `(11a + 13b)/7`.
-/

namespace Chain

def P : Site := (0, 0)
def Q : Site := (3, 5)

/-- `49 ×` the squared distance from site `p` to the `j`-th chain point. -/
def clear49 (p : Site) (j : Int) : Int :=
  let u := 14 * p.1 + 7 * p.2 - 11 * j
  let v := 7 * p.2 - 5 * j
  u * u + 3 * v * v

/-- a body site must keep every chain circle at distance `≥ 2`, touching one only at the two
designated ends (an extra body/chain contact would make that chain circle a lattice circle). -/
def allowed (p : Site) : Bool :=
  (List.range 6).all fun jj =>
    let j : Int := (jj : Int) + 1
    let c := clear49 p j
    c > 196 || (c == 196 && ((p == P && j == 1) || (p == Q && j == 6)))

/-- `49 ×` the squared distance from `p` to the line `PQ`. -/
def perp49 (p : Site) : Int := 3 * (5 * p.1 - 3 * p.2) ^ 2
/-- `7 ×` the coordinate of `p` along `PQ` (0 at `P`, 98 at `Q`). -/
def along7 (p : Site) : Int := 11 * p.1 + 13 * p.2

/-- the window: allowed sites in a band of half-width `√(w49/49)` about `PQ`, not more than
`ext/7` beyond either end.  Capped at 64 sites so that sets are `UInt64` masks. -/
def window (w49 ext : Int) : Array Site := Id.run do
  let mut out := #[]
  for a in [0:25] do
    for b in [0:25] do
      let p : Site := ((a : Int) - 10, (b : Int) - 8)
      if allowed p && perp49 p ≤ w49 && -ext ≤ along7 p && along7 p ≤ 98 + ext then
        out := out.push p
  return out

/-- E30's body, `docs/offlattice.md` §8, in build order. -/
def e30Body : Array Site :=
  #[(0,0), (-1,0), (-1,1), (-2,1), (-2,2), (-1,2), (-2,3), (-1,3), (-2,4), (-1,4), (0,3), (0,4),
    (-1,5), (0,5), (-1,6), (0,6), (1,5), (1,6), (0,7), (1,7), (2,6), (2,7), (3,6), (3,5)]

end Chain

/-- exact check of a complete E30-type arrangement: body + 6 chain circles. -/
def chainReport (body : Array Site) : String := Id.run do
  let mut out : Array String := #[]
  let m := body.size
  out := out.push s!"  body {m} sites, {(contacts body).size} contacts, exact rank \
    {rigRank body} (2m−3 = {2 * m - 3}), infinitesimally rigid {infRigid body}"
  out := out.push s!"  P = {showSite Chain.P} ∈ body: {body.contains Chain.P}; \
    Q = {showSite Chain.Q} ∈ body: {body.contains Chain.Q}; eN (Q−P) = {eN (sub Chain.Q Chain.P)}"
  -- 7 ∤ (3+5ω): else (3,5) = 7·unit
  out := out.push s!"  (3,5) is 7 × a unit: \
    {(Chain.Q.1 % 7 == 0 && Chain.Q.2 % 7 == 0)}  (so the chain direction is not a lattice one)"
  let mut clearOk := true
  let mut worst : Int := 1000000
  let mut worstAt : Site × Int := ((0,0), 0)
  let mut extra := 0
  for p in body do
    for jj in [0:6] do
      let j : Int := (jj : Int) + 1
      let c := Chain.clear49 p j
      if c < 196 then clearOk := false
      if c == 196 && !((p == Chain.P && j == 1) || (p == Chain.Q && j == 6)) then
        extra := extra + 1
      if c < worst && !((p == Chain.P && j == 1) || (p == Chain.Q && j == 6)) then
        worst := c; worstAt := (p, j)
  out := out.push s!"  no body/chain overlap: {clearOk}; extra body/chain contacts: {extra}; \
    tightest non-contact pair {showSite worstAt.1}–c{worstAt.2} at 49d² = {worst} (> 196)"
  out := out.push s!"  chain points are not lattice points: \
    {(List.range 6).all fun jj => (11 * ((jj : Int) + 1)) % 7 != 0}"
  out := out.push s!"  n = {m + 6}; contacts = {(contacts body).size + 7} \
    (2n−3 = {2 * (m + 6) - 3}); rigid by tautness, not infinitesimally rigid"
  return String.intercalate "\n" out.toList

def modeChain (w49 ext : Int) (cap tries nodeCap : Nat) : IO Unit := do
  IO.println s!"E30-type chain: P = {showSite Chain.P}, Q = {showSite Chain.Q}, \
    6 chain circles, |PQ| = 14 = 2·7"
  IO.println "E30's own body, rechecked exactly:"
  IO.println (chainReport Chain.e30Body)
  IO.println s!"E30's body fits the band: max 49·perp² = \
    {Chain.e30Body.foldl (fun acc p => max acc (Chain.perp49 p)) 0}, along7 range \
    [{Chain.e30Body.foldl (fun acc p => min acc (Chain.along7 p)) 1000}, \
    {Chain.e30Body.foldl (fun acc p => max acc (Chain.along7 p)) (-1000)}]"
  let pts := Chain.window w49 ext
  IO.println s!"window (49·perp² ≤ {w49}, −{ext} ≤ along7 ≤ {98 + ext}): {pts.size} allowed sites"
  if pts.size > 64 then
    IO.println "  (more than 64 sites: narrow the band)"
    return
  IO.println s!"  {showSites pts}"
  let terms := #[(pts.findIdx? (· == Chain.P)).get!, (pts.findIdx? (· == Chain.Q)).get!]
  let R := mkRegion pts terms
  IO.println s!"  shortest allowed P→Q connection (steiner lower bound) = {steiner R} sites"
  let C := mkCells R
  let (nc, T) := cellSteiner R C
  let S0 := cellsToSites C T R.pts.size
  let mut bestS : BS := 0
  let mut bestSz := 1000
  if nc > C.tri.size then IO.println "  no connected allowed cell family covers P and Q"
  else
    IO.println s!"  cells {C.tri.size}; covering cell family {nc} cells, {BS.card S0} corners, \
      legal body {goodBody R S0}"
    if goodBody R S0 then
      let Sh := shrink R S0
      bestS := Sh; bestSz := BS.card Sh
      IO.println s!"  shrunk to {bestSz} sites"
  match greedyRigid R cap tries with
  | none => IO.println s!"  greedy found no body of ≤ {cap} sites"
  | some S => if goodBody R S && BS.card S < bestSz then bestSz := BS.card S; bestS := S
  if bestSz > cap then IO.println "  no body constructed" else
  IO.println s!"  best body found: {bestSz} sites → n = {bestSz + 6}"
  IO.println s!"  {showSites (subPts R bestS)}"
  IO.println (chainReport (subPts R bestS))
  let mut proved := 0
  for m in [(steiner R):bestSz] do
    let st := bb R nodeCap (bit R.terms[0]!) 0 1 ⟨m + 1, 0, 0, true⟩
    if st.best ≤ m then
      IO.println s!"  !! found a body of {st.best} sites: {showSites (subPts R st.bestSet)}"
      IO.println (chainReport (subPts R st.bestSet))
      break
    if st.complete then proved := m
    else
      IO.println s!"  exhaustive search incomplete at size {m} ({st.nodes} nodes)"
      break
  IO.println s!"  exhaustively excluded: no infinitesimally rigid body of ≤ {proved} sites in \
    this window, so no E30-type arrangement with n ≤ {proved + 6}"

end CaseB
