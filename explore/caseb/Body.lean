namespace CaseB

/-!
# Minimal rigid lattice bodies in a punctured window

Given a window of *allowed* lattice sites (those far enough from the free circles) and a set of
*required* sites (the anchors), find the smallest infinitesimally rigid lattice set inside the
window containing all of them.  Two numbers are produced:

* `steiner`: the exact minimum size of a **connected** allowed set containing the anchors.  Any
  infinitesimally rigid framework is connected, so this is a lower bound on the body — *for
  bodies inside the window*.  Run it on two window radii to see whether it is window-stable.
* `minRigid`: branch and bound over connected allowed sets containing the anchors.  When it
  finishes (`complete = true`) its answer is the exact minimum inside the window.

The branch and bound represents sets as `UInt64` masks, so it needs a window of at most 64 sites;
`steiner` works for any size.
-/

abbrev BS := UInt64

@[inline] def bit (i : Nat) : BS := (1 : UInt64) <<< (UInt64.ofNat i)
@[inline] def BS.has (s : BS) (i : Nat) : Bool := s &&& bit i != 0
def BS.card (s : BS) : Nat := Id.run do
  let mut c := 0
  let mut x := s
  while x != 0 do
    c := c + 1
    x := x &&& (x - 1)
  return c
def BS.toList (s : BS) (n : Nat) : List Nat := (List.range n).filter (BS.has s)

structure Region where
  pts : Array Site
  nbr : Array (Array Nat)
  adj : Array BS            -- only meaningful when `pts.size ≤ 64`
  terms : Array Nat
  /-- `degPrefix[t]` = the sum of the `t` largest degrees available in the window: an upper
  bound on the contacts that `t` further sites can bring. -/
  degPrefix : Array Nat
  /-- `termDist[i][j]` = site-graph distance between terminals `i` and `j` in the *whole* window.
  Removing sites can only lengthen paths, so this is a valid underestimate of the live
  distance, which is all the lower bounds need. -/
  termDist : Array (Array Nat)
  /-- the exact minimum size of a connected allowed set containing every terminal: a floor on
  every body inside the window, since a rigid framework is connected. -/
  floor : Nat
  /-- `ord[d]` lists the window's sites in order along the lines of direction `d`
  (`d = 0, 1, 2` for `(1,0)`, `(0,1)`, `(1,−1)`), sorted by `(line, position)`. -/
  ord : Array (Array Nat)
  lineNo : Array (Array Int)
  linePos : Array (Array Int)
  deriving Inhabited

/-- plain BFS from one site, over `nbr` (so it works for windows of more than 64 sites). -/
def bfsFrom (R : Region) (s : Nat) : Array Nat := Id.run do
  let n := R.pts.size
  let mut d : Array Nat := Array.replicate n (n + 1)
  d := d.set! s 0
  let mut fr : Array Nat := #[s]
  while fr.size > 0 do
    let mut nx : Array Nat := #[]
    for u in fr do
      for v in R.nbr[u]! do
        if d[v]! == n + 1 then
          d := d.set! v (d[u]! + 1)
          nx := nx.push v
    fr := nx
  return d

/-! ## Node-weighted Steiner tree (exact), unit node weights -/

/-- minimum number of sites of a connected subset containing every terminal (Dreyfus–Wagner over
the node-weighted graph, unit weights).  Takes the adjacency lists directly, so `mkRegion` can
call it while building the region. -/
def steinerOf (n : Nat) (nbr : Array (Array Nat)) (terms : Array Nat) : Nat := Id.run do
  let k := terms.size
  if k == 0 || n == 0 then return 0
  let inf := n + 1
  let full := (1 <<< k) - 1
  let mut dp : Array Nat := Array.replicate ((full + 1) * n) inf
  for i in [0:k] do
    dp := dp.set! ((1 <<< i) * n + terms[i]!) 1
  for mask in [1:full+1] do
    let mut sub := (mask - 1) &&& mask
    while sub > 0 do
      let other := mask ^^^ sub
      if sub < other then
        for v in [0:n] do
          let a := dp[sub * n + v]!
          let b := dp[other * n + v]!
          if a < inf && b < inf && a + b - 1 < dp[mask * n + v]! then
            dp := dp.set! (mask * n + v) (a + b - 1)
      sub := (sub - 1) &&& mask
    for _ in [0:n] do
      let mut changed := false
      for v in [0:n] do
        let dv := dp[mask * n + v]!
        if dv < inf then
          for u in nbr[v]! do
            if dv + 1 < dp[mask * n + u]! then
              dp := dp.set! (mask * n + u) (dv + 1); changed := true
      if !changed then break
  let mut best := inf
  for v in [0:n] do
    if dp[full * n + v]! < best then best := dp[full * n + v]!
  return best

/-- minimum number of sites of a connected subset of the region containing every terminal. -/
def steiner (R : Region) : Nat := steinerOf R.pts.size R.nbr R.terms

def mkRegion (pts : Array Site) (terms : Array Nat) : Region := Id.run do
  let n := pts.size
  let mut nbr : Array (Array Nat) := Array.replicate n #[]
  let mut adj : Array BS := Array.replicate n 0
  for i in [0:n] do
    for j in [0:n] do
      if i != j && eN (sub pts[i]! pts[j]!) == 1 then
        nbr := nbr.set! i (nbr[i]!.push j)
        if n ≤ 64 then adj := adj.set! i (adj[i]! ||| bit j)
  -- degrees raised to at least 2, which keeps the bound valid and makes it monotone in the
  -- target size, so checking it at the largest target size suffices
  let ds := ((List.range n).map fun i => max nbr[i]!.size 2).toArray.qsort (· > ·)
  let mut pre : Array Nat := #[0]
  for i in [0:n] do pre := pre.push (pre[i]! + ds[i]!)
  -- line order in each of the three lattice directions
  let key (d : Nat) (i : Nat) : Int × Int :=
    let p := pts[i]!
    if d == 0 then (p.2, p.1) else if d == 1 then (p.1, p.2) else (p.1 + p.2, p.1)
  let all := (List.range n).toArray
  let mut ord : Array (Array Nat) := #[]
  let mut lns : Array (Array Int) := #[]
  let mut pss : Array (Array Int) := #[]
  for d in [0:3] do
    ord := ord.push (all.qsort fun i j =>
      let a := key d i
      let b := key d j
      a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
    lns := lns.push (all.map fun i => (key d i).1)
    pss := pss.push (all.map fun i => (key d i).2)
  let R0 : Region := ⟨pts, nbr, adj, terms, pre, #[], 0, ord, lns, pss⟩
  let mut td : Array (Array Nat) := #[]
  for i in [0:terms.size] do
    let d := bfsFrom R0 terms[i]!
    td := td.push (terms.map (fun t => d[t]!))
  return { R0 with termDist := td, floor := steinerOf n nbr terms }

/-- BFS distance (in sites) from the set `src` to every node, avoiding `ex`; `n+1` = unreachable.
Allocation-free bit iteration: this is the inner loop of the branch and bound. -/
def dists (R : Region) (src : BS) (ex : BS) : Array Nat := Id.run do
  let n := R.pts.size
  let mut d : Array Nat := Array.replicate n (n + 1)
  let mut seen := src
  for i in [0:n] do
    if BS.has src i then d := d.set! i 0
  let mut frontier := src
  let mut k := 0
  while frontier != 0 do
    k := k + 1
    let mut nxt : BS := 0
    for i in [0:n] do
      if BS.has frontier i then nxt := nxt ||| R.adj[i]!
    nxt := nxt &&& (~~~ex) &&& (~~~seen)
    for i in [0:n] do
      if BS.has nxt i then d := d.set! i k
    seen := seen ||| nxt
    frontier := nxt
  return d

/-- the terminals not yet in `inS`, with the number of further sites needed to reach the
farthest one; `none` if one of them is unreachable.  Stops as soon as all are found. -/
def reachDist (R : Region) (inS ex : BS) : Option Nat := Id.run do
  let n := R.pts.size
  let mut need : BS := 0
  let mut cnt := 0
  for t in R.terms do
    if !BS.has inS t && !BS.has need t then need := need ||| bit t; cnt := cnt + 1
  if cnt == 0 then return some 0
  let mut seen := inS
  let mut frontier := inS
  let mut k := 0
  while frontier != 0 do
    k := k + 1
    let mut nxt : BS := 0
    for i in [0:n] do
      if BS.has frontier i then nxt := nxt ||| R.adj[i]!
    nxt := nxt &&& (~~~ex) &&& (~~~seen)
    if nxt == 0 then return none
    for i in [0:n] do
      if BS.has nxt i && BS.has need i then cnt := cnt - 1
    if cnt == 0 then return some k
    seen := seen ||| nxt
    frontier := nxt
  return none

/-! ## Branch and bound for the minimum infinitesimally rigid set -/

structure BBState where
  best : Nat
  bestSet : BS
  nodes : Nat
  complete : Bool
  deriving Inhabited

def subPts (R : Region) (s : BS) : Array Site :=
  (BS.toList s R.pts.size).foldl (fun acc i => acc.push R.pts[i]!) #[]

/-- a legal body: at least a triangle, contains every anchor, infinitesimally rigid. -/
def goodBody (R : Region) (s : BS) : Bool :=
  BS.card s ≥ 3 && R.terms.all (BS.has s) && infRigid (subPts R s)

/-- live site-graph distances from `inS` to each terminal (`0` for the ones already in `inS`);
`none` as soon as some terminal is unreachable in the live region. -/
def reachDists (R : Region) (inS ex : BS) : Option (Array Nat) := Id.run do
  let n := R.pts.size
  let k := R.terms.size
  let mut d : Array Nat := Array.replicate k 0
  let mut left := 0
  for i in [0:k] do
    if !BS.has inS R.terms[i]! then left := left + 1
  if left == 0 then return some d
  let mut seen := inS
  let mut frontier := inS
  let mut step := 0
  while frontier != 0 do
    step := step + 1
    let mut nxt : BS := 0
    for i in [0:n] do
      if BS.has frontier i then nxt := nxt ||| R.adj[i]!
    nxt := nxt &&& (~~~ex) &&& (~~~seen)
    if nxt == 0 then return none
    for i in [0:k] do
      if d[i]! == 0 && !BS.has inS R.terms[i]! && BS.has nxt R.terms[i]! then
        d := d.set! i step
        left := left - 1
    if left == 0 then return some d
    seen := seen ||| nxt
    frontier := nxt
  return none

/-- Lower bound on the number of sites still to be added, given the live distances `d` from the
chosen set to each uncovered terminal.

Let `T` be any connected site set containing the chosen set `S` and all the terminals.  Contract
`S` to a single node `s*`; a spanning tree of the contracted `T` has exactly `added` edges, where
`added = |T \\ S|`.  Take `q = 1 + #uncovered` terminals `s*, a, b, …` and a tree spanning them
inside that tree: each of its edges splits the terminals into two parts, so

    Σ over pairs of distances = Σ over edges (n₁·n₂) ≤ ⌊q²/4⌋ · added,

hence `added ≥ ⌈(Σ pairs)/⌊q²/4⌋⌉`.  Every distance must be a *contracted* one — moving inside
`S` is free — so the `s*`–`a` term is `d a` and the `a`–`b` term is
`min (termDist a b) (d a + d b)`; both underestimate the contracted distance in `T`, which is all
the bound needs.  (Using the plain `termDist a b` would be WRONG: `S` can be long and join two
terminals near its two ends at a cost of one site each.)  Summing over the pairs of a
*sub*-collection is also valid, so the bound is maximised over the single-terminal case
(`max dᵢ`), every pair, every triple, and the whole set. -/
def steinerPairBound (R : Region) (d : Array Nat) : Nat := Id.run do
  let k := R.terms.size
  let mut un : Array Nat := #[]            -- indices of the uncovered terminals
  for i in [0:k] do
    if d[i]! > 0 then un := un.push i
  let mut bnd := 0
  for i in un do
    if d[i]! > bnd then bnd := d[i]!
  -- every sub-collection of the uncovered terminals, together with the chosen set
  let u := un.size
  for mask in [1:(1 <<< u)] do
    let mut sel : Array Nat := #[]
    for t in [0:u] do
      if (mask >>> t) &&& 1 == 1 then sel := sel.push un[t]!
    if sel.size ≥ 2 then
      let q := sel.size + 1
      let den := (q * q) / 4
      if den > 0 then
        let mut tot := 0
        for a in sel do tot := tot + d[a]!            -- pairs {s*, a}
        for a in [0:sel.size] do
          for c in [a+1:sel.size] do
            let ia := sel[a]!
            let ic := sel[c]!
            tot := tot + min R.termDist[ia]![ic]! (d[ia]! + d[ic]!)
        let v := (tot + den - 1) / den
        if v > bnd then bnd := v
  return bnd

/-! ### The run bound

Every contact of a lattice set points along one of the three lattice directions, and along one
line in one direction the set is a union of maximal runs, a run of `p` sites carrying `p − 1`
contacts.  Summing over the three directions gives the **exact identity**

    e(S) = 3·|S| − R₁(S) − R₂(S) − R₃(S),

where `R_d` counts the maximal runs along the lines of direction `d`.  Infinitesimal rigidity
needs `e ≥ 2|S| − 3`, so

    |S| ≥ R₁ + R₂ + R₃ − 3.

(H30's own body makes this tight: 26 sites, 49 contacts, `ΣR = 78 − 49 = 29 = 26 + 3`.)

`runBound` evaluates a lower bound on `ΣR` of any final set `S*` with `inS ⊆ S* ⊆ window \\ ex`:
along each line, group the chosen sites by the maximal stretches that are free of `ex` **and**
unbroken in the window (a position missing from the window can never be filled either), and count
the stretches that hold at least one chosen site.  Runs of `S*` cannot straddle two such
stretches, so each contributes at least one run.  The count only grows as sites are chosen or
excluded, which is what makes it a usable bound — in particular it prunes the *exclusion*
branches of the search, which the connectivity bounds barely touch. -/
def runBound (R : Region) (inS ex : BS) : Nat := Id.run do
  let mut groups := 0
  for d in [0:3] do
    let od := R.ord[d]!
    let ld := R.lineNo[d]!
    let pd := R.linePos[d]!
    let mut line : Int := 0
    let mut lastPos : Int := 0
    let mut first := true
    let mut opn := false
    for i in od do
      if first || ld[i]! != line then
        line := ld[i]!
        opn := false
        first := false
      else if pd[i]! != lastPos + 1 then
        opn := false
      lastPos := pd[i]!
      if BS.has ex i then opn := false
      else if BS.has inS i then
        if !opn then
          groups := groups + 1
          opn := true
  return groups

/-- lower bound on the size of any infinitesimally rigid allowed set extending `inS` and avoiding
`ex`: the three independent bounds are the Steiner/connectivity bound from the chosen set, the
window-wide Steiner floor, and the run bound. -/
def lowerBound (R : Region) (inS ex : BS) (sz : Nat) : Nat :=
  match reachDists R inS ex with
  | none => R.pts.size + 1
  | some d =>
    let g := runBound R inS ex
    max (max (sz + steinerPairBound R d) R.floor) (if g > 3 then g - 3 else 0)

/-- contacts inside `S`. -/
def edgeCount (R : Region) (S : BS) : Nat := Id.run do
  let n := R.pts.size
  let mut c := 0
  for i in [0:n] do
    if BS.has S i then c := c + BS.card (R.adj[i]! &&& S)
  return c / 2

partial def bb (R : Region) (nodeCap : Nat) (inS ex : BS) (sz : Nat) (st : BBState) : BBState :=
  if st.nodes ≥ nodeCap then { st with complete := false } else
  let st := { st with nodes := st.nodes + 1 }
  let n := R.pts.size
  if lowerBound R inS ex sz ≥ st.best then st else
  let st :=
    if sz ≥ 3 && R.terms.all (BS.has inS) && sz < st.best && infRigid (subPts R inS) then
      { st with best := sz, bestSet := inS } else st
  if sz + 1 ≥ st.best then st else
  -- a chosen site must be able to reach degree 2, else the framework cannot be rigid
  if (List.range n).any (fun i => BS.has inS i && BS.card (R.adj[i]! &&& (~~~ex)) < 2) then st else
  -- the final set, of some size `M ≤ st.best - 1`, needs `2M − 3` contacts; `t = M − sz` more
  -- sites can bring at most the `t` largest degrees in the window
  let m := st.best - 1
  if edgeCount R inS + R.degPrefix[m - sz]! + 3 < 2 * m then st else
  Id.run do
    let mut front : BS := 0
    for i in [0:n] do
      if BS.has inS i then front := front ||| R.adj[i]!
    let cand := front &&& (~~~inS) &&& (~~~ex)
    let mut v := n
    for i in [0:n] do
      if v == n && BS.has cand i then v := i
    if v == n then return st
    let st := bb R nodeCap (inS ||| bit v) ex (sz + 1) st
    return bb R nodeCap inS (ex ||| bit v) sz st

/-- exact minimum infinitesimally rigid allowed set containing `R.terms`, searched up to size
`cap`; grown from `terms[0]`, which is harmless because such a set is connected. -/
def minRigid (R : Region) (cap : Nat) (nodeCap : Nat := 20000000) : BBState :=
  bb R nodeCap (bit R.terms[0]!) 0 1 ⟨cap + 1, 0, 0, true⟩

/-- the same search started from a known solution (from `greedyRigid`), so that it either proves
that solution optimal (`complete = true`) or improves it. -/
def minRigidFrom (R : Region) (initBest : Nat) (initSet : BS) (nodeCap : Nat) : BBState :=
  bb R nodeCap (bit R.terms[0]!) 0 1 ⟨initBest, initSet, 0, true⟩

/-! ## Cells: the polyiamond view

Rigidity forces the body to be *essentially triangulated*: with `V` sites, `e` contacts and `f`
bounded faces of the (plane) contact graph, Euler gives `e = V + f − 1`, so `e ≥ 2V − 3` needs
`f ≥ V − 2`, which for a lattice set means almost every face is a single cell.  So the cheapest
bodies are edge-connected polyiamonds, and the minimum number of *sites* is close to the minimum
number of *cells* plus two (a cell glued to a strip along an edge brings one new corner).

`cellSteiner` therefore computes the exact minimum number of allowed cells in an edge-connected
family whose corner set contains all four anchors (Dreyfus–Wagner over the cell-adjacency graph,
terminals = "some chosen cell has this anchor as a corner") and returns the cell set, whose
corner set is a rigid body. -/

structure Cells where
  tri : Array (Nat × Nat × Nat)       -- cells as triples of site indices
  nb : Array (Array Nat)              -- edge-adjacency of cells
  deriving Inhabited

def mkCells (R : Region) : Cells := Id.run do
  let n := R.pts.size
  let mut tri : Array (Nat × Nat × Nat) := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      if BS.has R.adj[i]! j then
        for k in [j+1:n] do
          if BS.has R.adj[i]! k && BS.has R.adj[j]! k then tri := tri.push (i, j, k)
  let m := tri.size
  let corners (c : Nat × Nat × Nat) : BS := bit c.1 ||| bit c.2.1 ||| bit c.2.2
  let mut nb : Array (Array Nat) := Array.replicate m #[]
  for a in [0:m] do
    for b in [0:m] do
      if a != b && BS.card (corners tri[a]! &&& corners tri[b]!) == 2 then
        nb := nb.set! a (nb[a]!.push b)
  return ⟨tri, nb⟩

def cellCorners (C : Cells) (c : Nat) : BS :=
  bit C.tri[c]!.1 ||| bit C.tri[c]!.2.1 ||| bit C.tri[c]!.2.2

/-- a small edge-connected cell family whose corners cover every anchor, by Dreyfus–Wagner over
the cell graph.  Because the objective is the cardinality of a *union* of witness families, the
value is a valid upper bound on the minimum, not a certified optimum; it is used only to build
candidate bodies, and the lower bounds come from `steiner` and `bb`. -/
def cellSteiner (R : Region) (C : Cells) : Nat × BS := Id.run do
  let m := C.tri.size
  let k := R.terms.size
  if m == 0 || k == 0 then return (0, 0)
  let inf := m + 1
  let full := (1 <<< k) - 1
  -- dp value and a witness cell family, indexed mask * m + cell
  let mut dp : Array Nat := Array.replicate ((full + 1) * m) inf
  let mut wit : Array BS := Array.replicate ((full + 1) * m) 0
  for c in [0:m] do
    let cs := cellCorners C c
    let mut tm := 0
    for i in [0:k] do
      if BS.has cs R.terms[i]! then tm := tm ||| (1 <<< i)
    for sub in [1:full+1] do
      if sub &&& tm == sub && dp[sub * m + c]! > 1 then
        dp := dp.set! (sub * m + c) 1
        wit := wit.set! (sub * m + c) (bit c)
  for mask in [1:full+1] do
    let mut sub := (mask - 1) &&& mask
    while sub > 0 do
      let other := mask ^^^ sub
      if sub < other then
        for c in [0:m] do
          let a := dp[sub * m + c]!
          let b := dp[other * m + c]!
          if a < inf && b < inf then
            let u := wit[sub * m + c]! ||| wit[other * m + c]!
            let cu := BS.card u
            if cu < dp[mask * m + c]! then
              dp := dp.set! (mask * m + c) cu; wit := wit.set! (mask * m + c) u
      sub := (sub - 1) &&& mask
    for _ in [0:m] do
      let mut changed := false
      for c in [0:m] do
        let dc := dp[mask * m + c]!
        if dc < inf then
          for d in C.nb[c]! do
            let u := wit[mask * m + c]! ||| bit d
            let cu := BS.card u
            if cu < dp[mask * m + d]! then
              dp := dp.set! (mask * m + d) cu; wit := wit.set! (mask * m + d) u
              changed := true
      if !changed then break
  let mut best := inf
  let mut bw : BS := 0
  for c in [0:m] do
    if dp[full * m + c]! < best then best := dp[full * m + c]!; bw := wit[full * m + c]!
  return (best, bw)

/-- the corner set of a cell family. -/
def cellsToSites (C : Cells) (T : BS) (m : Nat) : BS :=
  (BS.toList T m).foldl (fun acc c => acc ||| cellCorners C c) 0

/-! ## Constructive upper bound: randomised greedy growth, then greedy shrinking -/

@[inline] def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- remove non-anchor sites while infinitesimal rigidity survives. -/
def shrink (R : Region) (S0 : BS) : BS := Id.run do
  let n := R.pts.size
  let mut S := S0
  let mut again := true
  while again do
    again := false
    for i in BS.toList S n do
      if !R.terms.contains i then
        let T := S &&& (~~~bit i)
        if infRigid (subPts R T) then S := T; again := true
  return S

def components (R : Region) (S : BS) : Array BS := Id.run do
  let n := R.pts.size
  let mut rem := S
  let mut out : Array BS := #[]
  while rem != 0 do
    let v := (BS.toList rem n).headD 0
    let mut seen := bit v
    let mut fr := seen
    while fr != 0 do
      let mut nxt : BS := 0
      for i in BS.toList fr n do nxt := nxt ||| R.adj[i]!
      nxt := nxt &&& S &&& (~~~seen)
      seen := seen ||| nxt
      fr := nxt
    out := out.push seen
    rem := rem &&& (~~~seen)
  return out

/-- join the components of `S` by shortest allowed paths (random tie-breaking). -/
def connectSet (R : Region) (S0 : BS) (rng0 : UInt64) : BS × UInt64 := Id.run do
  let n := R.pts.size
  let mut S := S0
  let mut rng := rng0
  let mut guard := 0
  while (components R S).size > 1 && guard < n do
    guard := guard + 1
    let c0 := (components R S)[0]!
    let d := dists R c0 0
    let mut bestT := n
    let mut bestD := n + 1
    for i in BS.toList (S &&& (~~~c0)) n do
      if d[i]! < bestD then bestD := d[i]!; bestT := i
    if bestT == n then return (S, rng)
    let mut cur := bestT
    while d[cur]! > 0 do
      S := S ||| bit cur
      let mut nxt := cur
      let mut bestR : UInt64 := 0
      for j in BS.toList R.adj[cur]! n do
        if d[j]! + 1 == d[cur]! then
          rng := lcg rng
          let r := rng >>> 40
          if r ≥ bestR then bestR := r; nxt := j
      if nxt == cur then return (S, rng)
      cur := nxt
  return (S, rng)

/-- add allowed sites, preferring ones that close a triangle, until infinitesimally rigid. -/
def rigidify (R : Region) (S0 : BS) (cap : Nat) (rng0 : UInt64) : BS × UInt64 := Id.run do
  let n := R.pts.size
  let mut S := S0
  let mut rng := rng0
  while BS.card S ≤ cap && !infRigid (subPts R S) do
    let mut bestV := n
    let mut bestSc : Nat := 0
    let mut bestR : UInt64 := 0
    for v in [0:n] do
      if !BS.has S v then
        let nb := R.adj[v]! &&& S
        let k := BS.card nb
        let mut tri := false
        for i in BS.toList nb n do
          if R.adj[i]! &&& nb != 0 then tri := true
        let sc := (if tri then 100 else 0) + 10 * k
        if sc > 0 then
          rng := lcg rng
          let r := rng >>> 40
          if sc > bestSc || (sc == bestSc && r > bestR) then bestSc := sc; bestV := v; bestR := r
    if bestV == n then return (S, rng)
    S := S ||| bit bestV
  return (S, rng)

/-- randomised construction: anchors → connect → rigidify → shrink, best of `tries`. -/
def greedyRigid (R : Region) (cap : Nat) (tries : Nat) (seed : UInt64 := 12345) : Option BS :=
  Id.run do
    let mut rng := seed
    let mut best : Option BS := none
    let mut bestSz := cap + 1
    for _ in [0:tries] do
      let mut S : BS := 0
      for t in R.terms do S := S ||| bit t
      let (S1, r1) := connectSet R S rng
      let (S2, r2) := rigidify R S1 cap r1
      rng := r2
      if BS.card S2 ≤ cap && infRigid (subPts R S2) then
        let T := shrink R S2
        let tz := BS.card T
        if tz < bestSz then bestSz := tz; best := some T
    return best

end CaseB
