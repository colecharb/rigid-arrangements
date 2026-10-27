namespace CaseB

/-! # Drivers.  `caseb <mode> [args]` -/

def pow10 : Nat → Float
  | 0 => 1.0
  | n + 1 => 10.0 * pow10 n

/-- fixed-point rendering with `d` digits after the point. -/
partial def fmt (x : Float) (d : Nat := 15) : String :=
  if x.isNaN then "nan" else
  if x < 0.0 then "-" ++ fmt (-x) d else
  let ip := x.floor
  let fr := (x - ip) * pow10 d
  let frn := fr.round.toUInt64.toNat
  let ipn := ip.toUInt64.toNat
  let (ipn, frn) := if frn ≥ (10 : Nat) ^ d then (ipn + 1, 0) else (ipn, frn)
  let s := toString frn
  toString ipn ++ "." ++ (String.ofList (List.replicate (d - s.length) '0')) ++ s

def showP (p : P2) (d : Nat := 15) : String := s!"({fmt p.x d}, {fmt p.y d})"

/-! ## Windows and allowed sites around a ring -/

/-- lattice sites whose centre is within `rad` of `c`. -/
def windowSites (c : P2) (rad : Float) : Array Site := Id.run do
  let k : Int := (rad.toUInt64.toNat : Int) + 2
  let mut out := #[]
  for a in [0:(2 * k + 1).toNat] do
    for b in [0:(2 * k + 1).toNat] do
      let p : Site := ((a : Int) - k, (b : Int) - k)
      if P2.d2 (siteF p) c ≤ rad * rad then out := out.push p
  return out

/-- a site is allowed if every free circle is at distance `≥ 2` from it, with equality only for
its own designated anchor (an extra ring/body contact would put that free circle on the lattice,
by Lemma 4). -/
def allowedSite (xs : Array Site) (ws : Array P2) (p : Site) (tol : Float := 1e-7) : Bool :=
  Id.run do
    let q := siteF p
    for i in [0:4] do
      let d := P2.d2 q ws[i]! - 4.0
      if d < tol then
        if !(xs[i]! == p && d.abs < tol) then return false
    return true

/-- window centred on the ring, pierced by the four free circles; terminals = the four anchors
(anchors are deduplicated, since opposite anchors may coincide). -/
def candRegion (xs : Array Site) (ws : Array P2) (rad : Float) : Region :=
  let c : P2 := ⟨(ws[0]!.x + ws[1]!.x + ws[2]!.x + ws[3]!.x) / 4.0,
                 (ws[0]!.y + ws[1]!.y + ws[2]!.y + ws[3]!.y) / 4.0⟩
  let pts := (windowSites c rad).filter (allowedSite xs ws)
  let terms := Id.run do
    let mut ts : Array Nat := #[]
    for x in xs do
      match pts.findIdx? (· == x) with
      | some i => if !ts.contains i then ts := ts.push i
      | none => pure ()
    return ts
  mkRegion pts terms

/-- `(lower bound, best size, best body, search complete, nodes)` for one ring. -/
def bodySearch (xs : Array Site) (ws : Array P2) (rad : Float) (cap tries nodeCap : Nat) :
    Option (Nat × Nat × Array Site × Bool × Nat) :=
  let R := candRegion xs ws rad
  if R.terms.size != (xs.toList.eraseDups).length then none else
  let lb := steiner R
  let (ub, us) := match greedyRigid R cap tries with
    | some S => (BS.card S, S)
    | none => (cap + 1, 0)
  let st := minRigidFrom R ub us nodeCap
  some (lb, st.best, subPts R st.bestSet, st.complete, st.nodes)

def candReport (xs : Array Site) (ws : Array P2) (rad : Float) (cap : Nat)
    (nodeCap : Nat) : String :=
  match bodySearch xs ws rad cap 200 nodeCap with
  | none => s!"  !! an anchor is not an allowed site (window radius {rad}?)"
  | some (lb, best, body, complete, nodes) =>
    let R := candRegion xs ws rad
    let head := s!"  window {R.pts.size} allowed sites, {R.terms.size} terminals, \
      steiner lb {lb}, nodes {nodes}, complete {complete}"
    if best > cap then head ++ s!"; no infinitesimally rigid body of ≤ {cap} sites"
    else head ++ s!"; min body {best} sites → n = {best + 4}\n  body = {showSites body} \
      rank {rigRank body}/{2 * best - 3} contacts {(contacts body).size}"

/-! ## Modes -/

/-- the H30 body in the convention of `docs/offlattice.md` §8 (site `(a,b) ↦ (2a+b, √3 b)`). -/
def h30Body : Array Site :=
  #[(-2,1), (-2,2), (-2,3), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3), (0,-2), (0,-1), (0,0),
    (0,2), (0,3), (1,-3), (1,-2), (1,2), (1,3), (2,-3), (2,-2), (2,2), (2,3), (3,0), (3,1),
    (3,2), (4,0), (4,1)]

/-- H30's anchors, doc convention: x₁ = (0,0), x₂ = (4,2√3), x₃ = (6,0), x₄ = (2,−2√3). -/
def h30Anchors : Array Site := #[(0,0), (1,2), (3,0), (2,-2)]

def modeH30 (steps : Nat) : IO Unit := do
  IO.println s!"H30 body: {h30Body.size} sites, contacts {(contacts h30Body).size}, \
    exact rank {rigRank h30Body} (2m-3 = {2 * h30Body.size - 3})"
  IO.println s!"anchors (doc convention) {showSites h30Anchors}, all in body: \
    {h30Anchors.all (h30Body.contains ·)}"
  let cands := scanTuple h30Anchors steps
  IO.println s!"closures found on the 8 branches: {cands.size}"
  for C in cands do
    IO.println s!"  θ={fmt C.θ 12} σ=({C.sg2},{C.sg4},{C.sg3}) d13²={fmt C.d13 12} \
      d24²={fmt C.d24 12} sep={fmt C.sep 9} off={fmt C.offMax 6} det8={fmt C.det8 6} \
      ok={C.ok}"
    if C.ok then
      for i in [0:4] do IO.println s!"      w{i+1} = {showP C.ws[i]!}"
      -- body must be contained in the allowed region and no ring/body overlap
      let bad := h30Body.filter (fun p => !allowedSite h30Anchors C.ws p)
      IO.println s!"      body sites violating the ring clearance: {showSites bad}"

/-- local search: drop `j` non-anchor sites and add `j-1` allowed ones, for j = 2, 3. -/
def swapDown (R : Region) (S : BS) : Option BS := Id.run do
  let n := R.pts.size
  let drop := (BS.toList S n).filter (fun i => !R.terms.contains i)
  let outside := (List.range n).filter (fun i => !BS.has S i)
  -- j = 2: remove two, add one
  for a in drop do
    for b in drop do
      if a < b then
        let base := S &&& (~~~bit a) &&& (~~~bit b)
        if infRigid (subPts R base) then return some base
        for c in outside do
          let T := base ||| bit c
          if infRigid (subPts R T) then return some T
  -- j = 3: remove three, add two
  for a in drop do
    for b in drop do
      for c in drop do
        if a < b && b < c then
          let base := S &&& (~~~bit a) &&& (~~~bit b) &&& (~~~bit c)
          for d in outside do
            for e in outside do
              if d < e then
                let T := base ||| bit d ||| bit e
                if (contacts (subPts R T)).size ≥ 2 * BS.card T - 3 && infRigid (subPts R T) then
                  return some T
  return none

/-- everything that can be said about the body for one ring: the window, the rigorous Steiner
lower bound, the exhaustive branch and bound by iterative deepening, the polyiamond construction,
the randomised greedy and a 2- and 3-swap local search. -/
def modeRing (xs : Array Site) (steps : Nat) (rad : Float) (idCap tries nodeCap : Nat) :
    IO Unit := do
  let cands := (scanTuple xs steps).filter (·.ok)
  IO.println s!"anchors {showSites xs}: {cands.size} legal closure(s)"
  for C in cands do
    let R := candRegion xs C.ws rad
    if R.pts.size > 64 then
      IO.println s!"!! window radius {rad} holds {R.pts.size} allowed sites, more than the 64 \
        that fit a UInt64 mask; every set-based answer below would be meaningless.  Narrow it."
    else
      let hole := (windowSites ⟨(C.ws[0]!.x + C.ws[2]!.x) / 2.0, (C.ws[0]!.y + C.ws[2]!.y) / 2.0⟩
        rad).filter (fun p => !allowedSite xs C.ws p)
      IO.println s!"window radius {rad}: {R.pts.size} allowed sites, {hole.size} forbidden"
      IO.println s!"  forbidden (the hole) = {showSites hole}"
      IO.println s!"  allowed = {showSites R.pts}"
      IO.println s!"  steiner lower bound (min connected allowed set with the 4 anchors) = \
        {steiner R}; root branch-and-bound lower bound = {lowerBound R (bit R.terms[0]!) 0 1}"
      -- polyiamond construction
      let C2 := mkCells R
      let (nc, T) := cellSteiner R C2
      let S0 := cellsToSites C2 T R.pts.size
      IO.println s!"  cells in the window {C2.tri.size}; small covering cell family {nc} cells, \
        {BS.card S0} corners, infinitesimally rigid {infRigid (subPts R S0)}"
      let mut bestS := S0
      -- `goodBody`, not `infRigid`: the empty set and single sites pass `infRigid` vacuously,
      -- so an empty cell family would otherwise be reported as a body of 0 sites
      let mut bestSz := if goodBody R S0 then BS.card S0 else 1000
      if bestSz < 1000 then
        let Sh := shrink R S0
        if BS.card Sh < bestSz then bestSz := BS.card Sh; bestS := Sh
        IO.println s!"  shrunk to {BS.card Sh} sites: {showSites (subPts R Sh)}"
      match greedyRigid R idCap tries with
      | none => IO.println s!"  greedy found no body of ≤ {idCap} sites"
      | some S =>
        IO.println s!"  randomised greedy ({tries} restarts): {BS.card S} sites: \
          {showSites (subPts R S)}"
        if goodBody R S && BS.card S < bestSz then bestSz := BS.card S; bestS := S
      -- local search
      let mut again := true
      while again do
        again := false
        match swapDown R bestS with
        | some T => if BS.card T < bestSz then
                      bestSz := BS.card T; bestS := T; again := true
                      IO.println s!"  swap improved to {BS.card T} sites"
        | none => pure ()
      if bestSz > idCap then
        IO.println s!"  NO body of ≤ {idCap} sites was constructed in this window, so there is \
          nothing to deepen against; widen the window or raise the cap"
        return
      IO.println s!"  best body: {bestSz} sites → n = {bestSz + 4}"
      IO.println s!"  {showSites (subPts R bestS)}"
      -- iterative deepening: prove there is no smaller body
      let mut proved := 0
      for m in [(steiner R):(bestSz)] do
        let st := bb R nodeCap (bit R.terms[0]!) 0 1 ⟨m + 1, 0, 0, true⟩
        if st.best ≤ m then
          IO.println s!"  !! found a body of {st.best} sites at depth {m}"
          break
        if st.complete then proved := m
        else
          IO.println s!"  exhaustive search incomplete at size {m} ({st.nodes} nodes)"
          break
      IO.println s!"  exhaustively excluded: no infinitesimally rigid body of ≤ {proved} sites \
        inside this window"
      IO.println (certify xs (subPts R bestS) C 30)

/-- the same window, but with only the anchors selected by `mask` as terminals. -/
def subRegion (xs : Array Site) (ws : Array P2) (rad : Float) (mask : Nat) : Region :=
  let R := candRegion xs ws rad
  let pts := R.pts
  let terms := Id.run do
    let mut ts : Array Nat := #[]
    for i in [0:4] do
      if (mask >>> i) &&& 1 == 1 then
        match pts.findIdx? (· == xs[i]!) with
        | some j => if !ts.contains j then ts := ts.push j
        | none => pure ()
    return ts
  mkRegion pts terms

/-- exhaustive minimum-corner search over edge-connected cell families in the window.

With `mask = 15` (all four anchors) this is the minimum **single-polyiamond body**.  The smaller
masks matter because an infinitesimally rigid lattice part need not be one polyiamond:

* an anchor can hang off the structure as a lattice circle in no triangle (a Henneberg-1 site:
  two non-antipodal neighbours already present), so the cell family need only cover the *other*
  anchors;
* the lattice part can be two bodies joined by three bars (`docs/offlattice.md` §3, Translation
  Lemma: in one frame, bars with at least two different vectors join them rigidly), and then the
  two cell families cover a partition of the anchors.

So the table of minima over all 15 masks bounds those structures from below: a two-body lattice
part realising the split `A ⊎ B` has at least `minCorner A + minCorner B` sites. -/
def modeCorner (xs : Array Site) (steps : Nat) (rad : Float) (cap nodeCap mask : Nat) :
    IO Unit := do
  let cands := (scanTuple xs steps).filter (·.ok)
  IO.println s!"anchors {showSites xs}: {cands.size} legal closure(s)"
  for C in cands do
    let R0 := candRegion xs C.ws rad
    IO.println s!"window radius {rad}: {R0.pts.size} allowed sites, {R0.terms.size} anchors; \
      exact Steiner over all four = {steiner R0}"
    for mk in (if mask == 0 then (List.range 15).map (· + 1) else [mask]) do
      let R := subRegion xs C.ws rad mk
      let which := String.intercalate "," ((List.range 4).filterMap fun i =>
        if (mk >>> i) &&& 1 == 1 then some s!"x{i+1}" else none)
      let P := mkCP R
      if R.pts.size > 64 || P.cells.size > 64 then
        IO.println s!"  mask {mk} ({which}): {R.pts.size} allowed sites / {P.cells.size} cells, \
          more than the 64 that fit a UInt64 mask; narrow the window"
      else
        let st := minCorner P cap nodeCap
        let head := s!"  mask {mk} ({which}): steiner {steiner R}, nodes {st.nodes}, \
          complete {st.complete}"
        if st.best > cap then
          IO.println s!"{head}, NO polyiamond with ≤ {cap} corners"
        else
          let body := subPts R st.bestSites
          IO.println s!"{head}, min {st.best} corners ({BS.card st.bestCells} cells), \
            rank {rigRank body}/{2 * st.best - 3}"
          if mk == 15 then
            IO.println s!"    {showSites body}"

/-- Soundness check of the bounds that the body search prunes on.  An *over*-counting `runBound`
would silently prune the true answer, and nothing else in the pipeline would notice, so this is
checked against H30's own body, where the run identity is tight.

1. `e(S) = 3|S| − ΣR(S)` on H30's body, with `ΣR` read off `runBound S (complement S)` — the run
   count of a *finished* set, every non-member being excluded.
2. `lowerBound ≤ 26` at H30's body: a bound that exceeded the true size would prune it.
3. the branch and bound, given an initial upper bound of 27, must *find* a 26-site body. This is
   the real test: it exercises every prune on the path to the answer. -/
def modeVerify (xs : Array Site) (steps : Nat) (rad : Float) (nodeCap : Nat) : IO Unit := do
  let cands := (scanTuple xs steps).filter (·.ok)
  for C in cands do
    let R := candRegion xs C.ws rad
    if R.pts.size > 64 then
      IO.println s!"!! {R.pts.size} allowed sites, more than 64"
    else
      -- H30's body as a mask of this window
      let mut S : BS := 0
      let mut missing : Array Site := #[]
      for p in h30Body do
        match R.pts.findIdx? (· == p) with
        | some i => S := S ||| bit i
        | none => missing := missing.push p
      IO.println s!"H30 body inside the window: {BS.card S}/26 sites, missing \
        {showSites missing}"
      let mut full : BS := 0
      for i in [0:R.pts.size] do full := full ||| bit i
      let m := BS.card S
      let e := (contacts (subPts R S)).size
      let sr := runBound R S (full &&& (~~~S))
      IO.println s!"(1) run identity: m = {m}, e = {e}, ΣR from runBound = {sr}, 3m − ΣR = \
        {3 * m - sr} — identity holds: {3 * m - sr == e}; tight (ΣR = m + 3): {sr == m + 3}"
      let lb := lowerBound R S (full &&& (~~~S)) m
      IO.println s!"(2) lowerBound at H30's body = {lb}, must be ≤ {m}: {decide (lb ≤ m)}"
      let st := bb R nodeCap (bit R.terms[0]!) 0 1 ⟨m + 1, 0, 0, true⟩
      IO.println s!"(3) branch and bound with initial best {m + 1}: found {st.best} sites, \
        complete {st.complete}, nodes {st.nodes} — recovers a {m}-site body: {st.best == m}"
      IO.println s!"    {showSites (subPts R st.bestSet)}"

def modeTuple (xs : Array Site) (steps : Nat) (rad : Float) (cap nodeCap : Nat) : IO Unit := do
  IO.println s!"anchors {showSites xs}"
  for C in scanTuple xs steps do
    IO.println s!"  θ={fmt C.θ 12} σ=({C.sg2},{C.sg4},{C.sg3}) d13²={fmt C.d13 12} \
      d24²={fmt C.d24 12} sep={fmt C.sep 9} off={fmt C.offMax 6} det8={fmt C.det8 6} ok={C.ok}"
    if C.ok then
      for i in [0:4] do IO.println s!"      w{i+1} = {showP C.ws[i]!}"
      IO.println (candReport xs C.ws rad cap nodeCap)

/-- all anchor 4-cycles up to translation, the 12 lattice symmetries and D₄. -/
def anchorTuples : Array (Array Site) := Id.run do
  let p9 := pool 1 9
  let p13 := pool 0 13
  let mut seen : Std.HashSet Nat := Std.HashSet.emptyWithCapacity 1024
  let mut out : Array (Array Site) := #[]
  let x1 : Site := (0, 0)
  for x2 in p9 do
    for x3 in p13 do
      if x3 != x2 && eN (sub x3 x2) ≤ 9 then
        for x4 in p9 do
          if x4 != x3 && eN (sub x4 x3) ≤ 9 && eN (sub x4 x2) ≤ 13 then
            let xs := #[x1, x2, x3, x4]
            let k := canonTup xs
            if !seen.contains k then
              seen := seen.insert k
              out := out.push xs
  return out

def modeCount : IO Unit := do
  IO.println s!"sites with 1 ≤ eN ≤ 9: {(pool 1 9).size}; with eN ≤ 13: {(pool 0 13).size}"
  let ts := anchorTuples
  IO.println s!"anchor 4-cycles up to symmetry: {ts.size}"

/-- the whole `|C| = 4` search: every anchor class, every branch, every transversal closure. -/
def modeScan (steps : Nat) (rad : Float) (cap tries nodeCap : Nat) : IO Unit := do
  let ts := anchorTuples
  IO.println s!"scanning {ts.size} anchor classes × 8 branches, {steps} θ-steps, \
    window radius {rad}, body cap {cap}, greedy tries {tries}"
  let mut nClos := 0        -- transversal closures
  let mut nFlat := 0        -- flat sign changes (flexing rhombus: singular, discarded)
  let mut nLat := 0         -- exact lattice closures (not case (b))
  let mut nLegal := 0       -- closures that are legal arrangements (no overlap, no triangle)
  let mut nTriFree := 0
  let mut nOk := 0
  let mut best : Nat := 1000
  let mut bestLB : Nat := 1000
  let mut margin : Float := 1.0e9        -- smallest failure margin among rejected closures
  let mut flatTuples : Array (Array Site) := #[]
  let mut bdry : Array String := #[]
  let mut rows : Array String := #[]
  let mut flatOk := 0
  let mut flatMaxDet : Float := 0.0
  let mut flatWorst : Float := 1.0e9
  let mut flatMaxSlope : Float := 0.0
  let mut transMinSlope : Float := 1.0e9
  for xs in ts do
    let so := scanTupleF xs steps
    let cs := so.cands
    let nf := so.nFlat
    flatOk := flatOk + so.flatOk
    if so.flatMaxDet > flatMaxDet then flatMaxDet := so.flatMaxDet
    if so.flatWorst < flatWorst then flatWorst := so.flatWorst
    if so.flatMaxSlope > flatMaxSlope then flatMaxSlope := so.flatMaxSlope
    if so.transMinSlope < transMinSlope then transMinSlope := so.transMinSlope
    if nf > 0 then
      nFlat := nFlat + nf
      flatTuples := flatTuples.push xs
    for C in cs do
      nClos := nClos + 1
      if C.d13 > 4.0 && C.d24 > 4.0 then nTriFree := nTriFree + 1
      match latticeClosure xs C.ws with
      | some _ => nLat := nLat + 1       -- exact lattice rhombus, rejected exactly
      | none =>
        if C.worstFail > 0.0 then margin := min margin C.worstFail
        -- EVERY geometrically legal non-lattice closure is listed and certified: these are the
        -- only ones where the det8 and z⁶ thresholds could matter at all
        if C.worstFail < 0.0 then
          nLegal := nLegal + 1
          bdry := bdry.push s!"LEGAL {showSites xs} th={fmt C.θ 12} \
            d13={fmt C.d13 12} d24={fmt C.d24 12} sep={fmt C.sep 12} off={fmt C.offMax 9} \
            det8={fmt C.det8 9} ok={C.ok}\n{certify xs #[] C 24}"
        if C.ok then
          nOk := nOk + 1
          if tries == 0 then
            let R := candRegion xs C.ws rad
            let lb := if R.terms.size == (xs.toList.eraseDups).length then steiner R else 0
            if lb < bestLB then bestLB := lb
            rows := rows.push s!"OK {showSites xs} th={fmt C.θ 12} d13={fmt C.d13 12} \
              d24={fmt C.d24 12} sep={fmt C.sep 9} det8={fmt C.det8 6} allowed={R.pts.size} \
              lb={lb}"
          else
            match bodySearch xs C.ws rad cap tries nodeCap with
            | none => rows := rows.push s!"OK {showSites xs} ANCHOR OUTSIDE WINDOW"
            | some (lb, bst, body, complete, nodes) =>
              if lb < bestLB then bestLB := lb
              if bst ≤ cap && bst < best then best := bst
              let mstr := if bst ≤ cap then toString bst else "none"
              let nstr := if bst ≤ cap then toString (bst + 4) else "-"
              rows := rows.push s!"OK {showSites xs} th={fmt C.θ 12} d13={fmt C.d13 12} \
                lb={lb} body={mstr} n={nstr} complete={complete} nodes={nodes}\n   \
                {showSites body}"
  IO.println s!"transversal closures {nClos}; of them triangle-free {nTriFree}, \
    exact lattice rhombi {nLat}, legal arrangements {nLegal}, passing every test {nOk}"
  IO.println s!"flat (flexing) sign changes discarded: {nFlat}, on {flatTuples.size} anchor \
    classes"
  IO.println s!"FLAT AUDIT: of the {nFlat} discarded flat sign changes, {flatOk} pass every \
    test (must be 0); the largest |det8| among the geometrically legal ones is \
    {fmt flatMaxDet 12}; the closest any of them comes to being legal is worstFail = \
    {fmt flatWorst 12} (< 0 would be legal)"
  IO.println s!"SLOPE SEPARATION: flat sign changes have |ΔF|·steps ≤ {fmt flatMaxSlope 12}, \
    transversal ones ≥ {fmt transMinSlope 12}; the cut is at 0.001"
  for xs in flatTuples do
    let lr := (List.range 4).all fun i => eN (sub xs[(i+1) % 4]! xs[i]!) == 1
    IO.println s!"  FLAT {showSites xs}  anchors form a side-2 lattice rhombus: {lr}"
  IO.println s!"smallest failure margin among rejected non-lattice closures: {fmt margin 12}"
  IO.println s!"geometrically legal non-lattice closures (all listed, all certified): \
    {bdry.size}"
  for r in bdry do IO.println r
  IO.println s!"smallest steiner lower bound over survivors: {bestLB} (so n ≥ {bestLB + 4})"
  let bstr := if best ≤ cap then toString best else "none"
  IO.println s!"smallest body constructed: {bstr}"
  for r in rows do IO.println r

def main (args : List String) : IO Unit := do
  let nat (i : Nat) (d : Nat) : Nat := (args[i]?.bind (·.toNat?)).getD d
  match args.head? with
  | some "h30" => modeH30 (nat 1 20000)
  | some "count" => modeCount
  | some "tuple" =>
      let g (i : Nat) : Int := ((args[i]?.bind (·.toInt?)).getD 0)
      modeTuple #[(0,0), (g 1, g 2), (g 3, g 4), (g 5, g 6)] (nat 7 20000)
        ((nat 8 8).toFloat) (nat 9 30) (nat 10 2000000)
  | some "ring" =>
      let g (i : Nat) : Int := ((args[i]?.bind (·.toInt?)).getD 0)
      modeRing #[(0,0), (g 1, g 2), (g 3, g 4), (g 5, g 6)] (nat 7 20000) ((nat 8 8).toFloat)
        (nat 9 30) (nat 10 300) (nat 11 3000000)
  | some "chain" =>
      let g (i : Nat) (d : Int) : Int := ((args[i]?.bind (·.toInt?)).getD d)
      modeChain (g 1 882) (g 2 28) (nat 3 30) (nat 4 300) (nat 5 3000000)
  | some "corner" =>
      let g (i : Nat) : Int := ((args[i]?.bind (·.toInt?)).getD 0)
      modeCorner #[(0,0), (g 1, g 2), (g 3, g 4), (g 5, g 6)] (nat 7 20000) ((nat 8 8).toFloat)
        (nat 9 30) (nat 10 100000000) (nat 11 15)
  | some "verify" =>
      modeVerify #[(0,0), (1,2), (3,0), (2,-2)] (nat 1 40000) ((nat 2 8).toFloat)
        (nat 3 2000000000)
  | some "scan" => modeScan (nat 1 4000) ((nat 2 8).toFloat) (nat 3 30) (nat 4 0) (nat 5 0)
  | _ => IO.println "modes: count | h30 [steps] | tuple a2 b2 a3 b3 a4 b4 [steps rad cap nodes] \
      | scan [steps rad cap tries nodes] | ring a2 b2 a3 b3 a4 b4 [steps rad cap tries nodes] | chain [w49 ext cap tries nodes] | corner a2 b2 a3 b3 a4 b4 [steps rad cap nodes mask] | verify [steps rad nodes]"

end CaseB

def main (args : List String) : IO Unit := CaseB.main args
