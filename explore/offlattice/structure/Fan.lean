import Std.Data.HashMap
import Std.Data.HashSet
open Std

/-! Exploratory, exact: two lattice bodies + one hinge + one bar.
Eisenstein integers `a + b ω` (ω = e^{iπ/3}) as `Int × Int`; lattice spacing 1 here
(the repo's spacing-2 picture is this one scaled by 2).
Positions of the second body lie in `(Z[ω] + Z[ω]·ι)/(2pq)` with `ι = i√Δ`,
`Δ = 4pq - (p+q-1)²`. All squared distances lie in `Q(√(3Δ))`; every comparison
below is an exact integer sign test. -/

abbrev E := Int × Int

namespace E
@[inline] def add (x y : E) : E := (x.1+y.1, x.2+y.2)
@[inline] def sub (x y : E) : E := (x.1-y.1, x.2-y.2)
@[inline] def neg (x : E) : E := (-x.1, -x.2)
@[inline] def smul (k : Int) (x : E) : E := (k*x.1, k*x.2)
@[inline] def mul (x y : E) : E := (x.1*y.1 - x.2*y.2, x.1*y.2 + x.2*y.1 + x.2*y.2)
@[inline] def conj (x : E) : E := (x.1 + x.2, -x.2)
@[inline] def nrm (x : E) : Int := x.1*x.1 + x.1*x.2 + x.2*x.2
def units : Array E := #[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
@[inline] def rot (x : E) : E := (-x.2, x.1 + x.2)   -- multiply by ω
end E

def isqrt (n : Nat) : Nat := Id.run do
  if n < 2 then return n
  let mut x := n
  let mut y := (x + 1) / 2
  while y < x do
    x := y
    y := (x + n / x) / 2
  return x

def isSquare (n : Int) : Bool := n ≥ 0 && (let r := isqrt n.toNat; r*r == n.toNat)

/-- sign of `e + f √d` (d ≥ 0). -/
def signSurd (e f d : Int) : Int :=
  if f == 0 || d == 0 then (if e > 0 then 1 else if e < 0 then -1 else 0)
  else if e ≥ 0 && f > 0 then 1
  else if e ≤ 0 && f < 0 then -1
  else
    let a := e*e
    let b := f*f*d
    if e > 0 then (if a > b then 1 else if a < b then -1 else 0)
    else (if b > a then 1 else if b < a then -1 else 0)

/-! ### Lattice bodies -/

def ltE (p q : E) : Bool := p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)
def sortE (s : Array E) : Array E := s.qsort ltE
def normT (s : Array E) : Array E :=
  let s := sortE s
  let o := s[0]!
  s.map (fun p => E.sub p o)
@[inline] def adj (p q : E) : Bool := E.nrm (E.sub p q) == 1
def deg (s : Array E) (p : E) : Nat := (s.filter (adj p)).size

/-- lattice triangles spanned by `s`: as triples of indices. -/
def spannedTriangles (s : Array E) : Array (Nat × Nat × Nat) := Id.run do
  let mut out := #[]
  for i in [0:s.size] do
    for j in [i+1:s.size] do
      if adj s[i]! s[j]! then
        for k in [j+1:s.size] do
          if adj s[i]! s[k]! && adj s[j]! s[k]! then out := out.push (i, j, k)
  return out

/-- spanned triangles edge-connected and covering every site. -/
def isSAT (s : Array E) : Bool := Id.run do
  let ts := spannedTriangles s
  if ts.size == 0 then return false
  let shareEdge := fun (a b : Nat × Nat × Nat) =>
    let la := #[a.1, a.2.1, a.2.2]
    let lb := #[b.1, b.2.1, b.2.2]
    (la.filter (fun v => lb.contains v)).size == 2
  let mut seen := Array.replicate ts.size false
  seen := seen.set! 0 true
  let mut stack := #[0]
  while stack.size > 0 do
    let t := stack.back!
    stack := stack.pop
    for u in [0:ts.size] do
      if !seen[u]! && shareEdge ts[t]! ts[u]! then
        seen := seen.set! u true
        stack := stack.push u
  if seen.any (· == false) then return false
  let mut cov := Array.replicate s.size false
  for (a, b, c) in ts do
    cov := ((cov.set! a true).set! b true).set! c true
  return cov.all id

/-- all fixed sets (up to translation) reachable from a triangle by adding a site adjacent to
two adjacent sites; sizes 3..M. -/
def reachable (M : Nat) : Array (Array (Array E)) := Id.run do
  let t1 := normT #[(0,0),(1,0),(0,1)]
  let t2 := normT #[(1,0),(0,1),(1,1)]
  let mut lv : Array (Array (Array E)) := #[#[], #[], #[], #[t1, t2]]
  for n in [4:M+1] do
    let mut seen : HashSet (Array E) := {}
    let mut out := #[]
    for S in lv[n-1]! do
      for p in S do
        for u in E.units do
          let x := E.add p u
          if !S.contains x then
            let nb := S.filter (adj x)
            let mut ok := false
            for i in [0:nb.size] do
              for j in [i+1:nb.size] do
                if adj nb[i]! nb[j]! then ok := true
            if ok then
              let T := normT (S.push x)
              if !seen.contains T then
                seen := seen.insert T
                out := out.push T
    lv := lv.push out
  return lv

/-! ### Port bodies: (S, h = 0, x), canonical under the 6 rotations about h. -/

structure Port where
  sites : Array E    -- relative to the hinge, sorted; contains (0,0)
  x : E              -- the bar end
  p : Int            -- N(x)
  key : Array Int
  deriving Inhabited

def keyOf (sites : Array E) (x : E) : Array Int :=
  let s := sortE sites
  #[x.1, x.2] ++ (s.foldl (fun acc q => acc.push q.1 |>.push q.2) #[])

def ltArr (a b : Array Int) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return a.size < b.size

def canonPort (sites : Array E) (x : E) : Array E × E × Array Int := Id.run do
  let mut s := sites
  let mut y := x
  let mut best := keyOf s y
  let mut bs := sortE s
  let mut bx := y
  for _ in [0:5] do
    s := s.map E.rot
    y := E.rot y
    let k := keyOf s y
    if ltArr k best then
      best := k; bs := sortE s; bx := y
  return (bs, bx, best)

def mkPort (sites : Array E) (x : E) : Port :=
  let (s, y, k) := canonPort sites x
  { sites := s, x := y, p := E.nrm y, key := k }

def mirrorPort (P : Port) : Port := mkPort (P.sites.map E.conj) (E.conj P.x)

/-- port-core condition: every site other than h = 0 and x has degree ≥ 3. -/
def portCores (M : Nat) : Array Port := Id.run do
  let lv := reachable M
  let mut seen : HashSet (Array Int) := {}
  let mut out := #[]
  for n in [3:M+1] do
    for S in lv[n]! do
      if isSAT S then
        for h in S do
          let rel := S.map (fun q => E.sub q h)
          for x in rel do
            if x != (0,0) then
              let ok := rel.all fun z => z == (0,0) || z == x || deg rel z ≥ 3
              if ok then
                let P := mkPort rel x
                if !seen.contains P.key then
                  seen := seen.insert P.key
                  out := out.push P
  return out

/-! ### Hinge + bar realization (s = +, second body placed by a rotation). -/

structure Real2 where
  n : Nat
  p : Int
  q : Int
  dlt : Int
  offType : Nat          -- 0 lattice, 1 type I (ζ ∉ Q(ω)), 2 type II (ζ ∈ Q(ω) \ μ6)
  extra : Nat            -- accidental cross contacts besides the bar
  P1 : Port
  P2 : Port
  key : Array Int
  deriving Inhabited

/-- returns none if overlap; else (offType, extra contacts). -/
def realize (P1 P2 : Port) : Option (Nat × Nat) := Id.run do
  let p := P1.p
  let q := P2.p
  let c := p + q - 1
  let dlt := 4*p*q - c*c
  let S := 2*p*q
  let D3 := 3*dlt
  let ab := E.mul P1.x (E.conj P2.x)     -- α β̄
  let mut extra := 0
  for a in P1.sites do
    if a != (0,0) then
      let U := E.smul S a
      for b in P2.sites do
        if b != (0,0) then
          let w := E.mul ab b
          let du := E.sub U (E.smul c w)
          let dv := E.neg w
          -- m = ω-coefficient of dv * conj(du)
          let m := (E.mul dv (E.conj du)).2
          let e0 := E.nrm du + dlt * E.nrm dv - S*S
          let sg := signSurd e0 (-m) D3
          if sg < 0 then return none
          if sg == 0 then
            if !(a == P1.x && b == P2.x) then extra := extra + 1
  -- lattice test
  let typ : Nat :=
    if dlt % 3 != 0 || !isSquare (dlt / 3) then 1
    else
      let k : Int := (isqrt (dlt/3).toNat : Nat)
      let z := E.mul ab ((c - k), 2*k)
      if E.units.any (fun u => E.smul S u == z) then 0 else 2
  return some (typ, extra)

structure Pt2 where
  u : E
  v : E
  deriving Inhabited

/-- squared distance (scaled by Sc²) as e + f·√(3D). -/
@[inline] def d2 (D : Int) (P Q : Pt2) : Int × Int :=
  let du := E.sub P.u Q.u
  let dv := E.sub P.v Q.v
  let m := (E.mul dv (E.conj du)).2
  (E.nrm du + D * E.nrm dv, -m)

def squarefreeSplit (n : Nat) : Nat × Nat := Id.run do
  -- n = f² · d0
  let mut f := 1
  let mut d0 := n
  let mut k := 2
  while k * k ≤ d0 do
    if d0 % (k*k) == 0 then
      d0 := d0 / (k*k)
      f := f * k
    else
      k := k + 1
  return (f, d0)

abbrev C := Float × Float
@[inline] def cadd (z w : C) : C := (z.1 + w.1, z.2 + w.2)
@[inline] def csub (z w : C) : C := (z.1 - w.1, z.2 - w.2)
@[inline] def cmul (z w : C) : C := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
@[inline] def cn2 (z : C) : Float := z.1 * z.1 + z.2 * z.2
@[inline] def ccross (z w : C) : Float := z.1 * w.2 - z.2 * w.1
@[inline] def toC (p : E) : C := (Float.ofInt p.1 + Float.ofInt p.2 / 2.0, Float.ofInt p.2 * Float.sqrt 3.0 / 2.0)
@[inline] def cis (t : Float) : C := (Float.cos t, Float.sin t)
def piF : Float := 3.141592653589793

/-! ## Part 4: exact coordinates and exact re-verification of hinge+bar and ring examples.
Spacing-2 convention (circles of radius 1). A point is `(u + v ι)/S` in unit spacing, `ι = i√D`,
`u, v ∈ Z[ω]`; in spacing 2 its coordinates are
  Re = [ (2u₁+u₂) - v₂ √(3D) ] / S,   Im = [ u₂ √3 + (2v₁+v₂) √D ] / S
(with u = u₁ + u₂ω, v = v₁ + v₂ω). -/

def showPt (D S : Int) (P : Pt2) : String :=
  let a := 2*P.u.1 + P.u.2
  let b := -P.v.2
  let c := P.u.2
  let d := 2*P.v.1 + P.v.2
  let fl := fun (x : Int) => Float.ofInt x
  let re := (fl a + fl b * Float.sqrt (3.0 * fl D)) / fl S
  let im := (fl c * Float.sqrt 3.0 + fl d * Float.sqrt (fl D)) / fl S
  s!"(({a}) + ({b})√{3*D})/{S} + i(({c})√3 + ({d})√{D})/{S}  ≈ ({re}, {im})"

def floatPt (D S : Int) (P : Pt2) : C :=
  let fl := fun (x : Int) => Float.ofInt x
  ((fl (2*P.u.1 + P.u.2) + fl (-P.v.2) * Float.sqrt (3.0 * fl D)) / fl S,
   (fl P.u.2 * Float.sqrt 3.0 + fl (2*P.v.1 + P.v.2) * Float.sqrt (fl D)) / fl S)

/-- exact report on a point list: contacts (exact), degrees, minimal non-contact clearance (float). -/
def report (name : String) (D S : Int) (pts : Array Pt2) : IO Unit := do
  IO.println s!"== {name}: n = {pts.size}, D = {D}, scale S = {S}"
  for i in [0:pts.size] do
    IO.println s!"  c{i} = {showPt D S pts[i]!}"
  let mut deg : Array Nat := Array.replicate pts.size 0
  let mut ne := 0
  let mut bad := 0
  let mut minClr : Float := 1000.0
  for i in [0:pts.size] do
    for j in [i+1:pts.size] do
      let (e, g) := d2 D pts[i]! pts[j]!
      let sg := signSurd (e - S*S) g (3*D)
      if sg < 0 then bad := bad + 1
      if sg == 0 then
        ne := ne + 1
        deg := (deg.set! i (deg[i]! + 1)).set! j (deg[j]! + 1)
      else
        let f := Float.sqrt (cn2 (csub (floatPt D S pts[i]!) (floatPt D S pts[j]!)))
        if f < minClr then minClr := f
  IO.println s!"  overlapping pairs: {bad}; contacts: {ne} (2n-3 = {2*pts.size - 3}); degrees: {deg.toList}"
  IO.println s!"  min center distance over non-touching pairs (spacing 2): {minClr}"

/-- hinge+bar: B1 (h = 0, x), B2 (h = 0, y), s = +, rotation placement. -/
def hbPoints (P1 P2 : Port) : Int × Int × Array Pt2 :=
  let p := P1.p
  let q := P2.p
  let c := p + q - 1
  let dlt := 4*p*q - c*c
  let S := p*q        -- spacing 2: unit-spacing denominator 2pq becomes pq
  let ab := E.mul P1.x (E.conj P2.x)
  let A := P1.sites.map (fun a => Pt2.mk (E.smul (2*S) a) (0,0))
  -- unit spacing: (c w + w ι)/(2pq); spacing 2: (c w + w ι)/(pq); our Pt2 convention is u+vι over S
  -- but showPt already doubles (uses 2u₁+u₂ etc.), so feed (c w, w) with S = 2pq.
  let B := (P2.sites.filter (· != (0,0))).map (fun b => let w := E.mul ab b; Pt2.mk (E.smul c w) w)
  (dlt, 2*p*q, (A.map (fun P => Pt2.mk (E.smul 1 P.u) P.v)).map (fun P => Pt2.mk (P.u) P.v) ++ B)

def mkP (sites : List (Int × Int)) (x : Int × Int) : Port := mkPort sites.toArray x


/-! ## Part 5: Henneberg extensions of an exact example (float positions for the new circle). -/

def latticeDist (z : C) : Float :=
  -- distance (unit spacing) from z to the nearest point of Z[ω]
  let b := 2.0 * z.2 / Float.sqrt 3.0
  let a := z.1 - b / 2.0
  let cands := #[(Float.floor a, Float.floor b), (Float.floor a + 1.0, Float.floor b),
    (Float.floor a, Float.floor b + 1.0), (Float.floor a + 1.0, Float.floor b + 1.0)]
  cands.foldl (fun m (x, y) =>
    let p : C := (x + y / 2.0, y * Float.sqrt 3.0 / 2.0)
    min m (Float.sqrt (cn2 (csub p z)))) 1000.0

def hennExt (nm : String) (P1 P2 : Port) : IO Unit := do
  let (dlt, S, pts) := hbPoints P1 P2
  -- float positions, unit spacing (divide spacing-2 coords by 2)
  let F := pts.map (fun P => let z := floatPt dlt S P; (z.1 / 2.0, z.2 / 2.0))
  let nB1 := P1.sites.size
  -- frame of B2: ζ = τ/(ᾱβ); B2 coordinates of z: (z - h)/ζ ; h = 0
  let p := Float.ofInt P1.p
  let q := Float.ofInt P2.p
  let cc := p + q - 1.0
  let ab := toC (E.mul (E.conj P1.x) P2.x)
  let tau : C := (cc / 2.0, Float.sqrt (Float.ofInt dlt) / 2.0)
  -- ζ = τ / ab
  let abn := cn2 ab
  let zeta : C := ((tau.1 * ab.1 + tau.2 * ab.2) / abn, (tau.2 * ab.1 - tau.1 * ab.2) / abn)
  let zinv : C := (zeta.1, -zeta.2)
  IO.println s!"== Henneberg extensions of {nm} (n = {F.size}); ζ ≈ {zeta}"
  for i in [0:F.size] do
    for j in [i+1:F.size] do
      let d := Float.sqrt (cn2 (csub F[i]! F[j]!))
      if d > 1.0 + 1e-9 && d < 2.0 - 1e-9 then
        let m : C := ((F[i]!.1 + F[j]!.1) / 2.0, (F[i]!.2 + F[j]!.2) / 2.0)
        let u := csub F[j]! F[i]!
        let hgt := Float.sqrt (1.0 - d * d / 4.0)
        for sgn in [1.0, -1.0] do
          let f : C := (m.1 - sgn * u.2 / d * hgt, m.2 + sgn * u.1 / d * hgt)
          let ds := F.map (fun z => Float.sqrt (cn2 (csub z f)))
          let minOther := Id.run do
            let mut mm := 1000.0
            for k in [0:F.size] do
              if k != i && k != j then mm := min mm ds[k]!
            return mm
          if minOther > 1.0 + 1e-6 then
            let inB1 := fun (k : Nat) => k < nB1
            let side := if inB1 i && inB1 j then "both in B1" else if !(inB1 i) && !(inB1 j) then "both in B2" else "one in each body"
            let l1 := latticeDist f
            let l2 := latticeDist (cmul zinv f)
            IO.println s!"  new circle touching c{i}, c{j} (|c{i}c{j}| = {2.0*d} in spacing 2; {side}); clearance to others {2.0*minOther}; dist to L1 {2.0*l1}, to L2 {2.0*l2}; f ≈ ({2.0*f.1}, {2.0*f.2})"


def dirDeg (z : E) : Float :=
  let c := toC z
  let t := Float.atan2 c.2 c.1 * 180.0 / piF
  if t < 0.0 then t + 360.0 else t

def normDeg (t : Float) : Float :=
  let r := t - 360.0 * Float.floor (t / 360.0)
  if r > 180.0 then r - 360.0 else r

/-- neighbour directions of `z` in `S`, relative to direction `ref` (degrees, in (-180,180]). -/
def nbrDirs (S : Array E) (z : E) (ref : Float) : Array Float :=
  ((S.filter (fun w => adj w z)).map (fun w => normDeg (dirDeg (E.sub w z) - ref))).qsort (· < ·)

def angGap (a b : Float) : Float := Float.abs (normDeg (a - b))

def fanMain : IO Unit := do
  let ports := portCores 8
  for p in [3, 4, 7] do
    let ps := (ports.filter (fun P => P.p == (p : Int))).qsort (fun a b => a.sites.size < b.sites.size)
    IO.println s!"p = {p}: {ps.size} port-cores with ≤ 8 sites"
    for P in ps do
      let ref := dirDeg P.x
      let hn := nbrDirs P.sites (0,0) ref
      let xn := nbrDirs P.sites P.x (dirDeg (E.neg P.x))
      IO.println s!"   size {P.sites.size}: sites {P.sites.toList} x={P.x}; h-nbr dirs rel. to h→x: {hn.toList.map (fun t => Float.round t)}; x-nbr dirs rel. to x→h: {xn.toList.map (fun t => Float.round t)}"
  -- hinge test for all pairs with total ≤ 11 circles
  let φ := fun (p q : Float) => Float.acos ((p + q - 1.0) / (2.0 * Float.sqrt (p*q))) * 180.0 / piF
  let mut tested := 0
  let mut passH := 0
  let mut passHX := 0
  for P1 in ports do
    for P2 in ports do
      let p := Float.ofInt P1.p
      let q := Float.ofInt P2.p
      let c := p + q - 1.0
      if P1.sites.size + P2.sites.size - 1 ≤ 11 && 4.0*p*q - c*c ≥ 0.0 && !(P1.p == 1 && P2.p == 1) then
        tested := tested + 1
        -- B2's port direction at +φ from B1's; B2 rotated so its port points there
        let f := φ p q
        let h1 := nbrDirs P1.sites (0,0) (dirDeg P1.x)
        let h2 := (nbrDirs P2.sites (0,0) (dirDeg P2.x)).map (· + f)
        let okH := h1.all (fun a => h2.all (fun b => angGap a b > 60.0 + 1e-6))
        if okH then
          passH := passH + 1
          -- bar-end test at x: B1's x-neighbours vs the bar direction x→y
          -- triangle h x y: angle at x between x→h and x→y is ψx with cos ψx = (p + 1 - q)/(2√p)
          let psx := Float.acos ((p + 1.0 - q) / (2.0 * Float.sqrt p)) * 180.0 / piF
          let psy := Float.acos ((q + 1.0 - p) / (2.0 * Float.sqrt q)) * 180.0 / piF
          let x1 := nbrDirs P1.sites P1.x (dirDeg (E.neg P1.x))   -- relative to x→h
          -- y lies on the +φ side, so seen from x the bar is at -ψx from x→h
          let okX := x1.all (fun a => angGap a (-psx) > 60.0 + 1e-6)
          let y2 := nbrDirs P2.sites P2.x (dirDeg (E.neg P2.x))
          let okY := y2.all (fun a => angGap a psy > 60.0 + 1e-6)
          if okX && okY then
            passHX := passHX + 1
            IO.println s!"   passes hinge+bar-end tests: |B1|={P1.sites.size} p={P1.p} B1={P1.sites.toList} x={P1.x} | |B2|={P2.sites.size} q={P2.p} B2={P2.sites.toList} y={P2.x}"
  IO.println s!"pairs with ≤ 11 circles and Δ ≥ 0: {tested}; pass hinge-fan test: {passH}; pass hinge and both bar-end tests: {passHX}"
def main : IO Unit := fanMain
