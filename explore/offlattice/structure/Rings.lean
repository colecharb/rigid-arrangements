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


/-! ## Part 2: (p,q) table, double hinges, three-body rings (exact). -/

/-- elements of norm `p`, up to units (canonical rep = lexicographically least rotation). -/
def elemsOfNorm (p : Int) : Array E := Id.run do
  let r : Int := (isqrt (4 * p.toNat / 3 + 1) : Nat) + 1
  let mut out : Array E := #[]
  for a in [0:(2*r+1).toNat] do
    for b in [0:(2*r+1).toNat] do
      let x : E := ((a : Int) - r, (b : Int) - r)
      if E.nrm x == p then
        let mut best := x
        let mut y := x
        for _ in [0:5] do
          y := E.rot y
          if ltE y best then best := y
        if !out.contains best then out := out.push best
  return out

@[inline] def isAssoc (x y : E) : Bool := E.units.any (fun u => E.mul u x == y)

def pqTable (Pmax : Int) : IO Unit := do
  let norms := (List.range (Pmax.toNat + 1)).filter (fun (p : Nat) => p ≥ 1 && (elemsOfNorm (p : Int)).size > 0)
  IO.println s!"Eisenstein norms ≤ {Pmax}: {norms}"
  for p in norms do
    for q in norms do
      if p ≤ q then
        let pI : Int := p
        let qI : Int := q
        let c := pI + qI - 1
        let dlt := 4*pI*qI - c*c
        if dlt ≥ 0 && !(p == 1 && q == 1) then
          if dlt % 3 != 0 || !isSquare (dlt / 3) then
            IO.println s!"  (p,q)=({p},{q}) Δ={dlt} cosφ={c}/(2√{p*q}) : type I, every realization off-lattice"
          else
            let k : Int := (isqrt (dlt/3).toNat : Nat)
            let mut lat := 0
            let mut off := 0
            for al in elemsOfNorm pI do
              for be in elemsOfNorm qI do
                for s in [(1 : Int), -1] do
                  let tau : E := ((c - s*k)/2, s*k)
                  if isAssoc tau (E.mul (E.conj al) be) then lat := lat + 1 else off := off + 1
            let tag := if off == 0 then "always lattice" else if lat == 0 then "type II only" else "mixed (lattice and type II)"
            IO.println s!"  (p,q)=({p},{q}) Δ={dlt}=3·{k}² : {tag}  [(α,β,s) combos: lattice {lat}, off {off}]"

/-! ### Double hinge: two bodies sharing two circles `0` and `a`, frames related by `ζ = a/a'`. -/

def dhKey (P1 P2 : Port) : Array Int := Id.run do
  let mut best : Array Int := #[]
  let mut first := true
  for (Q1, Q2) in [(P1, P2), (P2, P1)] do
    for flip in [false, true] do
      let R1 := if flip then mkPort (Q1.sites.map (fun z => E.sub z Q1.x)) (E.neg Q1.x) else Q1
      let R2 := if flip then mkPort (Q2.sites.map (fun z => E.sub z Q2.x)) (E.neg Q2.x) else Q2
      for mir in [false, true] do
        let S1 := if mir then mirrorPort R1 else R1
        let S2 := if mir then mirrorPort R2 else R2
        let k := S1.key ++ #[999] ++ S2.key
        if first || ltArr k best then
          best := k
          first := false
  return best

def doubleHinge (N : Nat) (ports : Array Port) : IO Unit := do
  let mut found : HashMap (Array Int) (Nat × Nat × Port × Port) := {}
  for P1 in ports do
    for P2 in ports do
      let n := P1.sites.size + P2.sites.size - 2
      if n ≤ N && P1.p == P2.p && !isAssoc P2.x P1.x then
        let p := P1.p
        let z := E.mul P1.x (E.conj P2.x)   -- ζ·p
        let mut ok := true
        let mut extra := 0
        for a in P1.sites do
          if ok && a != (0,0) && a != P1.x then
            for b in P2.sites do
              if ok && b != (0,0) && b != P2.x then
                let d := E.nrm (E.sub (E.smul p a) (E.mul z b))
                if d < p*p then ok := false
                else if d == p*p then extra := extra + 1
        if ok then
          let key := dhKey P1 P2
          if !found.contains key then found := found.insert key (n, extra, P1, P2)
  let all := found.toArray.map (·.2)
  for n in [6:N+1] do
    let here := all.filter (·.1 == n)
    if here.size > 0 then
      IO.println s!"double hinge n={n}: {here.size} classes ({(here.filter (·.2.1 == 0)).size} without extra contacts)"
      for (_, ex, P1, P2) in here do
        if n ≤ N then
          IO.println s!"    p={P1.p} extra={ex} B1={P1.sites.toList} a={P1.x} B2={P2.sites.toList} a'={P2.x}"

/-! ### Three-body rings. Hinges H12 = 0, H13 = x1 (in B1), H23. -/

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

def fingerprint (D : Int) (Sc : Int) (pts : Array Pt2) : String := Id.run do
  let (f, d0) := squarefreeSplit (3 * D).toNat
  let mut ds : Array (Rat × Rat) := #[]
  for i in [0:pts.size] do
    for j in [i+1:pts.size] do
      let (e, g) := d2 D pts[i]! pts[j]!
      ds := ds.push ((e : Rat) / (Sc*Sc : Int), ((g * (f : Int)) : Rat) / (Sc*Sc : Int))
  let srt := ds.qsort (fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 < b.2)))
  return s!"{if d0 == 1 then 0 else d0}|{srt.toList}"

def rings (N : Nat) (ports : Array Port) : IO Unit := do
  let mut found : HashMap String (Nat × Nat × Nat × Int × Int × Int × Port × Port × Port) := {}
  let small := ports.filter (fun P => P.sites.size + 8 ≤ N + 3)
  for P1 in small do
    for P2 in small do
      if P1.sites.size + P2.sites.size + 4 ≤ N + 3 then
      for P3 in small do
        let n := P1.sites.size + P2.sites.size + P3.sites.size - 3
        if n ≤ N then
          let a := P1.p
          let b := P2.p
          let c := P3.p
          let D := 2*a*b + 2*b*c + 2*c*a - a*a - b*b - c*c
          if D ≥ 0 then
            let Sc := 2*a*b*c
            let x1 := P1.x
            let w2 := E.mul (E.smul c x1) (E.conj P2.x)
            let w3 := E.mul (E.smul b x1) (E.conj P3.x)
            let A1 := P1.sites.map (fun z => (z, Pt2.mk (E.smul Sc z) (0,0)))
            let A2 := P2.sites.map (fun z => (z, let w := E.mul w2 z; Pt2.mk (E.smul (a + b - c) w) w))
            let A3 := P3.sites.map (fun z => (z, let w := E.mul w3 z;
                                      Pt2.mk (E.add (E.smul Sc x1) (E.smul (b - a - c) w)) w))
            -- pairs: (B1,B2) share H12 = site 0 of both; (B1,B3) share H13 = x1 of B1 / 0 of B3;
            -- (B2,B3) share H23 = x2 of B2 / x3 of B3.
            let mut ok := true
            let mut extra := 0
            let check := fun (L R : Array (E × Pt2)) (sl sr : E) (ok : Bool) (extra : Nat) => Id.run do
              let mut ok := ok
              let mut extra := extra
              for (zl, Pl) in L do
                if ok && zl != sl then
                  for (zr, Pr) in R do
                    if ok && zr != sr then
                      let (e, g) := d2 D Pl Pr
                      let sg := signSurd (e - Sc*Sc) g (3*D)
                      if sg < 0 then ok := false
                      else if sg == 0 then extra := extra + 1
              return (ok, extra)
            (ok, extra) := check A1 A2 (0,0) (0,0) ok extra
            if ok then (ok, extra) := check A1 A3 x1 (0,0) ok extra
            if ok then (ok, extra) := check A2 A3 P2.x P3.x ok extra
            if ok then
              -- lattice type
              let typ : Nat :=
                if D % 3 != 0 || !isSquare (D / 3) then 1
                else
                  let k : Int := (isqrt (D/3).toNat : Nat)
                  let io : E := (-k, 2*k)    -- ι = k(2ω - 1)
                  let z2 := E.mul w2 (E.add ((a + b - c), 0) io)        -- ζ2 · Sc·(...)
                  let z3 := E.mul w3 (E.add ((b - a - c), 0) io)
                  -- ζ2 = x1 x̄2 (a+b-c+ι)/(2ab): z2 = c·x1 x̄2 (a+b-c+ι) = Sc·ζ2
                  if E.units.any (fun u => E.smul Sc u == z2) && E.units.any (fun u => E.smul Sc u == z3) then 0 else 2
              -- union point list for fingerprint
              let pts := (A1.map (·.2)) ++ ((A2.filter (fun q => q.1 != (0,0))).map (·.2)) ++
                ((A3.filter (fun q => q.1 != (0,0) && q.1 != P3.x)).map (·.2))
              let fp := fingerprint D Sc pts
              if !found.contains fp then
                found := found.insert fp (n, typ, extra, a, b, c, P1, P2, P3)
  let all := found.toArray.map (·.2)
  for n in [9:N+1] do
    let here := all.filter (·.1 == n)
    let o1 := here.filter (fun r => r.2.1 == 1 && r.2.2.1 == 0)
    let o2 := here.filter (fun r => r.2.1 == 2 && r.2.2.1 == 0)
    let lt := here.filter (fun r => r.2.1 == 0 && r.2.2.1 == 0)
    let ex := here.filter (fun r => r.2.2.1 > 0)
    IO.println s!"rings n={n}: off typeI={o1.size} typeII={o2.size} lattice={lt.size} extraContacts={ex.size} (off among them {(ex.filter (·.2.1 != 0)).size})"
    for (_, typ, ex, a, b, c, P1, P2, P3) in here do
      if typ != 0 then
        let D := 2*a*b + 2*b*c + 2*c*a - a*a - b*b - c*c
        IO.println s!"    type={typ} extra={ex} (a,b,c)=({a},{b},{c}) D={D} B1={P1.sites.toList} H13={P1.x} B2={P2.sites.toList} H23={P2.x} B3={P3.sites.toList} H23'={P3.x}"

def main (args : List String) : IO Unit := do
  let mode := args.getD 0 "pq"
  if mode == "pq" then pqTable ((args.getD 1 "50").toNat! : Int)
  else if mode == "dh" then
    let N := (args.getD 1 "16").toNat!
    let ports := portCores (N - 3)
    doubleHinge N ports
  else if mode == "ring" then
    let N := (args.getD 1 "14").toNat!
    let ports := portCores (N - 5)
    IO.println s!"ports used: {ports.size}"
    rings N ports
