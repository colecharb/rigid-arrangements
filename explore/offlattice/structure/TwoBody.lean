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

def run (N M : Nat) : IO Unit := do
  let ports := portCores M
  IO.println s!"port-cores with ≤ {M} sites (one-sided, up to rotation): {ports.size}"
  -- smallest size for each p
  let mut best : HashMap Int Nat := {}
  for P in ports do
    let cur := best.getD P.p 1000
    if P.sites.size < cur then best := best.insert P.p P.sites.size
  let ps := (best.toArray.qsort (fun a b => a.1 < b.1))
  IO.println s!"smallest port-core size by p = N(x - h): {ps.toList}"
  let mut found : HashMap (Array Int) Real2 := {}
  let mut cnt := 0
  for P1 in ports do
    for P2 in ports do
      let n := P1.sites.size + P2.sites.size - 1
      if n ≤ N then
        let p := P1.p
        let q := P2.p
        let c := p + q - 1
        let dlt := 4*p*q - c*c
        if dlt ≥ 0 && !(p == 1 && q == 1) then
          match realize P1 P2 with
          | none => pure ()
          | some (typ, extra) =>
            cnt := cnt + 1
            let k1 := P1.key ++ #[999] ++ P2.key
            let M1 := mirrorPort P1
            let M2 := mirrorPort P2
            let k2 := M2.key ++ #[999] ++ M1.key
            let key := if ltArr k2 k1 then k2 else k1
            if !found.contains key then
              let r : Real2 := ⟨n, p, q, dlt, typ, extra, P1, P2, key⟩
              found := found.insert key r
  IO.println s!"non-overlapping realizations (ordered, s=+): {cnt}; free classes: {found.size}"
  let all := found.toArray.map (·.2)
  for n in [7:N+1] do
    let here := all.filter (·.n == n)
    let off1 := here.filter (fun r => r.offType == 1 && r.extra == 0)
    let off2 := here.filter (fun r => r.offType == 2 && r.extra == 0)
    let lat := here.filter (fun r => r.offType == 0 && r.extra == 0)
    let ex := here.filter (fun r => r.extra > 0)
    IO.println s!"n={n}: off-lattice typeI={off1.size} typeII={off2.size} lattice={lat.size} withExtraContacts={ex.size} (ex off: {(ex.filter (·.offType != 0)).size})"
  -- per (p,q): number of off-lattice classes (no extra contacts) and the smallest n
  let mut pqTab : HashMap (Int × Int) (Nat × Nat) := {}
  for r in all do
    if r.offType != 0 && r.extra == 0 then
      let k := if r.p ≤ r.q then (r.p, r.q) else (r.q, r.p)
      let (c0, m0) := pqTab.getD k (0, 1000)
      pqTab := pqTab.insert k (c0 + 1, min m0 r.n)
  let pqs := pqTab.toArray.qsort (fun a b => a.2.2 < b.2.2 || (a.2.2 == b.2.2 && (a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2))))
  IO.println s!"(p,q) ↦ (#off-lattice cores with one bar, smallest n): {pqs.toList}"
  for r in (all.qsort (fun a b => a.n < b.n || (a.n == b.n && (a.p < b.p || (a.p == b.p && a.q < b.q))))) do
    if r.offType != 0 && r.n ≤ N then
      let ab := E.mul r.P1.x (E.conj r.P2.x)
      -- float angles
      let pf := Float.ofInt r.p
      let qf := Float.ofInt r.q
      let cf := pf + qf - 1.0
      let phi := Float.acos (cf / (2.0 * Float.sqrt (pf*qf))) * 180.0 / 3.141592653589793
      -- ζ = αβ̄(c + i√Δ)/(2pq)
      let abx := Float.ofInt ab.1 + Float.ofInt ab.2 / 2.0
      let aby := Float.ofInt ab.2 * Float.sqrt 3.0 / 2.0
      let sd := Float.sqrt (Float.ofInt r.dlt)
      let zx := abx * cf - aby * sd
      let zy := abx * sd + aby * cf
      let th := Float.atan2 zy zx * 180.0 / 3.141592653589793
      let thm := th - 60.0 * Float.round (th / 60.0)
      IO.println s!"  n={r.n} p={r.p} q={r.q} Δ={r.dlt} type={r.offType} extra={r.extra} φ={phi} θ(frame rot mod 60)={thm} |B1|={r.P1.sites.size} |B2|={r.P2.sites.size} B1={r.P1.sites.toList} x={r.P1.x} B2={r.P2.sites.toList} y={r.P2.x}"

def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "13").toNat!
  let M := (args.getD 1 "10").toNat!
  run N M
