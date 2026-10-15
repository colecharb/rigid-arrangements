/-! Rigorous interval-arithmetic certificate for H30 (lattice body of 26 circles + free 4-ring).
Exploratory `main`, no Mathlib. Numbers are fixed-point integers scaled by S = 2^200, intervals
rounded outward. Real coordinates: lattice site (a,b) ↦ (2a + b, √3 b). Ring centre c = (2, -√3);
by central symmetry w1 = c + p, w3 = c - p, w2 = c + q, w4 = c - q, p = (u, v), q = (s, t):
 (1) |p + (3,0)|² = 4         [bar w1–x1, x1 = site (0,-1), x1 - c = (-3, 0)]
 (2) |q - (1, 2√3)|² = 4      [bar w2–x2, x2 = site (1,1),  x2 - c = (1, 2√3)]
 (3) p·q = 0, (4) |p|² + |q|² = 4   [rhombus of side 2]
Elimination: v = √(4 - (u+3)²), t = -u(9+3u)/(v - 2√3 u), s = 9 + 3u - 2√3 t, and
G(u) := (s-1)² + (t-2√3)² - 4 = 0. -/

def S : Int := 2 ^ 200

def fdiv (a b : Int) : Int := if b > 0 then Int.ediv a b else Int.ediv (-a) (-b)   -- floor, b ≠ 0
def cdiv (a b : Int) : Int := -(fdiv (-a) b)

structure I where
  lo : Int
  hi : Int
deriving Inhabited

namespace I
def ofInt (n : Int) : I := ⟨n * S, n * S⟩
def ofRat (a b : Int) : I := ⟨fdiv (a * S) b, cdiv (a * S) b⟩
instance : OfNat I n := ⟨ofInt n⟩
def add (x y : I) : I := ⟨x.lo + y.lo, x.hi + y.hi⟩
def neg (x : I) : I := ⟨-x.hi, -x.lo⟩
def sub (x y : I) : I := add x (neg y)
def mul (x y : I) : I :=
  let ps := [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
  let mn := ps.foldl min (x.lo * y.lo)
  let mx := ps.foldl max (x.lo * y.lo)
  ⟨fdiv mn S, cdiv mx S⟩
def pos (x : I) : Bool := 0 < x.lo
def neg? (x : I) : Bool := x.hi < 0
def inv (x : I) : Option I :=
  if pos x || neg? x then some ⟨fdiv (S * S) x.hi, cdiv (S * S) x.lo⟩ else none
def div (x y : I) : Option I := (inv y).map (mul x)
instance : Add I := ⟨add⟩
instance : Sub I := ⟨sub⟩
instance : Mul I := ⟨mul⟩
instance : Neg I := ⟨neg⟩
def isqrtFloor (n : Nat) : Nat := Nat.sqrt n
def isqrtCeil (n : Nat) : Nat := let r := Nat.sqrt n; if r * r == n then r else r + 1
def sqrt (x : I) : Option I :=
  if x.lo < 0 then none
  else some ⟨isqrtFloor (x.lo * S).toNat, isqrtCeil (x.hi * S).toNat⟩
def contains (x : I) (q : Int) : Bool := x.lo ≤ q * S && q * S ≤ x.hi
/-- decimal rendering of the interval with `d` digits. -/
def shw (x : I) (d : Nat := 12) : String :=
  let p := (10 : Int) ^ d
  s!"[{fdiv (x.lo * p) S}, {cdiv (x.hi * p) S}]e-{d}"
end I

open I

def r3 : I := (I.sqrt (I.ofInt 3)).get!

structure V2 where
  x : I
  y : I
deriving Inhabited
def V2.sub (a b : V2) : V2 := ⟨a.x - b.x, a.y - b.y⟩
def V2.add (a b : V2) : V2 := ⟨a.x + b.x, a.y + b.y⟩
def V2.dot (a b : V2) : I := a.x * b.x + a.y * b.y
def V2.n2 (a : V2) : I := a.dot a

def site (p : Int × Int) : V2 := ⟨I.ofInt (2 * p.1 + p.2), I.ofInt p.2 * r3⟩

def solve (u : I) : Option (V2 × V2 × I) := do
  let w := 4 - (u + 3) * (u + 3)
  let v ← I.sqrt w
  let den := v - 2 * r3 * u
  let t ← I.div (-(u * (9 + 3 * u))) den
  let s := 9 + 3 * u - 2 * r3 * t
  let G := (s - 1) * (s - 1) + (t - 2 * r3) * (t - 2 * r3) - 4
  return (⟨u, v⟩, ⟨s, t⟩, G)

def body : List (Int × Int) := [(-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
  (0, -3), (0, -2), (0, -1), (0, 1), (0, 2), (1, -4), (1, -3), (1, 1), (1, 2), (2, -4), (2, -3),
  (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0)]

def eN (p : Int × Int) : Int := p.1 * p.1 + p.1 * p.2 + p.2 * p.2

def intRank (rows : Array (Array Int)) (ncols : Nat) : Nat := Id.run do
  let mut M := rows
  let m := M.size
  let mut r := 0
  for col in [0:ncols] do
    if r < m then
      let mut piv := m
      for i in [r:m] do
        if piv == m && M[i]![col]! != 0 then piv := i
      if piv < m then
        let rowP := M[piv]!
        M := (M.set! piv M[r]!).set! r rowP
        let pv := rowP[col]!
        for i in [r+1:m] do
          let rowI := M[i]!
          let f := rowI[col]!
          let g := Int.gcd pv f
          let a := pv / g
          let b := f / g
          M := M.set! i ((List.range ncols).toArray.map fun j => a * rowI[j]! - b * rowP[j]!)
        r := r + 1
  return r

def bodyRank : Nat × Nat := Id.run do
  let b := body.toArray
  let n := b.size
  let mut rows : Array (Array Int) := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      let d := (b[i]!.1 - b[j]!.1, b[i]!.2 - b[j]!.2)
      if eN d == 1 then
        rows := rows.push ((((((Array.replicate (2*n) (0:Int)).set! (2*i) d.1).set! (2*i+1) d.2).set!
          (2*j) (-d.1)).set! (2*j+1) (-d.2)))
  return (rows.size, intRank rows (2*n))

/-- certified nonsingularity by interval Gaussian elimination (pivots bounded away from 0). -/
def certNonsingular (M0 : Array (Array I)) : Bool := Id.run do
  let n := M0.size
  let mut M := M0
  for col in [0:n] do
    let mut piv := n
    let mut best : Int := -1
    for i in [col:n] do
      let e := M[i]![col]!
      let mag := max e.lo.natAbs e.hi.natAbs
      if (I.pos e || I.neg? e) && (mag : Int) > best then best := mag; piv := i
    if piv == n then return false
    let rowP := M[piv]!
    M := (M.set! piv M[col]!).set! col rowP
    for i in [col+1:n] do
      let rowI := M[i]!
      match I.div rowI[col]! rowP[col]! with
      | none => return false
      | some f => M := M.set! i ((List.range n).toArray.map fun j => rowI[j]! - f * rowP[j]!)
  return true

def main : IO Unit := do
  let ua := I.ofRat (-1055627) 1000000
  let ub := I.ofRat (-1055427) 1000000
  let some (_, _, Ga) := solve ua | IO.println "fail a"
  let some (_, _, Gb) := solve ub | IO.println "fail b"
  IO.println s!"G(-1.055627) ∈ {Ga.shw}; G(-1.055427) ∈ {Gb.shw}"
  if !((I.pos Ga && I.neg? Gb) || (I.neg? Ga && I.pos Gb)) then IO.println "no certified sign change"
  -- continuity on the whole bracket: sqrt argument > 0 and denominator bounded away from 0
  let Uall : I := ⟨ua.lo, ub.hi⟩
  let w := 4 - (Uall + 3) * (Uall + 3)
  let vv := (I.sqrt w).get!
  IO.println s!"on [ua,ub]: 4-(u+3)² ∈ {w.shw 6} (>0: {I.pos w}); v - 2√3u ∈ {(vv - 2 * r3 * Uall).shw 6} (>0: {I.pos (vv - 2 * r3 * Uall)})"
  -- bisection (each midpoint evaluated rigorously) to shrink the bracket
  let mut lo := ua.lo
  let mut hi := ub.lo
  let posLo := I.pos Ga
  for _ in [0:150] do
    let m := (lo + hi) / 2
    match solve ⟨m, m⟩ with
    | some (_, _, g) =>
      if I.pos g || I.neg? g then
        if I.pos g == posLo then lo := m else hi := m
    | none => pure ()
  let U : I := ⟨lo, hi⟩
  IO.println s!"root bracket u ∈ {U.shw 30}"
  let some (p, q, G) := solve U | IO.println "solve failed"
  IO.println s!"G on bracket ∈ {G.shw 20} (contains 0: IVT gives an exact root u* inside, since G is continuous there and changes sign at the ends)"
  let c : V2 := ⟨2, -r3⟩
  let ring : Array V2 := #[c.add p, c.add q, c.sub p, c.sub q]
  for k in [0:4] do
    IO.println s!"w{k+1} = ({ring[k]!.x.shw 15}, {ring[k]!.y.shw 15})"
  let pts : Array V2 := (body.map site).toArray ++ ring
  let n := pts.size
  let mut latContacts := 0
  let mut ambiguous : Array (Nat × Nat) := #[]
  let mut minSlack : Int := S * 1000
  let mut overlap := false
  for i in [0:n] do
    for j in [i+1:n] do
      if i < 26 && j < 26 then
        let e := eN ((body[i]!.1 - body[j]!.1), (body[i]!.2 - body[j]!.2))
        if e == 1 then latContacts := latContacts + 1
        if e < 1 then overlap := true
      else
        let d2 := (pts[i]!.sub pts[j]!).n2
        if I.contains d2 4 then ambiguous := ambiguous.push (i, j)
        else if d2.lo > 4 * S then minSlack := min minSlack (d2.lo - 4 * S)
        else overlap := true
  IO.println s!"lattice contacts (exact) = {latContacts}; overlap found = {overlap}"
  IO.println s!"ring pairs with d² not separated from 4 (must be exactly the 8 designed contacts): {ambiguous.toList}"
  IO.println s!"all other ring pairs: d² - 4 ≥ {fdiv (minSlack * 10000) S}e-4"
  IO.println s!"body: (contacts, exact rank) = {bodyRank} ; 2·26-3 = 49"
  let xs : Array V2 := #[site (0,-1), site (1,1), site (3,-1), site (2,-3)]
  let z : I := 0
  let mut M : Array (Array I) := #[]
  for i in [0:4] do
    let d := ring[i]!.sub xs[i]!
    M := M.push (((Array.replicate 8 z).set! (2*i) d.x).set! (2*i+1) d.y)
  for i in [0:4] do
    let j := (i + 1) % 4
    let d := ring[i]!.sub ring[j]!
    M := M.push (((((Array.replicate 8 z).set! (2*i) d.x).set! (2*i+1) d.y).set! (2*j) (-d.x)).set! (2*j+1) (-d.y))
  IO.println s!"8×8 ring-relative rigidity matrix certified nonsingular: {certNonsingular M}"
  let dl := (ring[0]!.sub (site (1,-1))).n2
  IO.println s!"|w1 - site(1,-1)|² ∈ {dl.shw 6} (so w1 is not a lattice point: every other lattice point is ≥ 1 farther)"
  let d13 := (ring[0]!.sub ring[2]!).n2
  let d24 := (ring[1]!.sub ring[3]!).n2
  IO.println s!"diagonals: |w1-w3|² ∈ {d13.shw 12}, |w2-w4|² ∈ {d24.shw 12}; cos(ring angle at w2) = 1 - |w1-w3|²/8"

