namespace CaseB

/-!
# Rigorous rational interval arithmetic, and certificates for a closure

Same scheme as `explore/offlattice/adversary/H30CertI.lean`: fixed-point integers scaled by
`SC = 2^160`, intervals rounded outward, so every printed bound is a theorem about the real
configuration (modulo the correctness of this code).  Nothing here is `native_decide`'d or
otherwise trusted by the library; it is an exploratory certificate.

What `certify` establishes, for one anchor 4-cycle and one branch `(sy, σ₂, σ₄, σ₃)`:

1. a rational bracket `[dlo, dhi]` for `d = w₁ₓ − x₁ₓ` on which the branch is continuous
   (`4 − d² > 0`, and each circle-circle intersection has `0 < L² < 16`), and on whose endpoints
   `F = |w₃ − x₃|² − 4` takes opposite signs — so by the intermediate value theorem there is an
   exact root `d°` inside, i.e. an exact closed side-2 rhombus;
2. interval enclosures of `w₁ … w₄` at `d°`, hence rigorous bounds on the diagonals (both `> 4`
   in square, so the ring is triangle-free), on the clearances `|wᵢ − p|² − 4 > 0` for every
   lattice site `p` of the body other than the designated anchor, and on `|z⁶ − 64| > 0` for a
   contact vector `z` (the frame criterion: off the lattice);
3. nonsingularity of the 8×8 ring-relative rigidity matrix by interval Gaussian elimination,
   which together with the exact rank of the body gives total rank `2n − 3`.
-/

def SC : Int := 2 ^ 160

def fdivI (a b : Int) : Int := if b > 0 then Int.ediv a b else Int.ediv (-a) (-b)
def cdivI (a b : Int) : Int := -(fdivI (-a) b)

structure I where
  lo : Int
  hi : Int
  deriving Inhabited

namespace I
def ofInt (n : Int) : I := ⟨n * SC, n * SC⟩
def ofRat (a b : Int) : I := ⟨fdivI (a * SC) b, cdivI (a * SC) b⟩
instance : OfNat I n := ⟨ofInt n⟩
def add (x y : I) : I := ⟨x.lo + y.lo, x.hi + y.hi⟩
def neg (x : I) : I := ⟨-x.hi, -x.lo⟩
def sub (x y : I) : I := add x (neg y)
def mul (x y : I) : I :=
  let ps := [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
  ⟨fdivI (ps.foldl min (x.lo * y.lo)) SC, cdivI (ps.foldl max (x.lo * y.lo)) SC⟩
def pos (x : I) : Bool := 0 < x.lo
def isNeg (x : I) : Bool := x.hi < 0
def inv (x : I) : Option I :=
  if pos x || isNeg x then some ⟨fdivI (SC * SC) x.hi, cdivI (SC * SC) x.lo⟩ else none
def div (x y : I) : Option I := (inv y).map (mul x)
instance : Add I := ⟨add⟩
instance : Sub I := ⟨sub⟩
instance : Mul I := ⟨mul⟩
instance : Neg I := ⟨neg⟩
def sqrt (x : I) : Option I :=
  if x.lo < 0 then none
  else
    let a := (x.lo * SC).toNat
    let b := (x.hi * SC).toNat
    let rb := Nat.sqrt b
    some ⟨Nat.sqrt a, if rb * rb == b then rb else rb + 1⟩
/-- decimal rendering of the interval with `d` digits. -/
def shw (x : I) (d : Nat := 12) : String :=
  let p := (10 : Int) ^ d
  s!"[{fdivI (x.lo * p) SC}, {cdivI (x.hi * p) SC}]e-{d}"
def wid (x : I) : Int := x.hi - x.lo
end I

open I

def r3I : I := (I.sqrt (I.ofInt 3)).get!

structure V2I where
  x : I
  y : I
  deriving Inhabited

def V2I.sub (a b : V2I) : V2I := ⟨a.x - b.x, a.y - b.y⟩
def V2I.n2 (a : V2I) : I := a.x * a.x + a.y * a.y
def V2I.d2 (a b : V2I) : I := (a.sub b).n2
def siteI (p : Site) : V2I := ⟨I.ofInt (2 * p.1 + p.2), I.ofInt p.2 * r3I⟩

/-- the two points at distance 2 from both `A` and `B`; `sg = ±1`.  `none` unless `0 < L² < 16`
is *certified*, which is exactly the condition for the branch to be continuous here. -/
def cciI (A B : V2I) (sg : Int) : Option V2I := do
  let dx := B.x - A.x
  let dy := B.y - A.y
  let l2 := dx * dx + dy * dy
  guard (I.pos l2)
  guard (I.pos (I.ofInt 16 - l2))
  let q ← I.div (I.ofInt 16 - l2) (I.ofInt 4 * l2)
  let g0 ← I.sqrt q
  let g := I.ofInt sg * g0
  let h ← I.div dx (I.ofInt 2)
  let k ← I.div dy (I.ofInt 2)
  return ⟨A.x + h - g * dy, A.y + k + g * dx⟩

/-- the four free centres over an interval `U` of `d = w₁ₓ − x₁ₓ`, plus `F = |w₃ − x₃|² − 4`. -/
def closeI (xs : Array Site) (U : I) (sy sg2 sg4 sg3 : Int) : Option (Array V2I × I) := do
  let x1 := siteI xs[0]!; let x2 := siteI xs[1]!
  let x3 := siteI xs[2]!; let x4 := siteI xs[3]!
  let r ← I.sqrt (I.ofInt 4 - U * U)
  let w1 : V2I := ⟨x1.x + U, x1.y + I.ofInt sy * r⟩
  let w2 ← cciI w1 x2 sg2
  let w4 ← cciI w1 x4 sg4
  let w3 ← cciI w2 w4 sg3
  return (#[w1, w2, w3, w4], w3.d2 x3 - I.ofInt 4)

/-- `z⁶ − 64` as a pair of intervals, for `|z| = 2`: zero exactly on the lattice directions. -/
def z6I (z : V2I) : I × I :=
  let re2 := z.x * z.x - z.y * z.y
  let im2 := I.ofInt 2 * z.x * z.y
  let re3 := re2 * z.x - im2 * z.y
  let im3 := re2 * z.y + im2 * z.x
  (re3 * re3 - im3 * im3 - I.ofInt 64, I.ofInt 2 * re3 * im3)

/-- certified nonsingularity by interval Gaussian elimination (every pivot bounded off 0). -/
def certNonsingular (M0 : Array (Array I)) : Bool := Id.run do
  let n := M0.size
  let mut M := M0
  for col in [0:n] do
    let mut piv := n
    let mut best : Int := -1
    for i in [col:n] do
      let e := M[i]![col]!
      let mag := max e.lo.natAbs e.hi.natAbs
      if (I.pos e || I.isNeg e) && (mag : Int) > best then best := mag; piv := i
    if piv == n then return false
    let rowP := M[piv]!
    M := (M.set! piv M[col]!).set! col rowP
    for i in [col+1:n] do
      let rowI := M[i]!
      match I.div rowI[col]! rowP[col]! with
      | none => return false
      | some f => M := M.set! i ((List.range n).toArray.map fun j => rowI[j]! - f * rowP[j]!)
  return true

def ringMatrixI (xs : Array Site) (ws : Array V2I) : Array (Array I) := Id.run do
  let z : I := I.ofInt 0
  let mut M : Array (Array I) := #[]
  for i in [0:4] do
    let d := ws[i]!.sub (siteI xs[i]!)
    M := M.push (((Array.replicate 8 z).set! (2*i) d.x).set! (2*i+1) d.y)
  for i in [0:4] do
    let j := (i + 1) % 4
    let d := ws[i]!.sub ws[j]!
    M := M.push (((((Array.replicate 8 z).set! (2*i) d.x).set! (2*i+1) d.y).set!
      (2*j) (I.ofInt 0 - d.x)).set! (2*j+1) (I.ofInt 0 - d.y))
  return M

/-- full certificate for one closure.  `body` may be empty (then only the ring is certified). -/
def certify (xs : Array Site) (body : Array Site) (C : Cand) (digits : Nat := 30) : String :=
  Id.run do
    let x1f := siteF xs[0]!
    let d := C.ws[0]!.x - x1f.x
    let sy : Int := if C.ws[0]!.y - x1f.y ≥ 0.0 then 1 else -1
    let sg2 : Int := if C.sg2 > 0.0 then 1 else -1
    let sg4 : Int := if C.sg4 > 0.0 then 1 else -1
    let sg3 : Int := if C.sg3 > 0.0 then 1 else -1
    let den : Int := 10 ^ 15
    let c0 := roundToInt (d * 1.0e15)
    -- widen the bracket until a sign change of F is certified at the endpoints
    let mut lo : Int := 0
    let mut hi : Int := 0
    let mut found := false
    let mut k : Int := 1
    for _ in [0:9] do
      let a := I.ofRat (c0 - k) den
      let b := I.ofRat (c0 + k) den
      match closeI xs a sy sg2 sg4 sg3, closeI xs b sy sg2 sg4 sg3 with
      | some (_, fa), some (_, fb) =>
        if (I.pos fa && I.isNeg fb) || (I.isNeg fa && I.pos fb) then
          lo := c0 - k; hi := c0 + k; found := true; break
      | _, _ => pure ()
      k := k * 10
    if !found then return "  CERT FAILED: no certified sign change of F near the float root"
    let posLo := (closeI xs (I.ofRat lo den) sy sg2 sg4 sg3).bind (fun p => some (I.pos p.2))
    -- bisect, each midpoint evaluated rigorously, to shrink the bracket
    let mut a := (I.ofRat lo den).lo
    let mut b := (I.ofRat hi den).hi
    for _ in [0:(4 * digits)] do
      let m := (a + b) / 2
      match closeI xs ⟨m, m⟩ sy sg2 sg4 sg3 with
      | some (_, g) =>
        if I.pos g || I.isNeg g then
          if some (I.pos g) == posLo then a := m else b := m
      | none => pure ()
    let U : I := ⟨a, b⟩
    let some (ws, F) := closeI xs U sy sg2 sg4 sg3
      | return "  CERT FAILED: the shrunken bracket is not in the branch's domain"
    let mut out : Array String := #[]
    out := out.push s!"  branch (sy,σ2,σ4,σ3) = ({sy},{sg2},{sg4},{sg3})"
    out := out.push s!"  d = w1x − x1x ∈ {U.shw digits}   (bracket width {(U.wid)} / 2^160)"
    out := out.push s!"  F = |w3−x3|²−4 ∈ {F.shw 24}  (IVT: F changes sign on the bracket, and \
      the branch is continuous there, so an exact root lies inside)"
    for i in [0:4] do
      out := out.push s!"  w{i+1} = ({ws[i]!.x.shw digits}, {ws[i]!.y.shw digits})"
    let d13 := ws[0]!.d2 ws[2]!
    let d24 := ws[1]!.d2 ws[3]!
    out := out.push s!"  |w1−w3|² ∈ {d13.shw 24}  > 4 : {I.pos (d13 - I.ofInt 4)}"
    out := out.push s!"  |w2−w4|² ∈ {d24.shw 24}  > 4 : {I.pos (d24 - I.ofInt 4)}"
    out := out.push s!"  (16/3 = 5.3333…; a side-2 rhombus ON the lattice has a diagonal of \
      exactly 2, so both diagonals > 2 already certifies the ring is not a lattice rhombus)"
    -- tether lengths are 2 by construction; check the other anchor/ring separations
    let mut sepOk := true
    let mut sepMin : I := I.ofInt 1000
    for i in [0:4] do
      for j in [0:4] do
        if i != j then
          let s := ws[i]!.d2 (siteI xs[j]!) - I.ofInt 4
          if !I.pos s then sepOk := false
          if s.hi < sepMin.hi then sepMin := s
    out := out.push s!"  every non-tether anchor/ring pair has d² − 4 > 0 : {sepOk}  \
      (smallest {sepMin.shw 12})"
    -- frame criterion on all eight contacts
    let mut offOk := false
    let mut offBest : String := ""
    for i in [0:4] do
      for z in [ws[i]!.sub (siteI xs[i]!), ws[i]!.sub ws[(i+1) % 4]!] do
        let (re, im) := z6I z
        if I.pos re || I.isNeg re || I.pos im || I.isNeg im then
          if !offOk then
            offBest := s!"Re(z⁶)−64 ∈ {re.shw 9}, Im(z⁶) ∈ {im.shw 9}"
          offOk := true
    out := out.push s!"  off the lattice (some contact has z⁶ ≠ 64) : {offOk}   {offBest}"
    -- body clearance
    if body.size > 0 then
      let mut clearOk := true
      let mut worst : I := I.ofInt 1000
      let mut worstP : Site := (0, 0)
      for p in body do
        for i in [0:4] do
          if xs[i]! != p then
            let s := ws[i]!.d2 (siteI p) - I.ofInt 4
            if !I.pos s then clearOk := false
            if s.hi < worst.hi then worst := s; worstP := p
      out := out.push s!"  every body site other than its own anchor has d² − 4 > 0 : {clearOk} \
        (worst at {showSite worstP}: {worst.shw 12})"
      out := out.push s!"  body: {body.size} sites, {(contacts body).size} contacts, exact rank \
        {rigRank body} (2m−3 = {2 * body.size - 3})"
    out := out.push s!"  8×8 ring-relative rigidity matrix certified nonsingular : \
      {certNonsingular (ringMatrixI xs ws)}"
    return String.intercalate "\n" out.toList

end CaseB
