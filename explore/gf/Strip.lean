import Std.Data.HashMap
import Std.Data.HashSet
open Std

/-!
# Bounded-width rigid lattice sets: brute force, GF recheck, constructibility

Exploratory (plain Lean + Std, no Mathlib, no theorems). Site `(a,b)` is the point
`2a + b(1+i√3)`; two circles touch iff the difference of sites has `eNorm = 1`,
where `eNorm (x,y) = x² + xy + y²`.

Modes:
* `series N`    – expand the GFs `T3`, `V`, `R`, `H`, `C3` of `docs/formula-plan.md` §5, check
                  that the Burnside sum is divisible by 4, and check the published closed form
                  for `T3` against the rational form `N3/D3` recovered in `Transfer.lean`.
* `brute W N`   – brute force over `W`-row strips, `n ≤ N`: fixed counts, class counts, the
                  width filter, exact rank, flex certificates, second-order rigidity and
                  R1–R4 constructibility. Prunes on `|E| ≥ 2n−3`, which is valid for
                  *infinitesimal* rigidity only (see `certFlexible`).
* `bruteall W N`– the same without that prune, so the rigid (not merely infinitesimally rigid)
                  sets are all seen.
* `check FILE`  – read site lists (`(a,b),(a,b),…`, one set per line) and report, for each,
                  `|E|`, the exact rank, the generic (Laman) rank, the flex and stress
                  dimensions, the width, the peeled core, a verdict
                  (`INF-RIGID` / `FLEXIBLE` / `RIGID-SINGULAR` / `UNDECIDED`) and
                  constructibility under R1+R2, R1+R2+R4 and R1–R4.
* `rule3 N`     – test the published width-3 structural rule of §5 against the exact rank on
                  every connected 3-row set of minimum degree 2.
-/

namespace GF

/-! ## Power series over ℤ -/

def padTo (a : Array Int) (N : Nat) : Array Int := Id.run do
  let mut out : Array Int := #[]
  for i in [0:N+1] do
    out := out.push (if i < a.size then a[i]! else 0)
  return out

def sAdd (a b : Array Int) (N : Nat) : Array Int := Id.run do
  let a := padTo a N
  let b := padTo b N
  let mut out : Array Int := #[]
  for i in [0:N+1] do out := out.push (a[i]! + b[i]!)
  return out

def sSub (a b : Array Int) (N : Nat) : Array Int := Id.run do
  let a := padTo a N
  let b := padTo b N
  let mut out : Array Int := #[]
  for i in [0:N+1] do out := out.push (a[i]! - b[i]!)
  return out

def sMul (a b : Array Int) (N : Nat) : Array Int := Id.run do
  let a := padTo a N
  let b := padTo b N
  let mut out := Array.replicate (N+1) (0 : Int)
  for i in [0:N+1] do
    if a[i]! != 0 then
      for j in [0:N+1-i] do
        if b[j]! != 0 then out := out.set! (i+j) (out[i+j]! + a[i]! * b[j]!)
  return out

/-- series of `num / den` with `den[0] = 1`. -/
def sDiv (num den : Array Int) (N : Nat) : Array Int := Id.run do
  let num := padTo num N
  let den := padTo den N
  let mut q := Array.replicate (N+1) (0 : Int)
  for i in [0:N+1] do
    let mut s := num[i]!
    for j in [1:i+1] do
      s := s - den[j]! * q[i-j]!
    q := q.set! i s
  return q

def sScale (a : Array Int) (c : Int) : Array Int := a.map (c * ·)

/-- `x^k`. -/
def sX (k : Nat) : Array Int := Id.run do
  let mut out : Array Int := #[]
  for i in [0:k+1] do out := out.push (if i == k then 1 else 0)
  return out

def poly (cs : List Int) : Array Int := cs.toArray

/-! ## The §5 generating functions -/

/-- `T3 = x³(1+x)²(2+x+2x²+2x³+2x⁴−x⁵)/(1−x²−x³−x⁵) − 2x³ − 4x⁴/(1−x)` -/
def serT3 (N : Nat) : Array Int :=
  let onePx := poly [1, 1]
  let num := sMul (sMul (sX 3) (sMul onePx onePx N) N) (poly [2, 1, 2, 2, 2, -1]) N
  let den := poly [1, 0, -1, -1, 0, -1]
  let main := sDiv num den N
  let corr := sAdd (sScale (sX 3) 2) (sDiv (sScale (sX 4) 4) (poly [1, -1]) N) N
  sSub main corr N

/-- `V = (x⁴+x⁶+x⁷+3x⁹−2x¹⁰+4x¹¹−x¹²+2x¹³+x¹⁴−x¹⁵−x¹⁷)/((1−x²)(1−x⁴−x⁶−x¹⁰))` -/
def serV (N : Nat) : Array Int :=
  let num := poly [0,0,0,0, 1, 0, 1, 1, 0, 3, -2, 4, -1, 2, 1, -1, 0, -1]
  let den := sMul (poly [1,0,-1]) (poly [1,0,0,0,-1,0,-1,0,0,0,-1]) N
  sDiv num den N

/-- `R = (x⁴+2x⁶+x⁷+2x⁸+2x⁹+2x¹¹−x¹²−x¹⁵)/(1−x⁴−x⁶−x¹⁰)` -/
def serR (N : Nat) : Array Int :=
  let num := poly [0,0,0,0, 1, 0, 2, 1, 2, 2, 0, 2, -1, 0, 0, -1]
  let den := poly [1,0,0,0,-1,0,-1,0,0,0,-1]
  sDiv num den N

/-- `H = x⁴(1+x²)²/(1−x³)` -/
def serH (N : Nat) : Array Int :=
  let onePx2 := poly [1, 0, 1]
  sDiv (sMul (sX 4) (sMul onePx2 onePx2 N) N) (poly [1,0,0,-1]) N

/-- The form recovered from the transfer matrix: `T3 = N3/D3` with
`N3 = x⁴+3x⁵+5x⁶+3x⁷−x⁸−3x⁹−x¹⁰+x¹¹` and `D3 = 1−x−x²+x⁴−x⁵+x⁶ = (1−x)(1−x²−x³−x⁵)`. -/
def serT3rec (N : Nat) : Array Int :=
  sDiv (poly [0,0,0,0, 1, 3, 5, 3, -1, -3, -1, 1]) (poly [1,-1,-1,0,1,-1,1]) N

/-- `C3 = ¼(T3+V+R+H) − x⁴ − x⁵ − 2x⁶ − 2x⁷` -/
def serC3 (N : Nat) : Array Int := Id.run do
  let s := (serC3raw N).map (· / 4)
  let corr := sAdd (sAdd (sX 4) (sX 5) N) (sAdd (sScale (sX 6) 2) (sScale (sX 7) 2) N) N
  return sSub s corr N
where
  /-- `T3+V+R+H`, before dividing by 4. -/
  serC3raw (N : Nat) : Array Int :=
    sAdd (sAdd (serT3 N) (serV N) N) (sAdd (serR N) (serH N) N) N

/-- `T3+V+R+H`, to check divisibility by 4. -/
def serC3raw (N : Nat) : Array Int :=
  sAdd (sAdd (serT3 N) (serV N) N) (sAdd (serR N) (serH N) N) N

/-! ## Lattice basics -/

abbrev Pt := Int × Int

@[inline] def eNorm (x y : Int) : Int := x * x + x * y + y * y

structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Inhabited

@[inline] def M2.app (m : M2) (p : Pt) : Pt := (m.a * p.1 + m.b * p.2, m.c * p.1 + m.d * p.2)
def M2.mul (m n : M2) : M2 :=
  ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d, m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d⟩

def rotM : M2 := ⟨0, -1, 1, 1⟩
def refM : M2 := ⟨0, 1, 1, 0⟩

def syms : Array M2 := Id.run do
  let mut out : Array M2 := #[]
  let mut r : M2 := ⟨1, 0, 0, 1⟩
  for _ in [0:6] do
    out := out.push r
    out := out.push (r.mul refM)
    r := rotM.mul r
  return out

/-- Packed key after translating the bounding box to the origin. -/
def packKey (pts : Array Pt) : Nat := Id.run do
  let mut ma : Int := pts[0]!.1
  let mut mb : Int := pts[0]!.2
  for p in pts do
    if p.1 < ma then ma := p.1
    if p.2 < mb then mb := p.2
  let codes := (pts.map fun p => ((p.1 - ma) * 64 + (p.2 - mb)).toNat).qsort (· < ·)
  let mut k := 0
  for c in codes do k := k * 4096 + c
  return k

/-- Canonical key: minimum of `packKey` over the 12 lattice symmetries. -/
def canonKey (pts : Array Pt) : Nat := Id.run do
  let mut best := packKey pts
  for i in [1:12] do
    let k := packKey (pts.map (syms[i]!.app ·))
    if k < best then best := k
  return best

def contacts (pts : Array Pt) : Array (Nat × Nat) := Id.run do
  let mut es := #[]
  for i in [0:pts.size] do
    for j in [i+1:pts.size] do
      if eNorm (pts[i]!.1 - pts[j]!.1) (pts[i]!.2 - pts[j]!.2) == 1 then es := es.push (i, j)
  return es

/-- min over the three lattice directions of the span of the corresponding coordinate. -/
def minWidth (pts : Array Pt) : Nat := Id.run do
  let mut lo : Array Int := #[pts[0]!.1, pts[0]!.2, pts[0]!.1 + pts[0]!.2]
  let mut hi := lo
  for p in pts do
    let vs : Array Int := #[p.1, p.2, p.1 + p.2]
    for k in [0:3] do
      if vs[k]! < lo[k]! then lo := lo.set! k vs[k]!
      if vs[k]! > hi[k]! then hi := hi.set! k vs[k]!
  let mut best : Int := hi[0]! - lo[0]!
  for k in [1:3] do
    if hi[k]! - lo[k]! < best then best := hi[k]! - lo[k]!
  return (best + 1).toNat

/-! ## Rank of the rigidity matrix -/

def PR : Nat := 2147483647

def powMod (b0 e0 : Nat) : Nat := Id.run do
  let mut r := 1
  let mut b := b0 % PR
  let mut e := e0
  while e > 0 do
    if e % 2 == 1 then r := r * b % PR
    b := b * b % PR
    e := e / 2
  return r

def invMod (a : Nat) : Nat := powMod a (PR - 2)

def modRank (rows0 : Array (Array Nat)) (ncols : Nat) : Nat := Id.run do
  let mut M := rows0
  let m := M.size
  let mut r := 0
  for col in [0:ncols] do
    if r < m then
      let mut piv := m
      for i in [r:m] do
        if piv == m && M[i]![col]! != 0 then piv := i
      if piv < m then
        let rowP0 := M[piv]!
        M := M.set! piv M[r]!
        let inv := invMod rowP0[col]!
        let mut rowP := rowP0
        for j in [col:ncols] do
          rowP := rowP.set! j (rowP[j]! * inv % PR)
        M := M.set! r rowP
        for i in [r+1:m] do
          let rowI := M[i]!
          let f := rowI[col]!
          if f != 0 then
            let mut nr := rowI
            for j in [col:ncols] do
              nr := nr.set! j ((rowI[j]! + (PR - f) * rowP[j]!) % PR)
            M := M.set! i nr
        r := r + 1
  return r

/-- exact fraction-free rank over ℤ. -/
def intRank (rows : Array (Array Int)) (ncols : Nat) : Nat := Id.run do
  let mut M := rows
  let m := M.size
  let mut r := 0
  let mut prev : Int := 1
  for col in [0:ncols] do
    if r < m then
      let mut piv := m
      for i in [r:m] do
        if piv == m && M[i]![col]! != 0 then piv := i
      if piv < m then
        let rowP := M[piv]!
        M := M.set! piv M[r]!
        M := M.set! r rowP
        let pv := rowP[col]!
        for i in [r+1:m] do
          let rowI := M[i]!
          let f := rowI[col]!
          let mut nr := rowI
          for j in [0:ncols] do
            if j > col then
              nr := nr.set! j ((pv * rowI[j]! - f * rowP[j]!) / prev)
          nr := nr.set! col 0
          M := M.set! i nr
        prev := pv
        r := r + 1
  return r

@[inline] def toF (x : Int) : Nat := (if x < 0 then x + PR else x).toNat

/-- rank of the rigidity matrix in coordinates `(a,b)`, mod `PR`. -/
def rigRankMod (pts : Array Pt) (es : Array (Nat × Nat)) : Nat := Id.run do
  let n := pts.size
  let mut rows : Array (Array Nat) := #[]
  for (i, j) in es do
    let x := pts[i]!.1 - pts[j]!.1
    let y := pts[i]!.2 - pts[j]!.2
    let row := ((((Array.replicate (2*n) (0 : Nat)).set! (2*i) (toF x)).set! (2*i+1) (toF y)).set!
      (2*j) (toF (-x))).set! (2*j+1) (toF (-y))
    rows := rows.push row
  return modRank rows (2 * n)

def rigRankExact (pts : Array Pt) (es : Array (Nat × Nat)) : Nat := Id.run do
  let n := pts.size
  let mut rows : Array (Array Int) := #[]
  for (i, j) in es do
    let x := pts[i]!.1 - pts[j]!.1
    let y := pts[i]!.2 - pts[j]!.2
    let row := ((((Array.replicate (2*n) (0 : Int)).set! (2*i) x).set! (2*i+1) y).set!
      (2*j) (-x)).set! (2*j+1) (-y)
    rows := rows.push row
  return intRank rows (2 * n)

/-- `true` iff rank = 2n − 3 (checked mod `PR`, confirmed exactly when the mod-`PR` rank
is deficient). -/
def infRigid (pts : Array Pt) (es : Array (Nat × Nat)) : Bool :=
  let n := pts.size
  if n ≤ 1 then true
  else if rigRankMod pts es == 2 * n - 3 then true
  else rigRankExact pts es == 2 * n - 3

/-! ## R1–R4 constructibility -/

def pc (m : Nat) : Nat := Id.run do
  let mut c := 0
  let mut m := m
  while m > 0 do
    if m % 2 == 1 then c := c + 1
    m := m / 2
  return c

/-- drop masks contained in another mask. -/
def dedupMax (cs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:cs.size] do
    let x := cs[i]!
    let mut keep := true
    for j in [0:cs.size] do
      if keep && j != i then
        let y := cs[j]!
        if x &&& y == x && (x != y || j < i) then keep := false
    if keep then out := out.push x
  return out

/-- merge any two clusters sharing ≥ 2 circles, to saturation. -/
partial def satR1 (cs0 : Array Nat) : Array Nat := Id.run do
  let mut cs := dedupMax cs0
  let mut go := true
  while go do
    go := false
    let mut fi := cs.size
    let mut fj := cs.size
    for i in [0:cs.size] do
      if fi == cs.size then
        for j in [i+1:cs.size] do
          if fi == cs.size && pc (cs[i]! &&& cs[j]!) ≥ 2 then
            fi := i; fj := j
    if fi < cs.size then
      let u := cs[fi]! ||| cs[fj]!
      let mut nw : Array Nat := #[u]
      for k in [0:cs.size] do
        if k != fi && k != fj then nw := nw.push cs[k]!
      cs := dedupMax nw
      go := true
  return cs

/-- R2: three clusters with three distinct shared circles. Returns `none` if no merge fires. -/
def tryR2 (cs : Array Nat) : Option (Array Nat) := Id.run do
  for i in [0:cs.size] do
    for j in [i+1:cs.size] do
      let xij := cs[i]! &&& cs[j]!
      if xij != 0 then
        for k in [j+1:cs.size] do
          let xjk := cs[j]! &&& cs[k]!
          let xik := cs[i]! &&& cs[k]!
          if xjk != 0 && xik != 0 then
            -- after R1-saturation each pairwise intersection is a single circle
            if xij != xjk && xjk != xik && xij != xik then
              let u := cs[i]! ||| cs[j]! ||| cs[k]!
              let mut nw : Array Nat := #[u]
              for t in [0:cs.size] do
                if t != i && t != j && t != k then nw := nw.push cs[t]!
              return some (dedupMax nw)
  return none

/-- R3: `p, q` in one cluster, `q − p = k·u` with `k ≥ 2` and the whole straight run present. -/
def tryR3 (pts : Array Pt) (idxOf : Pt → Option Nat) (cs : Array Nat) : Option (Array Nat) :=
  Id.run do
  let dirs : Array Pt := #[(1,0), (0,1), (-1,1)]
  for ci in [0:cs.size] do
    let c := cs[ci]!
    for i in [0:pts.size] do
      if c &&& (1 <<< i) != 0 then
        for d in dirs do
          let mut chain := 1 <<< i
          let mut k := 1
          let mut cont := true
          while cont do
            let q : Pt := (pts[i]!.1 + d.1 * k, pts[i]!.2 + d.2 * k)
            match idxOf q with
            | none => cont := false
            | some jx =>
              chain := chain ||| (1 <<< jx)
              if k ≥ 2 && c &&& (1 <<< jx) != 0 && chain &&& c != chain then
                let u := c ||| chain
                let mut nw : Array Nat := #[u]
                for t in [0:cs.size] do
                  if t != ci then nw := nw.push cs[t]!
                return some (dedupMax nw)
              k := k + 1
              if k > 40 then cont := false
  return none

@[inline] def lineRow (p q : Pt) : Pt × Int := ((p.2 - q.2, q.1 - p.1), p.1 * q.2 - p.2 * q.1)

def det3 (r0 r1 r2 : Pt × Int) : Int :=
  let a := r0.1.1; let b := r0.1.2; let c := r0.2
  let d := r1.1.1; let e := r1.1.2; let f := r1.2
  let g := r2.1.1; let h := r2.1.2; let i := r2.2
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- R4: two clusters joined by three contacts whose homogeneous line rows are independent. -/
def tryR4 (pts : Array Pt) (es : Array (Nat × Nat)) (cs : Array Nat) : Option (Array Nat) :=
  Id.run do
  for i in [0:cs.size] do
    for j in [i+1:cs.size] do
      let A := cs[i]!
      let B := cs[j]!
      let mut rows : Array (Pt × Int) := #[]
      for (u, v) in es do
        let bu := 1 <<< u
        let bv := 1 <<< v
        if (A &&& bu != 0 && B &&& bv != 0) || (A &&& bv != 0 && B &&& bu != 0) then
          rows := rows.push (lineRow pts[u]! pts[v]!)
      if rows.size ≥ 3 then
        for p in [0:rows.size] do
          for q in [p+1:rows.size] do
            for r in [q+1:rows.size] do
              if det3 rows[p]! rows[q]! rows[r]! != 0 then
                let u := A ||| B
                let mut nw : Array Nat := #[u]
                for t in [0:cs.size] do
                  if t != i && t != j then nw := nw.push cs[t]!
                return some (dedupMax nw)
  return none

/-- which of R1..R4 to use. -/
structure Rules where
  r2 : Bool := true
  r3 : Bool := true
  r4 : Bool := true

/-- run the cluster calculus to a fixpoint; `true` iff some cluster is everything. -/
partial def constructible (pts : Array Pt) (es : Array (Nat × Nat)) (rl : Rules) : Bool :=
  Id.run do
  let n := pts.size
  let full := (1 <<< n) - 1
  let mut grid : HashMap Pt Nat := {}
  for i in [0:n] do grid := grid.insert pts[i]! i
  let idxOf : Pt → Option Nat := fun p => grid[p]?
  let mut cs : Array Nat := #[]
  for (u, v) in es do cs := cs.push ((1 <<< u) ||| (1 <<< v))
  cs := satR1 cs
  let mut go := true
  while go do
    if cs.any (· == full) then return true
    if cs.size == 1 then return cs[0]! == full
    go := false
    if rl.r3 then
      match tryR3 pts idxOf cs with
      | some nw => cs := satR1 nw; go := true
      | none => pure ()
    if !go && rl.r4 then
      match tryR4 pts es cs with
      | some nw => cs := satR1 nw; go := true
      | none => pure ()
    if !go && rl.r2 then
      match tryR2 cs with
      | some nw => cs := satR1 nw; go := true
      | none => pure ()
  return cs.any (· == full)

/-! ## Brute force over `W`-row strips -/

/-- degree table: `degOk W l c r` is true iff every site of column `c` has ≥ 2 neighbours,
given left column `l` and right column `r`. -/
def mkDegOk (W : Nat) : Array Bool := Id.run do
  let S := 1 <<< W
  let mut out := Array.replicate (S * S * S) false
  for l in [0:S] do
    for c in [0:S] do
      for r in [0:S] do
        let mut ok := true
        for b in [0:W] do
          if c &&& (1 <<< b) != 0 then
            let mut d := 0
            if b > 0 && c &&& (1 <<< (b-1)) != 0 then d := d + 1
            if b + 1 < W && c &&& (1 <<< (b+1)) != 0 then d := d + 1
            if l &&& (1 <<< b) != 0 then d := d + 1
            if b + 1 < W && l &&& (1 <<< (b+1)) != 0 then d := d + 1
            if r &&& (1 <<< b) != 0 then d := d + 1
            if b > 0 && r &&& (1 <<< (b-1)) != 0 then d := d + 1
            if d < 2 then ok := false
        out := out.set! ((l * S + c) * S + r) ok
  return out

def colsToPts (W : Nat) (cols : Array Nat) : Array Pt := Id.run do
  let mut out : Array Pt := #[]
  for a in [0:cols.size] do
    for b in [0:W] do
      if cols[a]! &&& (1 <<< b) != 0 then out := out.push (Int.ofNat a, Int.ofNat b)
  return out

def isConnected (pts : Array Pt) (es : Array (Nat × Nat)) : Bool := Id.run do
  let n := pts.size
  if n == 0 then return true
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for (i, j) in es do
    adj := adj.modify i (·.push j)
    adj := adj.modify j (·.push i)
  let mut seen := Array.replicate n false
  seen := seen.set! 0 true
  let mut st : Array Nat := #[0]
  let mut cnt := 1
  while st.size > 0 do
    let v := st.back!
    st := st.pop
    for w in adj[v]! do
      if !seen[w]! then
        seen := seen.set! w true
        cnt := cnt + 1
        st := st.push w
  return cnt == n

/-! ## Flex certificates (sound: each certifies a finite flex) -/

def dA : Array Int := #[1, 0, -1, -1, 0, 1]
def dB : Array Int := #[0, 1, 1, 0, -1, -1]

/-- a circle whose removal disconnects the contact graph (rotation flex). -/
def hasCutCircle (pts : Array Pt) (es : Array (Nat × Nat)) : Bool := Id.run do
  let n := pts.size
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for (i, j) in es do
    adj := adj.modify i (·.push j)
    adj := adj.modify j (·.push i)
  for v in [0:n] do
    let start := if v == 0 then 1 else 0
    let mut seen := Array.replicate n false
    seen := seen.set! v true
    seen := seen.set! start true
    let mut stack := #[start]
    let mut cnt := 1
    while !stack.isEmpty do
      let u := stack.back!
      stack := stack.pop
      for w in adj[u]! do
        if !seen[w]! then
          seen := seen.set! w true
          cnt := cnt + 1
          stack := stack.push w
    if cnt < n - 1 then return true
  return false

/-- shear flex: for some unit vector `u`, a nonempty proper set `S` with every contact across
the cut parallel to `u` and oriented the same way. -/
def hasShear (pts : Array Pt) (es : Array (Nat × Nat)) : Bool := Id.run do
  let n := pts.size
  if n < 3 then return false
  for k in [0:3] do
    let mut out : Array (Array Nat) := Array.replicate n #[]
    let mut inn : Array (Array Nat) := Array.replicate n #[]
    for (i, j) in es do
      let x := pts[j]!.1 - pts[i]!.1
      let y := pts[j]!.2 - pts[i]!.2
      if x == dA[k]! && y == dB[k]! then
        out := out.modify i (·.push j); inn := inn.modify j (·.push i)
      else if x == -dA[k]! && y == -dB[k]! then
        out := out.modify j (·.push i); inn := inn.modify i (·.push j)
      else
        out := (out.modify i (·.push j)).modify j (·.push i)
        inn := (inn.modify i (·.push j)).modify j (·.push i)
    for g in [out, inn] do
      let mut seen := (Array.replicate n false).set! 0 true
      let mut stack := #[0]
      let mut cnt := 1
      while !stack.isEmpty do
        let u := stack.back!
        stack := stack.pop
        for w in g[u]! do
          if !seen[w]! then
            seen := seen.set! w true; cnt := cnt + 1; stack := stack.push w
      if cnt < n then return true
  return false

/-- `balTab W` at `(l, m)` is `Σ_{b ∈ m} (#backward neighbours of (a,b) − 2)`, where the
backward neighbours of `(a,b)` are `(a−1,b)`, `(a−1,b+1)` (in `l`) and `(a,b−1)` (in `m`).
Summed over the whole set this is `|E| − 2n`, and every future site contributes at most `+1`. -/
def mkBalTab (W : Nat) : Array Int := Id.run do
  let S := 1 <<< W
  let mut out := Array.replicate (S * S) (0 : Int)
  for l in [0:S] do
    for m in [0:S] do
      let mut s : Int := 0
      for b in [0:W] do
        if m &&& (1 <<< b) != 0 then
          let mut d : Int := 0
          if l &&& (1 <<< b) != 0 then d := d + 1
          if b + 1 < W && l &&& (1 <<< (b+1)) != 0 then d := d + 1
          if b > 0 && m &&& (1 <<< (b-1)) != 0 then d := d + 1
          s := s + d - 2
      out := out.set! (l * S + m) s
  return out

/-- Peel removable circles (degree exactly 2, the two neighbours not opposite). Peeling is an
equivalence for rigidity: the peeled set is rigid iff the original is.

Returns `(verdict, core)`: `verdict = some false` when some stage has a circle of degree ≤ 1
with ≥ 3 circles left (a rotation/translation flex), `some true` when peeling reaches ≤ 2
circles, `none` when it stops at a genuine core. -/
partial def peelCore (pts0 : Array Pt) : Option Bool × Array Pt := Id.run do
  let mut pts := pts0
  let mut go := true
  while go do
    go := false
    let n := pts.size
    if n ≤ 2 then return (some true, pts)
    let es := contacts pts
    let mut deg := Array.replicate n 0
    let mut nb : Array (Array Nat) := Array.replicate n #[]
    for (i, j) in es do
      deg := deg.modify i (· + 1); deg := deg.modify j (· + 1)
      nb := nb.modify i (·.push j); nb := nb.modify j (·.push i)
    let mut drop := n
    for i in [0:n] do
      if deg[i]! ≤ 1 then return (some false, pts)
      if drop == n && deg[i]! == 2 then
        let u := pts[nb[i]![0]!]!
        let v := pts[nb[i]![1]!]!
        -- opposite ⟺ the two neighbours are 4 apart ⟺ eNorm (u−v) = 4
        if eNorm (u.1 - v.1) (u.2 - v.2) != 4 then drop := i
    if drop < n then
      let mut out : Array Pt := #[]
      for i in [0:n] do
        if i != drop then out := out.push pts[i]!
      pts := out
      go := true
  return (none, pts)

/-! ## Second-order rigidity (a sufficient condition for rigidity)

Velocities are written in the lattice basis, so the Euclidean inner product becomes the Gram
form `G = [[4,2],[2,4]]` and `|v|² = 4·eNorm v`. The rigidity matrix therefore carries the rows
`G·d` (dropping a factor 2: `(2x+y, x+2y)`), and the infinitesimal rotation about the origin is
`u_i = A·p_i` with `A = [[-1,-2],[2,1]]` (`= √3` times the real rotation generator).

For a self-stress `ω` put `Q_ω(u) = Σ_e ω_e |u_i − u_j|²`. Then `Σ_e ω_e l_e² = 0` and the
cross term with a rotation vanishes, so `Q_ω` is a well-defined quadratic form on
`flexes / trivial`. Connelly's criterion: if some `Q_ω` is definite there, the framework is
second-order rigid, hence rigid. -/

def rrefQ (M0 : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) × Array Nat := Id.run do
  let mut M := M0
  let m := M.size
  let mut r := 0
  let mut piv : Array Nat := #[]
  for col in [0:ncols] do
    if r < m then
      let mut p := m
      for i in [r:m] do
        if p == m && M[i]![col]! != 0 then p := i
      if p < m then
        let rowP0 := M[p]!
        M := M.set! p M[r]!
        let c := rowP0[col]!
        let rowP := rowP0.map (· / c)
        M := M.set! r rowP
        for i in [0:m] do
          if i != r then
            let f := M[i]![col]!
            if f != 0 then
              let mut nr := M[i]!
              for j in [0:ncols] do nr := nr.set! j (nr[j]! - f * rowP[j]!)
              M := M.set! i nr
        piv := piv.push col
        r := r + 1
  return (M.extract 0 r, piv)

def kernelQ (M : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let (R, piv) := rrefQ M ncols
  let mut isPiv := Array.replicate ncols false
  for c in piv do isPiv := isPiv.set! c true
  let mut out : Array (Array Rat) := #[]
  for c in [0:ncols] do
    if !isPiv[c]! then
      let mut v := Array.replicate ncols (0 : Rat)
      v := v.set! c 1
      for i in [0:R.size] do v := v.set! piv[i]! (-R[i]![c]!)
      out := out.push v
  return out

/-- rigidity matrix over ℚ, rows `G·d`, in lattice velocity coordinates. -/
def rigMatQ (pts : Array Pt) (es : Array (Nat × Nat)) : Array (Array Rat) := Id.run do
  let n := pts.size
  let mut rows : Array (Array Rat) := #[]
  for (i, j) in es do
    let x := pts[i]!.1 - pts[j]!.1
    let y := pts[i]!.2 - pts[j]!.2
    let c1 : Rat := Rat.ofInt (2 * x + y)
    let c2 : Rat := Rat.ofInt (x + 2 * y)
    let row := ((((Array.replicate (2*n) (0 : Rat)).set! (2*i) c1).set! (2*i+1) c2).set!
      (2*j) (-c1)).set! (2*j+1) (-c2)
    rows := rows.push row
  return rows

def transposeM (M : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let mut out : Array (Array Rat) := #[]
  for j in [0:ncols] do
    let mut v : Array Rat := #[]
    for i in [0:M.size] do v := v.push M[i]![j]!
    out := out.push v
  return out

/-- `2·B(d, d')` for the Gram form, so that `2·B(d,d) = 2·eNorm d`. -/
@[inline] def bil (xa xb ya yb : Rat) : Rat := 2 * xa * ya + xa * yb + xb * ya + 2 * xb * yb

/-- Second-order rigidity: `true` certifies the framework is rigid. -/
def secondOrderRigid (pts : Array Pt) (es : Array (Nat × Nat)) : Bool := Id.run do
  let n := pts.size
  if n < 3 then return true
  let M := rigMatQ pts es
  let flex := kernelQ M (2 * n)
  let stress := kernelQ (transposeM M (2 * n)) es.size
  if stress.isEmpty then return false
  -- trivial motions: two translations and the rotation `u_i = A p_i`
  let mut triv : Array (Array Rat) := #[]
  let mut t1 := Array.replicate (2*n) (0 : Rat)
  let mut t2 := Array.replicate (2*n) (0 : Rat)
  let mut t3 := Array.replicate (2*n) (0 : Rat)
  for i in [0:n] do
    t1 := t1.set! (2*i) 1
    t2 := t2.set! (2*i+1) 1
    t3 := t3.set! (2*i) (Rat.ofInt (-pts[i]!.1 - 2 * pts[i]!.2))
    t3 := t3.set! (2*i+1) (Rat.ofInt (2 * pts[i]!.1 + pts[i]!.2))
  triv := #[t1, t2, t3]
  -- complement of the trivial motions inside the flex space
  let mut basis := triv
  let mut rk := (rrefQ triv (2*n)).1.size
  let mut gauged : Array (Array Rat) := #[]
  for f in flex do
    let cand := basis.push f
    let r := (rrefQ cand (2*n)).1.size
    if r > rk then
      basis := cand
      rk := r
      gauged := gauged.push f
  let g := gauged.size
  if g == 0 then return true    -- infinitesimally rigid
  -- the quadratic forms `Q_ω` on the complement
  let formOf (w : Array Rat) : Array (Array Rat) := Id.run do
    let mut Qm : Array (Array Rat) := #[]
    for s in [0:g] do
      let mut row : Array Rat := #[]
      for t in [0:g] do
        let mut acc : Rat := 0
        for e in [0:es.size] do
          if w[e]! != 0 then
            let (i, j) := es[e]!
            acc := acc + w[e]! * bil (gauged[s]![2*i]! - gauged[s]![2*j]!)
              (gauged[s]![2*i+1]! - gauged[s]![2*j+1]!)
              (gauged[t]![2*i]! - gauged[t]![2*j]!)
              (gauged[t]![2*i+1]! - gauged[t]![2*j+1]!)
        row := row.push acc
      Qm := Qm.push row
    return Qm
  -- definite?  (all leading principal minors of `Qm` or of `−Qm` positive)
  let definite (Qm : Array (Array Rat)) : Bool := Id.run do
    for sgn in [0, 1] do
      let A := if sgn == 0 then Qm else Qm.map (·.map (-·))
      let mut ok := true
      for k in [1:g+1] do
        -- determinant of the top-left `k × k` block by fraction-free elimination
        let mut B : Array (Array Rat) := #[]
        for i in [0:k] do B := B.push (A[i]!.extract 0 k)
        let mut det : Rat := 1
        let mut r := 0
        for col in [0:k] do
          let mut p := k
          for i in [r:k] do
            if p == k && B[i]![col]! != 0 then p := i
          if p == k then det := 0
          else
            if p != r then
              let tmp := B[p]!
              B := B.set! p B[r]!
              B := B.set! r tmp
              det := -det
            det := det * B[r]![col]!
            let pv := B[r]![col]!
            for i in [r+1:k] do
              let f := B[i]![col]! / pv
              if f != 0 then
                let mut nr := B[i]!
                for j in [0:k] do nr := nr.set! j (nr[j]! - f * B[r]![j]!)
                B := B.set! i nr
            r := r + 1
        if det ≤ 0 then ok := false
      if ok then return true
    return false
  -- try each stress, and small combinations of pairs
  for w in stress do
    if definite (formOf w) then return true
  for a in [0:stress.size] do
    for b in [a+1:stress.size] do
      for c in [(-2 : Int), -1, 1, 2] do
        let mut w : Array Rat := #[]
        for e in [0:es.size] do
          w := w.push (stress[a]![e]! + Rat.ofInt c * stress[b]![e]!)
        if definite (formOf w) then return true
  return false

/-- Rank of the generic 2-dimensional rigidity matroid of the contact graph, by the
`(2,3)`-pebble game. If this is `< 2n − 3` the graph is not generically rigid, so the image of
the edge-length map has dimension `< 2n − 3`; every fibre then has dimension `> 3`, and the set
is flexible in *every* realization. -/
def genericRank (n : Nat) (es : Array (Nat × Nat)) : Nat := Id.run do
  let mut out : Array (Array Nat) := Array.replicate n #[]
  let mut peb := Array.replicate n 2
  let mut rank := 0
  for (u, v) in es do
    -- gather two free pebbles on each endpoint, never robbing the other endpoint
    for (a, b) in [(u, v), (v, u)] do
      let mut go := true
      while go && peb[a]! < 2 do
        let mut par := Array.replicate n n
        let mut seen := Array.replicate n false
        seen := seen.set! a true
        seen := seen.set! b true
        let mut q : Array Nat := #[a]
        let mut qi := 0
        let mut found := n
        while qi < q.size && found == n do
          let x := q[qi]!
          qi := qi + 1
          if peb[x]! > 0 && x != a then found := x
          else
            for y in out[x]! do
              if !seen[y]! then
                seen := seen.set! y true
                par := par.set! y x
                q := q.push y
        if found == n then go := false
        else
          let mut cur := found
          while cur != a do
            let p := par[cur]!
            out := out.modify p (fun arr => arr.filter (· != cur))
            out := out.modify cur (·.push p)
            cur := p
          peb := peb.modify found (· - 1)
          peb := peb.modify a (· + 1)
    if peb[u]! == 2 && peb[v]! == 2 then
      peb := peb.set! u 1
      out := out.modify u (·.push v)
      rank := rank + 1
  return rank

/-- an edge cut of size ≤ 2 with ≥ 2 circles on each side: two parts with `3 + 3` degrees of
freedom and only two bars between them leave a `4`-dimensional realization space, so the set is
flexible. -/
def hasSmallEdgeCut (pts : Array Pt) (es : Array (Nat × Nat)) : Bool := Id.run do
  let n := pts.size
  let comps (skip1 skip2 : Nat) : Nat := Id.run do
    let mut adj : Array (Array Nat) := Array.replicate n #[]
    for e in [0:es.size] do
      if e != skip1 && e != skip2 then
        let (i, j) := es[e]!
        adj := adj.modify i (·.push j)
        adj := adj.modify j (·.push i)
    let mut seen := Array.replicate n false
    seen := seen.set! 0 true
    let mut st : Array Nat := #[0]
    let mut cnt := 1
    while st.size > 0 do
      let v := st.back!
      st := st.pop
      for w in adj[v]! do
        if !seen[w]! then
          seen := seen.set! w true
          cnt := cnt + 1
          st := st.push w
    return cnt
  for e1 in [0:es.size] do
    for e2 in [e1:es.size] do
      let c := comps e1 e2
      if c ≥ 2 && n - c ≥ 2 then return true
  return false

/-- `true` when the set is certified flexible. Only certificates that exhibit an explicit
finite flex are used: a cut circle (rotate one side), a shear (translate one side along the
circle of admissible shifts), and peeling to a circle of degree ≤ 1.

`genericRank < 2n−3` and a small edge cut are deliberately NOT used: both are dimension counts
that fail over ℝ. A straight chain of `k` contacts between two circles exactly `2k` apart is
rigid although it is generically underbraced, so rigid lattice sets with `|E| = 2n−4` exist
(see the report). -/
def certFlexible (pts : Array Pt) (es : Array (Nat × Nat)) : Bool := Id.run do
  -- No self-stress and `|E| < 2n−3`: the rows of the rigidity matrix are independent, so the
  -- edge-length map is a submersion at `p` and its fibre is a smooth manifold of dimension
  -- `2n − |E| > 3` near `p`. (A rank equal to `|E|` modulo one prime already forces it over ℚ.)
  if es.size + 3 < 2 * pts.size && rigRankMod pts es == es.size then return true
  if hasCutCircle pts es || hasShear pts es then return true
  let (v, core) := peelCore pts
  match v with
  | some false => return true
  | some true => return false
  | none =>
    if core.size == pts.size then return false
    let ces := contacts core
    return hasCutCircle core ces || hasShear core ces

structure Stat where
  leaves : Nat := 0           -- degree- and balance-pruned complete column sequences
  cand : Nat := 0             -- connected, all rows used, |E| ≥ 2n−3
  ir : Nat := 0               -- infinitesimally rigid (fixed count)
  irMin : Nat := 0            -- infinitesimally rigid AND minWidth = W (fixed count)
  nir : Nat := 0              -- candidates that are NOT infinitesimally rigid
  nirFlex : Nat := 0          -- of those, certified flexible
  nirSOR : Nat := 0           -- of those, certified rigid at second order (singular rigid)
  deriving Inhabited

/-- Brute force: all column-mask sequences of total size `n` in `W` rows. -/
def bruteN (W n : Nat) (degOk : Array Bool) (balTab : Array Int) (usePrune : Bool) :
    Stat × HashMap Nat (Array Pt) × Array (Array Pt) × HashMap Nat (Array Pt) := Id.run do
  let S := 1 <<< W
  let full := S - 1
  let mut st : Stat := {}
  let mut reps : HashMap Nat (Array Pt) := {}   -- canonical key ↦ representative
  let mut nirs : Array (Array Pt) := #[]        -- NIR, neither certified flexible nor rigid
  let mut sing : HashMap Nat (Array Pt) := {}   -- NIR but second-order rigid
  let mut stack : Array (Array Nat × Nat × Int) := #[]
  for m in [1:S] do
    let p := pc m
    let b := balTab[0 * S + m]!
    if p ≤ n && (!usePrune || b + Int.ofNat (n - p) ≥ -3) then
      stack := stack.push (#[m], p, b)
  while stack.size > 0 do
    let (cols, placed, bal) := stack.back!
    stack := stack.pop
    let k := cols.size
    let l := if k ≥ 2 then cols[k-2]! else 0
    let c := cols[k-1]!
    if placed == n && degOk[(l * S + c) * S + 0]! && (!usePrune || bal ≥ -3) then
      st := { st with leaves := st.leaves + 1 }
      let mut u := 0
      for m in cols do u := u ||| m
      if u == full then
        let pts := colsToPts W cols
        let es := contacts pts
        if (!usePrune || es.size + 3 ≥ 2 * n) && isConnected pts es then
          st := { st with cand := st.cand + 1 }
          if infRigid pts es then
            st := { st with ir := st.ir + 1 }
            if minWidth pts == W then st := { st with irMin := st.irMin + 1 }
            let key := canonKey pts
            if !reps.contains key then reps := reps.insert key pts
          else
            st := { st with nir := st.nir + 1 }
            if certFlexible pts es then
              st := { st with nirFlex := st.nirFlex + 1 }
            else if secondOrderRigid pts es then
              st := { st with nirSOR := st.nirSOR + 1 }
              let key := canonKey pts
              if !sing.contains key then sing := sing.insert key pts
            else
              nirs := nirs.push pts
    if placed < n then
      for m in [1:S] do
        let p := pc m
        if placed + p ≤ n && degOk[(l * S + c) * S + m]! then
          let b := bal + balTab[c * S + m]!
          if !usePrune || b + Int.ofNat (n - placed - p) ≥ -3 then
            stack := stack.push (cols.push m, placed + p, b)
  return (st, reps, nirs, sing)

def showPts (pts : Array Pt) : String :=
  String.intercalate "," (pts.toList.map fun p => s!"({p.1},{p.2})")

def bruteMode (W maxN : Nat) (usePrune : Bool) : IO Unit := do
  let degOk := mkDegOk W
  let balTab := mkBalTab W
  IO.println s!"# brute force, W = {W} rows, |E| ≥ 2n−3 prune = {usePrune}"
  IO.println "n fixedIR fixedIRminW classesBspan classesMinW cand NIR NIRflex NIRsor leaves \
emg12 emg124 emg1234 ms"
  for n in [3:maxN+1] do
    let t0 ← IO.monoMsNow
    let (st, reps, nirs, sing) := bruteN W n degOk balTab usePrune
    let mut cMin := 0
    let mut e12 : Array (Array Pt) := #[]
    let mut e124 : Array (Array Pt) := #[]
    let mut e1234 : Array (Array Pt) := #[]
    for (_, pts) in reps do
      let isMin := minWidth pts == W
      if isMin then cMin := cMin + 1
      let es := contacts pts
      if !constructible pts es { r3 := false, r4 := false } then e12 := e12.push pts
      if !constructible pts es { r3 := false } then e124 := e124.push pts
      if !constructible pts es {} then e1234 := e1234.push pts
    let t1 ← IO.monoMsNow
    IO.println s!"{n} {st.ir} {st.irMin} {reps.size} {cMin} {st.cand} {st.nir} {st.nirFlex} \
{st.nirSOR} {st.leaves} {e12.size} {e124.size} {e1234.size} {t1 - t0}"
    for (_, p) in sing do
      IO.println s!"  SINGULAR-RIGID n={n} minW={minWidth p} {showPts p}"
    for p in e12 do
      IO.println s!"  EMERGENT-R12 n={n} minW={minWidth p} {showPts p}"
    for p in nirs do
      IO.println s!"  NIR-UNCERTIFIED n={n} {showPts p}"
    for p in e1234 do
      IO.println s!"  EMERGENT-R1234 n={n} minW={minWidth p} {showPts p}"
    for p in e124 do
      IO.println s!"  EMERGENT-R124 n={n} minW={minWidth p} {showPts p}"

/-! ## The published width-3 structural rule

`docs/formula-plan.md` §5: a set in rows 0–2 that uses all three rows is rigid iff, after
translation,

* row 1 is `m ≥ 2` consecutive circles;
* every interior slot of rows 0 and 2 is used, and consecutive interior slots share a row;
* an end slot is used only next to a used interior slot in the same row.

Reading: with row 1 = columns `0 … m−1`, a row-0 circle `(a,0)` touches row 1 at columns `a`
and `a−1`, so it is *interior* for `1 ≤ a ≤ m−1` and an *end slot* at `a = 0` and `a = m`.
A row-2 circle `(a,2)` touches row 1 at columns `a` and `a+1`, so it is interior for
`0 ≤ a ≤ m−2` and an end slot at `a = −1` and `a = m−1`. Interior slot `i` (`1 ≤ i ≤ m−1`)
is the pair (row 0 at column `i`, row 2 at column `i−1`). "Every interior slot is used" is
read as "at least one of each pair", and "consecutive interior slots share a row" as
"the used sets at `i` and `i+1` meet in a row". -/
def rule3 (cols : Array Nat) : Bool := Id.run do
  let L := cols.size
  let has (a b : Nat) : Bool := a < L && cols[a]! &&& (1 <<< b) != 0
  -- row 1 must be a nonempty run of `m ≥ 2` consecutive columns
  let mut lo := L
  let mut hi := L
  for a in [0:L] do
    if has a 1 then
      if lo == L then lo := a
      hi := a
  if lo == L then return false
  for a in [lo:hi+1] do
    if !has a 1 then return false
  let m := hi + 1 - lo
  if m < 2 then return false
  -- every site must sit in one of the allowed slots
  for a in [0:L] do
    if has a 0 && !(lo ≤ a && a ≤ lo + m) then return false
    if has a 2 && !(a + 1 ≥ lo && a + 1 ≤ lo + m) then return false
  -- interior slots
  let mut prev0 := false
  let mut prev2 := false
  for i in [1:m] do
    let u0 := has (lo + i) 0
    let u2 := has (lo + i - 1) 2
    if !u0 && !u2 then return false
    if i ≥ 2 then
      if !((u0 && prev0) || (u2 && prev2)) then return false
    prev0 := u0
    prev2 := u2
  -- end slots
  if has lo 0 && !(m ≥ 2 && has (lo + 1) 0) then return false
  if has (lo + m) 0 && !(m ≥ 2 && has (lo + m - 1) 0) then return false
  if lo ≥ 1 && has (lo - 1) 2 && !(m ≥ 2 && has lo 2) then return false
  if has (lo + m - 1) 2 && !(m ≥ 2 && has (lo + m - 2) 2) then return false
  return true

/-- Test `rule3` against the exact rank on every connected 3-row set with minimum degree 2. -/
def rule3Mode (maxN : Nat) : IO Unit := do
  let degOk := mkDegOk 3
  IO.println "n sets ruleYes irYes ruleNotIR irNotRule"
  for n in [3:maxN+1] do
    let mut sets := 0
    let mut ry := 0
    let mut iy := 0
    let mut bad1 : Array (Array Nat) := #[]
    let mut bad2 : Array (Array Nat) := #[]
    let mut stack : Array (Array Nat × Nat) := #[]
    for m in [1:8] do
      if pc m ≤ n then stack := stack.push (#[m], pc m)
    while stack.size > 0 do
      let (cols, placed) := stack.back!
      stack := stack.pop
      let k := cols.size
      let l := if k ≥ 2 then cols[k-2]! else 0
      let c := cols[k-1]!
      if placed == n && degOk[(l * 8 + c) * 8 + 0]! then
        let mut u := 0
        for m in cols do u := u ||| m
        if u == 7 then
          let pts := colsToPts 3 cols
          let es := contacts pts
          if isConnected pts es then
            sets := sets + 1
            let r := rule3 cols
            let i := infRigid pts es
            if r then ry := ry + 1
            if i then iy := iy + 1
            if r && !i then bad1 := bad1.push cols
            if i && !r then bad2 := bad2.push cols
      if placed < n then
        for m in [1:8] do
          if placed + pc m ≤ n && degOk[(l * 8 + c) * 8 + m]! then
            stack := stack.push (cols.push m, placed + pc m)
    IO.println s!"{n} {sets} {ry} {iy} {bad1.size} {bad2.size}"
    for cols in bad1 do IO.println s!"  RULE-NOT-RIGID {showPts (colsToPts 3 cols)}"
    for cols in bad2 do IO.println s!"  RIGID-NOT-RULE {showPts (colsToPts 3 cols)}"

def seriesMode (N : Nat) : IO Unit := do
  let t3 := serT3 N
  let v := serV N
  let r := serR N
  let h := serH N
  let raw := serC3raw N
  let c3 := serC3 N
  IO.println "n T3 V R H sum4 C3"
  for n in [3:N+1] do
    IO.println s!"{n} {t3[n]!} {v[n]!} {r[n]!} {h[n]!} {raw[n]!} {c3[n]!}"
  let bad := (List.range (N+1)).filter fun n => raw[n]! % 4 != 0
  IO.println s!"indices where the Burnside sum is not divisible by 4: {bad}"
  -- is `(1−x)(1−x²−x³−x⁵)` really `1−x−x²+x⁴−x⁵+x⁶`?
  let prod := sMul (poly [1,-1]) (poly [1,0,-1,-1,0,-1]) 6
  IO.println s!"(1-x)(1-x^2-x^3-x^5) = {prod.toList}"
  -- does the recovered rational form agree with the published closed form?
  let rec3 := serT3rec N
  let diff := (List.range (N+1)).filter fun n => rec3[n]! != t3[n]!
  IO.println s!"T3 published form vs N3/D3: disagreeing indices (n ≤ {N}): {diff}"

/-- parse a line like `(a,b),(a,b),…` by picking out the signed integers in order. -/
def parsePts (line : String) : Array Pt := Id.run do
  let mut nums : Array Int := #[]
  let mut cur : Int := 0
  let mut neg := false
  let mut inNum := false
  for ch in line.toList do
    if ch.isDigit then
      inNum := true
      cur := cur * 10 + Int.ofNat (ch.toNat - 48)
    else if ch == '-' then
      neg := true
    else
      if inNum then
        nums := nums.push (if neg then -cur else cur)
      cur := 0; neg := false; inNum := false
  if inNum then nums := nums.push (if neg then -cur else cur)
  let mut out : Array Pt := #[]
  let mut i := 0
  while i + 1 < nums.size do
    out := out.push (nums[i]!, nums[i+1]!)
    i := i + 2
  return out

def checkMode (file : String) : IO Unit := do
  let txt ← IO.FS.readFile file
  for line in txt.splitOn "\n" do
    let pts := parsePts line
    if pts.size ≥ 3 then
      let es := contacts pts
      let n := pts.size
      let rk := rigRankExact pts es
      let ir := rk == 2 * n - 3
      let (pv, core) := peelCore pts
      let cf := certFlexible pts es
      let sor := secondOrderRigid pts es
      let verdict :=
        if ir then "INF-RIGID" else if cf then "FLEXIBLE" else if sor then "RIGID-SINGULAR"
        else "UNDECIDED"
      let M := rigMatQ pts es
      let fdim := (kernelQ M (2*n)).size - 3
      let sdim := (kernelQ (transposeM M (2*n)) es.size).size
      IO.println s!"n={n} |E|={es.size} rank={rk} 2n-3={2*n-3} generic={genericRank n es} \
flexdim={fdim} stressdim={sdim} minW={minWidth pts} core={core.size} peel={pv} \
key={canonKey pts} {verdict}"
      do
        let c12 := constructible pts es { r3 := false, r4 := false }
        let c124 := constructible pts es { r3 := false }
        let c1234 := constructible pts es {}
        IO.println s!"   constructible: R12={c12} R124={c124} R1234={c1234}"

def main (args : List String) : IO Unit := do
  match args with
  | ["series", n] => seriesMode (n.toNat!)
  | ["brute", w, n] => bruteMode (w.toNat!) (n.toNat!) true
  | ["bruteall", w, n] => bruteMode (w.toNat!) (n.toNat!) false
  | ["check", f] => checkMode f
  | ["rule3", n] => rule3Mode (n.toNat!)
  | _ => IO.println "usage: series N | brute W N | bruteall W N | check FILE"

end GF

def main (args : List String) : IO Unit := GF.main args
