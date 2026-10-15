import Std.Data.HashMap
import Std.Data.HashSet
open Std

/-!
# Exact real quadratic towers

`K_0 = ℚ`, `K_{j+1} = K_j(√r_j)` with `r_j ∈ K_j`, `r_j > 0`. An element of level `k` is a tree:
`q c` (a rational, valid at every level) or `e a b = a + b √r_{k-1}` with `a b` of level `k-1`.
Signs are decided exactly (`tSign`), which is correct for real numbers whether or not the tower is
a field. `tInv` and `tSqrt?` need the tower to be a field (every radicand a non-square at its
level); `pushRad` guarantees that by testing `tSqrt?` before extending.
-/

namespace OL

inductive TN where
  | q : Rat → TN
  | e : TN → TN → TN
  deriving Inhabited, Repr, BEq

def TN.zero : TN := .q 0
def TN.one : TN := .q 1

def tAdd : Nat → TN → TN → TN
  | _, .q a, .q b => .q (a + b)
  | k+1, .e a b, .e c d => .e (tAdd k a c) (tAdd k b d)
  | k+1, .q a, .e c d => .e (tAdd k (.q a) c) d
  | k+1, .e a b, .q c => .e (tAdd k a (.q c)) b
  | 0, _, _ => .q 0

def tNeg : TN → TN
  | .q a => .q (-a)
  | .e a b => .e (tNeg a) (tNeg b)

def tSub (k : Nat) (x y : TN) : TN := tAdd k x (tNeg y)

def tScale (c : Rat) : TN → TN
  | .q a => .q (c * a)
  | .e a b => .e (tScale c a) (tScale c b)

/-- multiplication at level `k`; `rad[j]` is the radicand of level `j+1`. -/
def tMul (rad : Array TN) : Nat → TN → TN → TN
  | _, .q a, y => tScale a y
  | _, x, .q b => tScale b x
  | k+1, .e a b, .e c d =>
      let r := rad[k]!
      .e (tAdd k (tMul rad k a c) (tMul rad k (tMul rad k b d) r))
         (tAdd k (tMul rad k a d) (tMul rad k b c))
  | 0, _, _ => .q 0

def ratSign (a : Rat) : Int := if a > 0 then 1 else if a < 0 then -1 else 0

/-- exact sign (correct for the real value with positive square roots). -/
def tSign (rad : Array TN) : Nat → TN → Int
  | _, .q a => ratSign a
  | k+1, .e a b =>
      let sa := tSign rad k a
      let sb := tSign rad k b
      if sb == 0 then sa else if sa == 0 then sb else if sa == sb then sa
      else
        let t := tSub k (tMul rad k a a) (tMul rad k (tMul rad k b b) rad[k]!)
        sa * tSign rad k t
  | 0, _ => 0

def tIsZero (rad : Array TN) (k : Nat) (x : TN) : Bool := tSign rad k x == 0

def ratF (a : Rat) : Float :=
  let n := Float.ofInt a.num
  n / Float.ofNat a.den

def tFl (sq : Array Float) : Nat → TN → Float
  | _, .q a => ratF a
  | k+1, .e a b => tFl sq k a + tFl sq k b * sq[k]!
  | 0, .e _ _ => 0

/-- inverse at level `k` (tower must be a field). -/
def tInv (rad : Array TN) : Nat → TN → TN
  | _, .q a => .q a⁻¹
  | k+1, .e a b =>
      let n := tSub k (tMul rad k a a) (tMul rad k (tMul rad k b b) rad[k]!)
      let ni := tInv rad k n
      .e (tMul rad k a ni) (tNeg (tMul rad k b ni))
  | 0, _ => .q 0

def tDiv (rad : Array TN) (k : Nat) (x y : TN) : TN := tMul rad k x (tInv rad k y)

def natSqrt? (n : Nat) : Option Nat :=
  let s := n.sqrt
  if s * s == n then some s else none

def ratSqrt? (a : Rat) : Option Rat :=
  if a < 0 then none else
  match natSqrt? a.num.natAbs, natSqrt? a.den with
  | some s, some t => some ((s : Rat) / (t : Rat))
  | _, _ => none

/-- `some y` with `y ≥ 0`, `y² = x`, if `x` is a square at level `k` (tower a field). -/
partial def tSqrt? (rad : Array TN) : Nat → TN → Option TN
  | 0, .q a => (ratSqrt? a).map TN.q
  | 0, .e _ _ => none
  | k+1, x =>
    let (a, b) := match x with
      | .q c => (TN.q c, TN.q 0)
      | .e a b => (a, b)
    if tSign rad (k+1) x < 0 then none else
    if tIsZero rad k b then
      match tSqrt? rad k a with
      | some c => some (.e c (.q 0))
      | none =>
        -- y = d √r with d² = a / r
        match tSqrt? rad k (tDiv rad k a rad[k]!) with
        | some d => some (.e (.q 0) d)
        | none => none
    else
      let n := tSub k (tMul rad k a a) (tMul rad k (tMul rad k b b) rad[k]!)
      match tSqrt? rad k n with
      | none => none
      | some sn =>
        let try1 (c2 : TN) : Option TN :=
          if tSign rad k c2 ≤ 0 then none else
          match tSqrt? rad k c2 with
          | none => none
          | some c =>
            let d := tDiv rad k b (tScale 2 c)
            let y := TN.e c d
            if tSign rad (k+1) y < 0 then some (tNeg y) else some y
        match try1 (tScale (1/2) (tAdd k a sn)) with
        | some y => some y
        | none => try1 (tScale (1/2) (tSub k a sn))

/-- lift an element from level `j` to level `k ≥ j`. -/
def tLift : Nat → TN → TN
  | 0, x => x
  | m+1, x => match x with
    | .q c => .q c
    | _ => .e (tLift m x) (.q 0)

/-! ## Towers and complex numbers -/

structure Tower where
  rad : Array TN := #[]
  sq  : Array Float := #[]
  deriving Inhabited

def Tower.lvl (T : Tower) : Nat := T.rad.size

def Tower.base : Tower := { rad := #[.q 3], sq := #[Float.sqrt 3] }

/-- try to take `√x` (x at top level, x ≥ 0) inside the tower; otherwise extend by it.
Returns the new tower and `√x` at the new top level. -/
def Tower.sqrtOrPush (T : Tower) (x : TN) : Tower × TN × Bool :=
  let k := T.lvl
  match tSqrt? T.rad k x with
  | some y => (T, y, false)
  | none =>
    let xf := tFl T.sq k x
    ({ rad := T.rad.push x, sq := T.sq.push (Float.sqrt xf) }, .e (.q 0) (.q 1), true)

structure Cx where
  re : TN
  im : TN
  deriving Inhabited, Repr, BEq

namespace Cx
def add (k : Nat) (z w : Cx) : Cx := ⟨tAdd k z.re w.re, tAdd k z.im w.im⟩
def sub (k : Nat) (z w : Cx) : Cx := ⟨tSub k z.re w.re, tSub k z.im w.im⟩
def neg (z : Cx) : Cx := ⟨tNeg z.re, tNeg z.im⟩
def mul (rad : Array TN) (k : Nat) (z w : Cx) : Cx :=
  ⟨tSub k (tMul rad k z.re w.re) (tMul rad k z.im w.im),
   tAdd k (tMul rad k z.re w.im) (tMul rad k z.im w.re)⟩
def conj (z : Cx) : Cx := ⟨z.re, tNeg z.im⟩
def scale (c : Rat) (z : Cx) : Cx := ⟨tScale c z.re, tScale c z.im⟩
def mulR (rad : Array TN) (k : Nat) (t : TN) (z : Cx) : Cx := ⟨tMul rad k t z.re, tMul rad k t z.im⟩
def norm2 (rad : Array TN) (k : Nat) (z : Cx) : TN :=
  tAdd k (tMul rad k z.re z.re) (tMul rad k z.im z.im)
def lift (m : Nat) (z : Cx) : Cx := ⟨tLift m z.re, tLift m z.im⟩
def zero : Cx := ⟨.q 0, .q 0⟩
def one : Cx := ⟨.q 1, .q 0⟩
/-- lattice point `(a, b) ↦ a + bρ`, `ρ = 1/2 + i√3/2`, at level ≥ 1. -/
def ofLat (a b : Int) : Cx := ⟨.q ((a : Rat) + (b : Rat) / 2), .e (.q 0) (.q ((b : Rat) / 2))⟩
def i_sqrt3 : Cx := ⟨.q 0, .e (.q 0) (.q 1)⟩
end Cx

/-- float complex -/
structure CF where
  x : Float
  y : Float
  deriving Inhabited, Repr

def Cx.toF (T : Tower) (k : Nat) (z : Cx) : CF := ⟨tFl T.sq k z.re, tFl T.sq k z.im⟩

end OL
/-!
# Exact arrangements, lattice bodies, congruence

Units: circles of diameter 1; lattice site `(a, b)` is `a + bρ`, `ρ = e^{iπ/3}`. Contact iff the
squared distance is exactly `1`; overlap iff `< 1`.
-/

namespace OL

abbrev Pt := Int × Int

def eN (v : Pt) : Int := v.1 * v.1 + v.1 * v.2 + v.2 * v.2
def psub (v w : Pt) : Pt := (v.1 - w.1, v.2 - w.2)
def padd (v w : Pt) : Pt := (v.1 + w.1, v.2 + w.2)
def dA : Array Int := #[1, 0, -1, -1, 0, 1]
def dB : Array Int := #[0, 1, 1, 0, -1, -1]
def touchL (p q : Pt) : Bool := eN (psub p q) == 1

def rot60 (v : Pt) : Pt := (-v.2, v.1 + v.2)
def mirr (v : Pt) : Pt := (v.1 + v.2, -v.2)

/-- the 12 lattice symmetries -/
def symF (k : Nat) (v : Pt) : Pt := Id.run do
  let mut w := if k ≥ 6 then mirr v else v
  for _ in [0:k % 6] do w := rot60 w
  return w

def ptLt (p q : Pt) : Bool := p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)

def normSet (s : Array Pt) : Array Pt :=
  let s := s.qsort ptLt
  let o := s[0]!
  s.map (psub · o)

def arrLt (a b : Array Pt) : Bool := Id.run do
  for i in [0:a.size] do
    if ptLt a[i]! b[i]! then return true
    if ptLt b[i]! a[i]! then return false
  return false

def canonSet (s : Array Pt) : Array Pt := Id.run do
  let mut best := normSet s
  for k in [1:12] do
    let c := normSet (s.map (symF k))
    if arrLt c best then best := c
  return best

/-- rigid lattice sets of size `3..N` (closure of the triangle under adding a site touching ≥ 2;
equal to all rigid lattice sets for sizes < 14 by the census). -/
def latticeBodies (N : Nat) : Array (Array (Array Pt)) := Id.run do
  let tri : Array Pt := canonSet #[(0,0),(1,0),(0,1)]
  let mut lv : Array (Array (Array Pt)) := #[#[], #[], #[], #[tri]]
  for n in [4:N+1] do
    let mut seen : Std.HashSet (Array Pt) := {}
    let mut out : Array (Array Pt) := #[]
    for S in lv[n-1]! do
      for p in S do
        for k in [0:6] do
          let x : Pt := (p.1 + dA[k]!, p.2 + dB[k]!)
          if !S.contains x && (S.filter (touchL x)).size ≥ 2 then
            let T := canonSet (S.push x)
            if !seen.contains T then
              seen := seen.insert T
              out := out.push T
    lv := lv.push out
  return lv

/-- symmetries (as maps on sites) preserving the set `S` exactly up to translation:
returns list of permutations of indices. -/
def autPerms (S : Array Pt) : Array (Array Nat) := Id.run do
  let base := normSet S
  let mut out := #[]
  for k in [0:12] do
    let img := S.map (symF k)
    if normSet img == base then
      -- translation t with img + t = S as sets
      let sm := (img.qsort ptLt)[0]!
      let s0 := (S.qsort ptLt)[0]!
      let t := psub s0 sm
      let perm := img.map fun v => (S.findIdx? (· == padd v t)).getD 0
      out := out.push perm
  return out

/-! ## Exact arrangements -/

structure ExArr where
  T : Tower
  pts : Array Cx
  pf : Array CF
  contacts : Array (Nat × Nat) := #[]
  info : String := ""
  deriving Inhabited

def ExArr.k (A : ExArr) : Nat := A.T.lvl
def ExArr.n (A : ExArr) : Nat := A.pts.size

def cfd2 (a b : CF) : Float := (a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y)

def tol : Float := 1e-6

/-- exact comparison of the squared distance of points `i, j` with `c` (rational):
float decides when far from `c`, exact otherwise. Returns -1, 0, 1. -/
def cmpD2 (A : ExArr) (i j : Nat) (c : Rat) : Int :=
  let f := cfd2 A.pf[i]! A.pf[j]!
  let cf := ratF c
  if f < cf - tol then -1 else if f > cf + tol then 1 else
  let k := A.k
  let d := Cx.sub k A.pts[i]! A.pts[j]!
  tSign A.T.rad k (tSub k (Cx.norm2 A.T.rad k d) (.q c))

/-- fully exact comparison (no float shortcut). -/
def cmpD2X (A : ExArr) (i j : Nat) (c : Rat) : Int :=
  let k := A.k
  let d := Cx.sub k A.pts[i]! A.pts[j]!
  tSign A.T.rad k (tSub k (Cx.norm2 A.T.rad k d) (.q c))

def mkArr (T : Tower) (pts : Array Cx) (info : String := "") : ExArr :=
  { T, pts, pf := pts.map (·.toF T T.lvl), info }

/-- `none` if some pair overlaps; otherwise the arrangement with its contacts. -/
def ExArr.validate (A : ExArr) (exact : Bool := false) : Option ExArr := Id.run do
  let n := A.n
  let mut cs := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      let c := if exact then cmpD2X A i j 1 else cmpD2 A i j 1
      if c < 0 then return none
      if c == 0 then cs := cs.push (i, j)
  return some { A with contacts := cs }

def ExArr.nbrs (A : ExArr) : Array (Array Nat) := Id.run do
  let mut nb := Array.replicate A.n #[]
  for (i, j) in A.contacts do
    nb := nb.modify i (·.push j)
    nb := nb.modify j (·.push i)
  return nb

/-- circles with exactly two contacts less than 2 apart (removable) -/
def ExArr.removables (A : ExArr) : Array Nat := Id.run do
  let nb := A.nbrs
  let mut out := #[]
  for i in [0:A.n] do
    if nb[i]!.size == 2 then
      if cmpD2X A nb[i]![0]! nb[i]![1]! 4 < 0 then out := out.push i
  return out

def ExArr.isCore (A : ExArr) : Bool := A.removables.isEmpty

def ExArr.minDeg (A : ExArr) : Nat := (A.nbrs.map (·.size)).foldl min 1000

/-- some circle with two antipodal contacts only (taut) -/
def ExArr.tautCount (A : ExArr) : Nat := Id.run do
  let nb := A.nbrs
  let mut c := 0
  for i in [0:A.n] do
    if nb[i]!.size == 2 then
      if cmpD2X A nb[i]![0]! nb[i]![1]! 4 == 0 then c := c + 1
  return c

/-- exact lattice test (connected contact graph assumed): all contact directions differ by
sixth roots of unity. -/
def ExArr.onLattice (A : ExArr) : Bool := Id.run do
  if A.contacts.isEmpty then return true
  let k := A.k
  let rad := A.T.rad
  let (i0, j0) := A.contacts[0]!
  let d0 := Cx.sub k A.pts[j0]! A.pts[i0]!
  for (i, j) in A.contacts do
    let d := Cx.sub k A.pts[j]! A.pts[i]!
    let w := Cx.mul rad k d (Cx.conj d0)
    let w2 := Cx.mul rad k w w
    let w3 := Cx.mul rad k w2 w
    let w6 := Cx.mul rad k w3 w3
    if !(tIsZero rad k (tSub k w6.re (.q 1)) && tIsZero rad k w6.im) then return false
  return true

/-- connectivity of the contact graph -/
def ExArr.connected (A : ExArr) : Bool := Id.run do
  let nb := A.nbrs
  let mut seen := Array.replicate A.n false
  let mut stack := #[0]
  seen := seen.set! 0 true
  let mut cnt := 1
  while !stack.isEmpty do
    let v := stack.back!
    stack := stack.pop
    for w in nb[v]! do
      if !seen[w]! then
        seen := seen.set! w true
        cnt := cnt + 1
        stack := stack.push w
  return cnt == A.n

/-! ## Invariants and congruence -/

/-- float invariant: sorted squared distances rounded to 1e-6 -/
def ExArr.key (A : ExArr) : Array Int := Id.run do
  let mut ds : Array Float := #[]
  for i in [0:A.n] do
    for j in [i+1:A.n] do
      ds := ds.push (cfd2 A.pf[i]! A.pf[j]!)
  let ds2 := ds.qsort (· < ·)
  return ds2.map fun d => (Float.round (d * 1e6)).toInt64.toInt

/-- exact congruence test (relabelling + isometry, reflections allowed) -/
def congruent (A B : ExArr) : Bool := Id.run do
  if A.n != B.n || A.contacts.size != B.contacts.size then return false
  let kA := A.k
  let kB := B.k
  let K := kA + kB
  let rad := A.T.rad ++ B.T.rad
  let ptsA := A.pts.map (Cx.lift kB)
  let ptsB := B.pts
  let (a0, a1) := A.contacts[0]!
  let dA := Cx.sub K ptsA[a1]! ptsA[a0]!
  let dAf : CF := ⟨A.pf[a1]!.x - A.pf[a0]!.x, A.pf[a1]!.y - A.pf[a0]!.y⟩
  for (c0, c1) in B.contacts do
    for (b0, b1) in [(c0, c1), (c1, c0)] do
      for mir in [false, true] do
        -- float map
        let dBf : CF := ⟨B.pf[b1]!.x - B.pf[b0]!.x, B.pf[b1]!.y - B.pf[b0]!.y⟩
        -- rotation part m = dB * conj dA (|dA| = 1)
        let mf : CF := ⟨dBf.x * dAf.x + dBf.y * dAf.y, dBf.y * dAf.x - dBf.x * dAf.y⟩
        let mapF (z : CF) : CF :=
          let w : CF := ⟨z.x - A.pf[a0]!.x, z.y - A.pf[a0]!.y⟩
          let u : CF := ⟨w.x * dAf.x + w.y * dAf.y, w.y * dAf.x - w.x * dAf.y⟩
          let uc : CF := ⟨u.x, -u.y⟩
          let w2 : CF := if mir then ⟨dBf.x * uc.x - dBf.y * uc.y, dBf.x * uc.y + dBf.y * uc.x⟩
            else ⟨mf.x * w.x - mf.y * w.y, mf.x * w.y + mf.y * w.x⟩
          (⟨w2.x + B.pf[b0]!.x, w2.y + B.pf[b0]!.y⟩ : CF)
        let mut perm : Array Nat := #[]
        let mut ok := true
        for i in [0:A.n] do
          if ok then
            let z := mapF A.pf[i]!
            match (List.range B.n).find? (fun j => cfd2 z B.pf[j]! < 1e-8) with
            | some j => perm := perm.push j
            | none => ok := false
        if ok then
          -- exact confirmation
          let dBx := Cx.sub K ptsB[b1]! ptsB[b0]!
          let mapX (z : Cx) : Cx :=
            let w := Cx.sub K z ptsA[a0]!
            let u := Cx.mul rad K (Cx.conj dA) w
            let w' := if mir then Cx.mul rad K dBx (Cx.conj u) else Cx.mul rad K dBx u
            Cx.add K w' ptsB[b0]!
          let mut good := true
          for i in [0:A.n] do
            if good then
              let z := mapX ptsA[i]!
              let t := Cx.sub K z ptsB[perm[i]!]!
              if !(tIsZero rad K t.re && tIsZero rad K t.im) then good := false
          if good then return true
  return false

/-- store with dedupe up to exact congruence. -/
structure Store where
  arrs : Array ExArr := #[]
  idx : Std.HashMap (Array Int) (Array Nat) := {}
  deriving Inhabited

/-- insert; returns (store, index, isNew) -/
def Store.insert (S : Store) (A : ExArr) : Store × Nat × Bool := Id.run do
  let key := A.key
  let cands := S.idx.getD key #[]
  for c in cands do
    if congruent A S.arrs[c]! then return (S, c, false)
  let i := S.arrs.size
  return ({ arrs := S.arrs.push A, idx := S.idx.insert key (cands.push i) }, i, true)

/-! ## Exact rank of the rigidity matrix -/

def ExArr.rigRank (A : ExArr) : Nat := Id.run do
  let k := A.k
  let rad := A.T.rad
  let n := A.n
  let mut M : Array (Array TN) := #[]
  for (i, j) in A.contacts do
    let d := Cx.sub k A.pts[i]! A.pts[j]!
    let mut row := Array.replicate (2*n) TN.zero
    row := row.set! (2*i) d.re
    row := row.set! (2*i+1) d.im
    row := row.set! (2*j) (tNeg d.re)
    row := row.set! (2*j+1) (tNeg d.im)
    M := M.push row
  let m := M.size
  let mut r := 0
  for col in [0:2*n] do
    if r < m then
      let mut piv := m
      for i in [r:m] do
        if piv == m && !(tIsZero rad k M[i]![col]!) then piv := i
      if piv < m then
        let rowP := M[piv]!
        M := M.set! piv M[r]!
        M := M.set! r rowP
        let inv := tInv rad k rowP[col]!
        for i in [r+1:m] do
          let rowI := M[i]!
          let f := tMul rad k rowI[col]! inv
          if !(tIsZero rad k f) then
            let mut nr := rowI
            for j in [col:2*n] do
              nr := nr.set! j (tSub k rowI[j]! (tMul rad k f rowP[j]!))
            M := M.set! i nr
        r := r + 1
  return r

/-- float rank (for information) -/
def ExArr.rigRankF (A : ExArr) : Nat := Id.run do
  let n := A.n
  let mut M : Array (Array Float) := #[]
  for (i, j) in A.contacts do
    let dx := A.pf[i]!.x - A.pf[j]!.x
    let dy := A.pf[i]!.y - A.pf[j]!.y
    let mut row := Array.replicate (2*n) 0.0
    row := row.set! (2*i) dx
    row := row.set! (2*i+1) dy
    row := row.set! (2*j) (-dx)
    row := row.set! (2*j+1) (-dy)
    M := M.push row
  let m := M.size
  let mut r := 0
  for col in [0:2*n] do
    if r < m then
      let mut piv := m
      let mut best := 1e-9
      for i in [r:m] do
        if M[i]![col]!.abs > best then
          best := M[i]![col]!.abs
          piv := i
      if piv < m then
        let rowP := M[piv]!
        M := M.set! piv M[r]!
        M := M.set! r rowP
        for i in [r+1:m] do
          let rowI := M[i]!
          let f := rowI[col]! / rowP[col]!
          let mut nr := rowI
          for j in [col:2*n] do
            nr := nr.set! j (rowI[j]! - f * rowP[j]!)
          M := M.set! i nr
        r := r + 1
  return r

end OL
namespace OL

def sqrt3F : Float := Float.sqrt 3

def ofLatF (v : Pt) : CF := ⟨Float.ofInt v.1 + Float.ofInt v.2 / 2, Float.ofInt v.2 * sqrt3F / 2⟩
def cmul (a b : CF) : CF := ⟨a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x⟩
def cconj (a : CF) : CF := ⟨a.x, -a.y⟩
def cadd (a b : CF) : CF := ⟨a.x + b.x, a.y + b.y⟩
def csc (c : Float) (a : CF) : CF := ⟨c * a.x, c * a.y⟩

def isLatRotF (R : CF) : Bool :=
  let R2 := cmul R R
  let R3 := cmul R2 R
  let R6 := cmul R3 R3
  (R6.x - 1).abs < 1e-9 && R6.y.abs < 1e-9

/-- ordered pairs of distinct indices up to the automorphisms of the body -/
def pairOrbits (S : Array Pt) : Array (Nat × Nat) := Id.run do
  let auts := autPerms S
  let mut seen : Std.HashSet (Nat × Nat) := {}
  let mut out := #[]
  for i in [0:S.size] do
    for j in [0:S.size] do
      if i != j && !seen.contains (i, j) then
        out := out.push (i, j)
        for pm in auts do seen := seen.insert (pm[i]!, pm[j]!)
  return out

structure Found where
  all : Store := {}
  cores : Store := {}
  nCand : Nat := 0
  nExact : Nat := 0
  wantLat : Bool := false
  latCores : Array ExArr := #[]
  deriving Inhabited

def Found.add (F : Found) (A : ExArr) : Found := Id.run do
  let F := { F with nExact := F.nExact + 1 }
  match A.validate with
  | none => return F
  | some A =>
    if !A.connected then return F
    if A.onLattice then
      if F.wantLat && A.isCore then return { F with latCores := F.latCores.push A }
      return F
    let (all, _, _) := F.all.insert A
    let mut cores := F.cores
    if A.isCore then
      let (c, _, _) := cores.insert A
      cores := c
    return { F with all, cores }

/-- exact rotation `R = g (m - iε√Δ) / (2pq)`; returns tower, level, R. -/
def hingeRot (u v : Pt) (p q m Δ : Int) (ε : Int) : Tower × Cx := Id.run do
  let T0 := Tower.base
  let (T, sD, _) := T0.sqrtOrPush (.q Δ)
  let k := T.lvl
  let g1 := Cx.mul T0.rad 1 (Cx.ofLat u.1 u.2) (Cx.conj (Cx.ofLat v.1 v.2))
  let g := Cx.lift (k - 1) g1
  let fac : Cx := ⟨.q m, tScale (-(ε : Rat)) sD⟩
  let R := Cx.scale (1 / (2 * (p * q : Rat))) (Cx.mul T.rad k g fac)
  return (T, R)

/-- Type A: bodies `B1` (size s1) and `B2` (size s2), hinge + bar. -/
def enumA (bodies : Array (Array (Array Pt))) (n : Nat) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for s1 in [3:n] do
    let s2 := n + 1 - s1
    if s2 ≥ 3 && s1 ≤ s2 && s2 < bodies.size then
      for b1 in [0:bodies[s1]!.size] do
        let B1 := bodies[s1]![b1]!
        let pr1 := pairOrbits B1
        let B1f := B1.map ofLatF
        for b2 in [0:bodies[s2]!.size] do
          for mir in [false, true] do
            let B2 : Array Pt := if mir then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
            for ih2 in [0:s2] do
              for iy in [0:s2] do
                if iy != ih2 then
                  let h2 := B2[ih2]!
                  let y := B2[iy]!
                  let v := psub y h2
                  let q := eN v
                  for (ih1, ix) in pr1 do
                    let h1 := B1[ih1]!
                    let x := B1[ix]!
                    let u := psub x h1
                    let p := eN u
                    let m := p + q - 1
                    let Δ := 4 * p * q - m * m
                    if Δ ≥ 0 then
                      let eps : List Int := if Δ == 0 then [1] else [1, -1]
                      for ε in eps do
                        F := { F with nCand := F.nCand + 1 }
                        let g := cmul (ofLatF u) (cconj (ofLatF v))
                        let fac : CF := ⟨Float.ofInt m, -(Float.ofInt ε) * Float.sqrt (Float.ofInt Δ)⟩
                        let R := csc (1 / (2 * Float.ofInt (p * q))) (cmul g fac)
                        if F.wantLat || !isLatRotF R then
                          let h1f := ofLatF h1
                          let mut ok := true
                          for iw in [0:s2] do
                            if ok && iw != ih2 then
                              let P := cadd h1f (cmul R (ofLatF (psub B2[iw]! h2)))
                              for z in B1f do
                                if ok && cfd2 P z < 1 - 1e-6 then ok := false
                          if ok then
                            let (T, Rx) := hingeRot u v p q m Δ ε
                            let k := T.lvl
                            let mut pts : Array Cx := B1.map fun w => Cx.lift (k - 1) (Cx.ofLat w.1 w.2)
                            for iw in [0:s2] do
                              if iw != ih2 then
                                let w := Cx.lift (k - 1) (Cx.ofLat (B2[iw]!.1 - h2.1) (B2[iw]!.2 - h2.2))
                                pts := pts.push (Cx.add k (Cx.lift (k-1) (Cx.ofLat h1.1 h1.2)) (Cx.mul T.rad k Rx w))
                            let info := s!"A s=({s1},{s2}) B1={s1}#{b1} B2={s2}#{b2}{if mir then "m" else ""} hinge=({ih1},{ih2}) bar=({ix},{iy}) p={p} q={q} Delta={Δ} eps={ε}"
                            F := F.add (mkArr T pts info)
  return F

end OL
namespace OL

/-- Type C: ring of three bodies, three hinges. B1 is a largest body (fixed orientation). -/
def enumC (bodies : Array (Array (Array Pt))) (n : Nat) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for s1 in [3:bodies.size] do
    for s2 in [3:s1+1] do
      if n + 3 ≥ s1 + s2 + 3 then
        let s3 := n + 3 - s1 - s2
        if s3 ≥ 3 && s3 ≤ s1 then
          for b1 in [0:bodies[s1]!.size] do
            let B1 := bodies[s1]![b1]!
            let pr1 := pairOrbits B1
            let B1f := B1.map ofLatF
            for b2 in [0:bodies[s2]!.size] do
              for mir2 in [false, true] do
                let B2 : Array Pt := if mir2 then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
                for b3 in [0:bodies[s3]!.size] do
                  for mir3 in [false, true] do
                    let B3 : Array Pt := if mir3 then (bodies[s3]![b3]!).map mirr else bodies[s3]![b3]!
                    for (i12, i13) in pr1 do
                      let a := psub B1[i13]! B1[i12]!
                      let e1 := eN a
                      for j12 in [0:s2] do
                        for j23 in [0:s2] do
                          if j12 != j23 then
                            let b := psub B2[j23]! B2[j12]!
                            let e2 := eN b
                            for k23 in [0:s3] do
                              for k13 in [0:s3] do
                                if k23 != k13 then
                                  let c := psub B3[k13]! B3[k23]!
                                  let e3 := eN c
                                  let m := e1 + e2 - e3
                                  let Δ := 4 * e1 * e2 - m * m
                                  if Δ ≥ 0 then
                                    let eps : List Int := if Δ == 0 then [1] else [1, -1]
                                    for ε in eps do
                                      F := { F with nCand := F.nCand + 1 }
                                      let g := cmul (ofLatF a) (cconj (ofLatF b))
                                      let fac : CF := ⟨Float.ofInt m, -(Float.ofInt ε) * Float.sqrt (Float.ofInt Δ)⟩
                                      let R2 := csc (1 / (2 * Float.ofInt (e1 * e2))) (cmul g fac)
                                      let h12f := ofLatF B1[i12]!
                                      let H23 := cadd h12f (cmul R2 (ofLatF b))
                                      let amb := cadd (ofLatF a) (csc (-1) (cmul R2 (ofLatF b)))
                                      let R3 := csc (1 / Float.ofInt e3) (cmul amb (cconj (ofLatF c)))
                                      let mut ok := !(isLatRotF R2 && isLatRotF R3)
                                      let mut P2 : Array CF := #[]
                                      for iw in [0:s2] do
                                        if ok && iw != j12 then
                                          let P := cadd h12f (cmul R2 (ofLatF (psub B2[iw]! B2[j12]!)))
                                          for z in B1f do
                                            if ok && cfd2 P z < 1 - 1e-6 then ok := false
                                          P2 := P2.push P
                                      if ok then
                                        for iw in [0:s3] do
                                          if ok && iw != k23 && iw != k13 then
                                            let P := cadd H23 (cmul R3 (ofLatF (psub B3[iw]! B3[k23]!)))
                                            for z in B1f do
                                              if ok && cfd2 P z < 1 - 1e-6 then ok := false
                                            for z in P2 do
                                              if ok && cfd2 P z < 1 - 1e-6 then ok := false
                                      if ok then
                                        -- exact
                                        let (T, R2x) := hingeRot a b e1 e2 m Δ ε
                                        let K := T.lvl
                                        let rad := T.rad
                                        let L (v : Pt) : Cx := Cx.lift (K - 1) (Cx.ofLat v.1 v.2)
                                        let h12 := L B1[i12]!
                                        let bx := L b
                                        let H23x := Cx.add K h12 (Cx.mul rad K R2x bx)
                                        let ambx := Cx.sub K (L a) (Cx.mul rad K R2x bx)
                                        let R3x := Cx.scale (1 / (e3 : Rat)) (Cx.mul rad K ambx (Cx.conj (L c)))
                                        let mut pts : Array Cx := B1.map L
                                        for iw in [0:s2] do
                                          if iw != j12 then
                                            pts := pts.push (Cx.add K h12 (Cx.mul rad K R2x (L (psub B2[iw]! B2[j12]!))))
                                        for iw in [0:s3] do
                                          if iw != k23 && iw != k13 then
                                            pts := pts.push (Cx.add K H23x (Cx.mul rad K R3x (L (psub B3[iw]! B3[k23]!))))
                                        let info := s!"C s=({s1},{s2},{s3}) B1={s1}#{b1} B2={s2}#{b2}{if mir2 then "m" else ""} B3={s3}#{b3}{if mir3 then "m" else ""} h12=({i12},{j12}) h13=({i13},{k13}) h23=({j23},{k23}) e=({e1},{e2},{e3}) Delta={Δ} eps={ε}"
                                        F := F.add (mkArr T pts info)
  return F

/-- Type E: two bodies sharing two circles at distance √N (N with ≥ 2 rotation orbits). -/
def enumE (bodies : Array (Array (Array Pt))) (n : Nat) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for s1 in [3:bodies.size] do
    let s2 := n + 2 - s1
    if s2 ≥ 3 && s1 ≤ s2 && s2 < bodies.size then
      for b1 in [0:bodies[s1]!.size] do
        let B1 := bodies[s1]![b1]!
        let pr1 := pairOrbits B1
        let B1f := B1.map ofLatF
        for b2 in [0:bodies[s2]!.size] do
          for mir in [false, true] do
            let B2 : Array Pt := if mir then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
            for (iu1, iv1) in pr1 do
              let a := psub B1[iv1]! B1[iu1]!
              let N := eN a
              if N ≥ 7 then
                for iu2 in [0:s2] do
                  for iv2 in [0:s2] do
                    if iu2 != iv2 && eN (psub B2[iv2]! B2[iu2]!) == N then
                      F := { F with nCand := F.nCand + 1 }
                      let b := psub B2[iv2]! B2[iu2]!
                      let R := csc (1 / Float.ofInt N) (cmul (ofLatF a) (cconj (ofLatF b)))
                      if !isLatRotF R then
                        let u1f := ofLatF B1[iu1]!
                        let mut ok := true
                        for iw in [0:s2] do
                          if ok && iw != iu2 && iw != iv2 then
                            let P := cadd u1f (cmul R (ofLatF (psub B2[iw]! B2[iu2]!)))
                            for z in B1f do
                              if ok && cfd2 P z < 1 - 1e-6 then ok := false
                        if ok then
                          let T := Tower.base
                          let rad := T.rad
                          let L (v : Pt) : Cx := Cx.ofLat v.1 v.2
                          let Rx := Cx.scale (1 / (N : Rat)) (Cx.mul rad 1 (L a) (Cx.conj (L b)))
                          let mut pts : Array Cx := B1.map L
                          for iw in [0:s2] do
                            if iw != iu2 && iw != iv2 then
                              pts := pts.push (Cx.add 1 (L B1[iu1]!) (Cx.mul rad 1 Rx (L (psub B2[iw]! B2[iu2]!))))
                          let info := s!"E s=({s1},{s2}) B1={s1}#{b1} B2={s2}#{b2}{if mir then "m" else ""} shared=({iu1},{iu2}),({iv1},{iv2}) N={N}"
                          F := F.add (mkArr T pts info)
  return F

end OL
namespace OL

/-- add a point `c` (level `k` of `A.T`) to `A`, possibly over an extended tower. -/
def ExArr.addPt (A : ExArr) (T : Tower) (c : Cx) (info : String) : ExArr :=
  let dk := T.lvl - A.T.lvl
  let pts := (A.pts.map (Cx.lift dk)).push c
  { T, pts, pf := pts.map (·.toF T T.lvl), info }

/-- all one-circle extensions of `A` by a circle touching at least two circles (exact). -/
def ExArr.extensions (A : ExArr) : Array ExArr := Id.run do
  let n := A.n
  let k := A.k
  let rad := A.T.rad
  let mut out := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      let df := cfd2 A.pf[i]! A.pf[j]!
      if df ≤ 4 + tol then
        if cmpD2 A i j 4 ≤ 0 then
          -- float apexes first
          let mf : CF := ⟨(A.pf[i]!.x + A.pf[j]!.x) / 2, (A.pf[i]!.y + A.pf[j]!.y) / 2⟩
          let wf : CF := ⟨A.pf[j]!.x - A.pf[i]!.x, A.pf[j]!.y - A.pf[i]!.y⟩
          let hf := Float.sqrt (max 0 ((4 - df) / (4 * df)))
          for sgn in [1.0, -1.0] do
            let cf : CF := ⟨mf.x - sgn * hf * wf.y, mf.y + sgn * hf * wf.x⟩
            let mut ok := true
            for l in [0:n] do
              if ok && cfd2 cf A.pf[l]! < 1 - tol then ok := false
            if ok then
              -- exact apex
              let w := Cx.sub k A.pts[j]! A.pts[i]!
              let d2 := Cx.norm2 rad k w
              let s := tMul rad k (tSub k (.q 4) d2) (tInv rad k (tScale 4 d2))
              let (T, h, _) := A.T.sqrtOrPush s
              let K := T.lvl
              let dk := K - k
              let mid := Cx.scale (1/2) (Cx.add k A.pts[i]! A.pts[j]!)
              let iw : Cx := ⟨tNeg w.im, w.re⟩
              let off := Cx.mulR T.rad K h (Cx.lift dk iw)
              let c := if sgn > 0 then Cx.add K (Cx.lift dk mid) off else Cx.sub K (Cx.lift dk mid) off
              let B := A.addPt T c s!"{A.info} + apex({i},{j}){if sgn > 0 then "+" else "-"}"
              match B.validate with
              | some B' => out := out.push B'
              | none => pure ()
  return out

/-- closure levels: `lv[n] = Ext(lv[n-1]) ∪ seeds[n]` -/
def closure (seeds : Array (Array ExArr)) (N : Nat) (lo : Nat) : Array Store := Id.run do
  let mut lv : Array Store := Array.replicate (N + 1) {}
  for n in [lo:N+1] do
    let mut S : Store := {}
    if n > lo then
      for A in lv[n-1]!.arrs do
        for B in A.extensions do
          let (S', _, _) := S.insert B
          S := S'
    for A in seeds[n]! do
      let (S', _, _) := S.insert A
      S := S'
    lv := lv.set! n S
  return lv

end OL
namespace OL
def ExArr.peel (A : ExArr) : ExArr := Id.run do
  let mut B := A
  let mut go := true
  while go do
    match B.removables[0]? with
    | none => go := false
    | some c =>
      let keep := (List.range B.n).filter (· != c) |>.toArray
      let pts := keep.map (B.pts[·]!)
      let C := mkArr B.T pts B.info
      B := C.validate.getD C
  return B
end OL

open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "14").toNat!
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  for m in [11:N+1] do
    let FA := enumA bodies m {}
    let FC := enumC bodies m {}
    seeds := seeds.set! m (FA.cores.arrs ++ FC.cores.arrs)
  let lv := closure seeds N 11
  -- catalogue of cores (all levels)
  let mut cores : Array (String × ExArr) := #[]
  for n in [11:N+1] do
    for (A, i) in (lv[n]!.arrs.filter (·.isCore)).zipIdx do
      cores := cores.push (s!"core{n}.{i}[{A.info}]", A)
  for (nm, A) in cores do
    IO.println s!"{nm}: n={A.n} contacts={A.contacts.size} irreducible(count&rank)={A.contacts.size == 2*A.n-3}"
  for n in [11:N+1] do
    let mut hist : Std.HashMap String Nat := {}
    for A in lv[n]!.arrs do
      let K := A.peel
      let mut name := "UNMATCHED"
      for (nm, C) in cores do
        if name == "UNMATCHED" && C.n == K.n && congruent K C then name := nm
      hist := hist.insert name (hist.getD name 0 + 1)
    IO.println s!"n={n}: total {lv[n]!.arrs.size}"
    for (nm, c) in hist.toArray do
      IO.println s!"   {c} peel to {nm}"
