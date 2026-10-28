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
