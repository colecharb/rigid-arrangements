import Std.Data.HashMap
import Std.Data.HashSet
open Std

/-!
# Exploratory enumerator of rigid arrangements of unit circles on the triangular lattice

Lattice site `(a, b)` is the point `2a + b(1 + i√3)`; two circles touch iff the difference of
their sites is one of the six unit vectors below (eNorm 1).

* Canonical forms: minimum, over the 12 lattice symmetries, of the packed sorted codes of the
  translated image.
* `rigid n = Ext (rigid (n-1)) ∪ rigidCores n`, where `Ext` adds a site touching ≥ 2 sites
  (Henneberg step; always rigid) and a *core* is a set with no removable circle (no circle of
  degree exactly 2 whose two neighbours are not opposite).
* Core candidates (connected, min degree ≥ 2, every degree-2 circle straight) are found by a
  pruned Redelmeier search over fixed polyhexes; rigidity of a core candidate is decided by the
  exact rank of the rigidity matrix, written in the (affinely equivalent) coordinates `(a, b)`.
-/

namespace RA

abbrev Pt := Int × Int

/-- unit vectors, counterclockwise: direction `k` is at `60k°`; `k+3` is opposite. -/
def dA : Array Int := #[1, 0, -1, -1, 0, 1]
def dB : Array Int := #[0, 1, 1, 0, -1, -1]

/-! ## Symmetries and canonical form -/

structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Inhabited

@[inline] def M2.app (m : M2) (p : Pt) : Pt := (m.a * p.1 + m.b * p.2, m.c * p.1 + m.d * p.2)
def M2.mul (m n : M2) : M2 :=
  ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d, m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d⟩

/-- rotation by 60°: (a,b) ↦ (-b, a+b); reflection: (a,b) ↦ (b,a). -/
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

/-- Packed key of a point set after translating its bounding box to the origin:
sorted codes `64a + b`, packed base 4096 (most significant = smallest code). -/
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

/-- Decode a key of a set of `n` sites. Coordinates land in `[0, 63]`. -/
def decode (n key : Nat) : Array Pt := Id.run do
  let mut out : Array Pt := #[]
  let mut k := key
  for _ in [0:n] do
    let c := k % 4096
    out := out.push (Int.ofNat (c / 64), Int.ofNat (c % 64))
    k := k / 4096
  return out

/-! ## Local grid for a decoded set (coordinates in `[0,63]`, padded by 2) -/

def G : Nat := 68
@[inline] def gidx (p : Pt) : Nat := ((p.1 + 2) * 68 + (p.2 + 2)).toNat
/-- grid offsets of the 6 unit vectors: (a+1,b) → +68, (a,b+1) → +1, … -/
def gOff : Array Int := #[68, 1, -67, -68, -1, 67]
@[inline] def gnb (g : Nat) (k : Nat) : Nat := (Int.ofNat g + gOff[k]!).toNat

def mkGrid (pts : Array Pt) : Array Bool := Id.run do
  let mut gr := Array.replicate (G * G) false
  for p in pts do gr := gr.set! (gidx p) true
  return gr

/-- bitmask of occupied neighbour directions of grid cell `g`. -/
@[inline] def nbMask (gr : Array Bool) (g : Nat) : Nat := Id.run do
  let mut m := 0
  for k in [0:6] do
    if gr[gnb g k]! then m := m ||| (1 <<< k)
  return m

def popc (m : Nat) : Nat := Id.run do
  let mut c := 0
  for k in [0:6] do
    if m &&& (1 <<< k) != 0 then c := c + 1
  return c

@[inline] def isStraight (m : Nat) : Bool := m == 9 || m == 18 || m == 36

/-! ## Exact rank of the rigidity matrix (fraction-free Gaussian elimination over ℤ) -/

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

/-- contacts of a point set, as index pairs. -/
def contacts (pts : Array Pt) : Array (Nat × Nat) := Id.run do
  let mut es := #[]
  for i in [0:pts.size] do
    for j in [i+1:pts.size] do
      let x := pts[i]!.1 - pts[j]!.1
      let y := pts[i]!.2 - pts[j]!.2
      if x * x + x * y + y * y == 1 then es := es.push (i, j)
  return es

/-- rank of the rigidity matrix in coordinates `(a, b)`. -/
def rigRank (pts : Array Pt) : Nat := Id.run do
  let n := pts.size
  let es := contacts pts
  let mut rows : Array (Array Int) := #[]
  for (i, j) in es do
    let x := pts[i]!.1 - pts[j]!.1
    let y := pts[i]!.2 - pts[j]!.2
    let row := ((((Array.replicate (2 * n) (0 : Int)).set! (2*i) x).set! (2*i+1) y).set!
      (2*j) (-x)).set! (2*j+1) (-y)
    rows := rows.push row
  return intRank rows (2 * n)

/-- infinitesimally rigid: rank `2n - 3` (for `n ≥ 2`). -/
def infRigid (pts : Array Pt) : Bool :=
  pts.size ≤ 1 || rigRank pts == 2 * pts.size - 3

/-! ## Explicit flex certificates (as in `Flex.lean`) -/

/-- some circle whose removal disconnects the contact graph (rotation flex), or the graph is
disconnected. -/
def hasCutCircle (pts : Array Pt) : Bool := Id.run do
  let n := pts.size
  let es := contacts pts
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for (i, j) in es do
    adj := adj.modify i (·.push j)
    adj := adj.modify j (·.push i)
  for v in [0:n+1] do   -- v = n: no removal (connectivity)
    let start := if v == 0 then 1 else 0
    if n ≥ 3 || v == n then
      let mut seen := Array.replicate n false
      if v < n then seen := seen.set! v true
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
      let target := if v < n then n - 1 else n
      if cnt < target then return true
  return false

/-- shear flex: for some unit vector `u`, a nonempty proper set `S` such that every contact
between `S` and the rest is `center(S-side) - center(rest-side) = 2u`. Equivalently the digraph
(non-`u`-parallel contacts in both directions, `u`-parallel contacts oriented along `+u`) is not
strongly connected. -/
def hasShear (pts : Array Pt) : Bool := Id.run do
  let n := pts.size
  if n < 3 then return false
  let es := contacts pts
  for k in [0:3] do
    -- build digraph
    let mut out : Array (Array Nat) := Array.replicate n #[]
    let mut inn : Array (Array Nat) := Array.replicate n #[]
    for (i, j) in es do
      let x := pts[j]!.1 - pts[i]!.1
      let y := pts[j]!.2 - pts[i]!.2
      if x == dA[k]! && y == dB[k]! then        -- j = i + u : edge i → j
        out := out.modify i (·.push j); inn := inn.modify j (·.push i)
      else if x == -dA[k]! && y == -dB[k]! then  -- i = j + u : edge j → i
        out := out.modify j (·.push i); inn := inn.modify i (·.push j)
      else
        out := (out.modify i (·.push j)).modify j (·.push i)
        inn := (inn.modify i (·.push j)).modify j (·.push i)
    -- strongly connected iff vertex 0 reaches all along `out` and along `inn`
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

/-! ## Pruned Redelmeier search for core candidates

Grid of width `W = 2N+3`, rows `b = -1 … N`; cell index `(b+1)·W + (a+N+1)`.
Status: 0 free, 1 in, 2 pending (in the current untried list), 3 excluded/forbidden. -/

@[inline] def nbI (W c k : Nat) : Nat :=
  match k with
  | 0 => c + 1
  | 1 => c + W
  | 2 => c + W - 1
  | 3 => c - 1
  | 4 => c - W
  | _ => c - W + 1

/-- in-mask and available-mask (free or pending) of cell `c`. -/
@[inline] def cellMasks (st : Array UInt8) (W c : Nat) : Nat × Nat := Id.run do
  let mut im := 0
  let mut am := 0
  for k in [0:6] do
    let s := st[nbI W c k]!
    if s == 1 then im := im ||| (1 <<< k)
    else if s != 3 then am := am ||| (1 <<< k)
  return (im, am)

/-- Can cell `c` (in the polyhex) still end with degree ≥ 3, or degree 2 straight, given that
at most `r` more cells will be added? -/
@[inline] def feasible (st : Array UInt8) (W c r : Nat) : Bool :=
  let (im, am) := cellMasks st W c
  let i := popc im
  let a := popc am
  if i ≥ 3 then true
  else if i == 2 then isStraight im || (a ≥ 1 && r ≥ 1)
  else if i == 1 then
    let opp := ((im <<< 3) ||| (im >>> 3)) &&& 63
    ((am &&& opp) != 0 && r ≥ 1) || (a ≥ 2 && r ≥ 2)
  else a ≥ 2 && r ≥ 2

@[inline] def finalOK (st : Array UInt8) (W c : Nat) : Bool :=
  let (im, _) := cellMasks st W c
  popc im ≥ 3 || isStraight im

structure Acc where
  leaves : Nat := 0          -- fixed polyhexes of size N reached (all, if unpruned)
  nodes : Nat := 0
  found : Array (Array Nat) := #[]   -- fixed core candidates (cell indices)

partial def search (N W : Nat) (pruned : Bool) (U : Array Nat) (st0 : Array UInt8)
    (cells0 : Array Nat) (acc0 : Acc) : Array UInt8 × Array Nat × Acc := Id.run do
  let mut st := st0
  let mut cells := cells0
  let mut acc := acc0
  let mut i := 0
  let mut stop := false
  while i < U.size && !stop do
    let c := U[i]!
    st := st.set! c 1
    cells := cells.push c
    acc := { acc with nodes := acc.nodes + 1 }
    let size := cells.size
    let r := N - size
    let ok := !pruned ||
      (feasible st W c r && (r > 2 || cells.all (fun d => feasible st W d r)))
    if ok then
      if size == N then
        acc := { acc with leaves := acc.leaves + 1 }
        if cells.all (fun d => finalOK st W d) then
          acc := { acc with found := acc.found.push cells }
      else
        let mut newU := U.extract (i+1) U.size
        let start := newU.size
        for k in [0:6] do
          let d := nbI W c k
          if st[d]! == 0 then
            st := st.set! d 2
            newU := newU.push d
        let (st', cells', acc') := search N W pruned newU st cells acc
        st := st'; cells := cells'; acc := acc'
        for j in [start:newU.size] do
          st := st.set! newU[j]! 0
    st := st.set! c 3
    cells := cells.pop
    if pruned then
      let r' := N - cells.size
      for k in [0:6] do
        let d := nbI W c k
        if st[d]! == 1 && !(feasible st W d r') then stop := true
    i := i + 1
  for j in [0:i] do
    st := st.set! U[j]! 2
  return (st, cells, acc)

/-- Run the search for polyhexes of `N ≥ 2` cells. Returns the accumulator; core candidates are
converted to points. -/
def runSearch (N : Nat) (pruned : Bool) : Acc × Array (Array Pt) := Id.run do
  let W := 2 * N + 3
  let off := N + 1
  let H := N + 2
  let mut st := Array.replicate (W * H) (0 : UInt8)
  for x in [0:W] do st := st.set! x 3                       -- row b = -1
  for x in [0:off] do st := st.set! (W + x) 3               -- row b = 0, a < 0
  for y in [0:H] do
    st := st.set! (y * W) 3
    st := st.set! (y * W + W - 1) 3
  let o := W + off
  st := st.set! o 1
  let mut U : Array Nat := #[]
  for k in [0:6] do
    let d := nbI W o k
    if st[d]! == 0 then
      st := st.set! d 2
      U := U.push d
  let (_, _, acc) := search N W pruned U st #[o] {}
  let toPt (c : Nat) : Pt := (Int.ofNat (c % W) - Int.ofNat off, Int.ofNat (c / W) - 1)
  return (acc, acc.found.map (·.map toPt))

/-! ## Henneberg extension -/

/-- All `S ∪ {x}` with `x ∉ S` touching ≥ 2 sites of `S`, with a flag "x is a straight
degree-2 addition" (its only two neighbours are opposite). -/
def extensions (pts : Array Pt) : Array (Array Pt × Bool) := Id.run do
  let gr := mkGrid pts
  let mut seen := gr
  let mut out := #[]
  for p in pts do
    for k in [0:6] do
      let x : Pt := (p.1 + dA[k]!, p.2 + dB[k]!)
      let g := gidx x
      if !seen[g]! then
        seen := seen.set! g true
        let m := nbMask gr g
        if popc m ≥ 2 then
          out := out.push (pts.push x, popc m == 2 && isStraight m)
  return out

/-! ## The level-by-level enumeration -/

/-- rigid sets of size `n`: canonical key ↦ infinitesimally rigid? -/
abbrev Level := HashMap Nat Bool

end RA

namespace RA

/-- Search from `start` along directed edges for a vertex (not in `forbid`) holding a free
pebble; if found, reverse the path and move the pebble to `start`. -/
partial def pebbleSearch (peb : Array Nat) (out : Array (Array Nat)) (start : Nat)
    (forbid : Array Bool) : Option (Array Nat × Array (Array Nat)) := Id.run do
  let n := peb.size
  let mut parent : Array Nat := Array.replicate n n
  let mut seen := forbid.set! start true
  let mut stack := #[start]
  let mut found := n
  while !stack.isEmpty && found == n do
    let u := stack.back!
    stack := stack.pop
    for w in out[u]! do
      if found == n && !seen[w]! then
        seen := seen.set! w true
        parent := parent.set! w u
        if peb[w]! > 0 then found := w else stack := stack.push w
  if found == n then return none
  -- reverse the path start → … → found
  let mut peb := peb
  let mut out := out
  peb := peb.set! found (peb[found]! - 1)
  peb := peb.set! start (peb[start]! + 1)
  let mut x := found
  while x != start do
    let p := parent[x]!
    -- edge p → x becomes x → p
    let i := (out[p]!).idxOf x
    out := out.modify p (fun a => a.eraseIdx! i)
    out := out.modify x (·.push p)
    x := p
  return some (peb, out)

/-- Rank of the generic 2-dimensional rigidity matroid of a graph ((2,3)-pebble game). -/
def genericRank (n : Nat) (es : Array (Nat × Nat)) : Nat := Id.run do
  let mut peb := Array.replicate n 2
  let mut out : Array (Array Nat) := Array.replicate n #[]
  let mut rank := 0
  for (u, v) in es do
    let mut ok := true
    for (a, b) in [(u, v), (v, u)] do
      let forbid := (Array.replicate n false).set! b true
      while ok && peb[a]! < 2 do
        match pebbleSearch peb out a forbid with
        | some (p', o') => peb := p'; out := o'
        | none => ok := false
    if ok && peb[u]! == 2 && peb[v]! == 2 then
      peb := peb.set! u 1
      out := out.modify u (·.push v)
      rank := rank + 1
  return rank

/-- `p` is a regular point (rank of the rigidity matrix = generic rank) but not infinitesimally
rigid: then the framework flexes (Asimow–Roth 1978). Returns (rank R(p), generic rank). -/
def ranks (pts : Array Pt) : Nat × Nat :=
  (rigRank pts, genericRank pts.size (contacts pts))

end RA

namespace RA

/-! ## Optimized, parallel version of the pruned Redelmeier search -/

@[inline] def popc6 (m : UInt32) : UInt32 :=
  let one : UInt32 := 1
  (m &&& one) + ((m >>> 1) &&& one) + ((m >>> 2) &&& one) + ((m >>> 3) &&& one) +
    ((m >>> 4) &&& one) + ((m >>> 5) &&& one)

@[inline] def stat (st : ByteArray) (i : Nat) : UInt8 := st.get! i

/-- (in-mask, available-mask) of cell `c` on a grid of width `W`. -/
@[inline] def masks2 (st : ByteArray) (W c : Nat) : UInt32 × UInt32 :=
  let s0 := stat st (c + 1)
  let s1 := stat st (c + W)
  let s2 := stat st (c + W - 1)
  let s3 := stat st (c - 1)
  let s4 := stat st (c - W)
  let s5 := stat st (c - W + 1)
  let i : UInt32 := (if s0 == 1 then 1 else 0) ||| (if s1 == 1 then 2 else 0) ||| (if s2 == 1 then 4 else 0) |||
    (if s3 == 1 then 8 else 0) ||| (if s4 == 1 then 16 else 0) ||| (if s5 == 1 then 32 else 0)
  let a : UInt32 := (if s0 == 0 || s0 == 2 then 1 else 0) ||| (if s1 == 0 || s1 == 2 then 2 else 0) |||
    (if s2 == 0 || s2 == 2 then 4 else 0) ||| (if s3 == 0 || s3 == 2 then 8 else 0) |||
    (if s4 == 0 || s4 == 2 then 16 else 0) ||| (if s5 == 0 || s5 == 2 then 32 else 0)
  (i, a)

@[inline] def feasible2 (st : ByteArray) (W c r : Nat) : Bool :=
  let (im, am) := masks2 st W c
  let i := popc6 im
  if i ≥ 3 then true
  else
    let a := popc6 am
    if i == 2 then (im == 9 || im == 18 || im == 36) || (a ≥ 1 && r ≥ 1)
    else if i == 1 then
      let opp := ((im <<< 3) ||| (im >>> 3)) &&& 63
      ((am &&& opp) != 0 && r ≥ 1) || (a ≥ 2 && r ≥ 2)
    else a ≥ 2 && r ≥ 2

@[inline] def finalOK2 (st : ByteArray) (W c : Nat) : Bool :=
  let (im, _) := masks2 st W c
  popc6 im ≥ 3 || im == 9 || im == 18 || im == 36

structure Acc2 where
  nodes : Nat := 0
  found : Array (Array Nat) := #[]
  frontier : Array (Array Nat × ByteArray × Array Nat) := #[]

/-- `checkAll`: below this many remaining cells, re-check every cell of the polyhex. -/
partial def search2 (N W splitAt checkAll : Nat) (U : Array Nat) (st0 : ByteArray)
    (cells0 : Array Nat) (acc0 : Acc2) : ByteArray × Array Nat × Acc2 := Id.run do
  let mut st := st0
  let mut cells := cells0
  let mut acc := acc0
  let mut nodes := 0
  let mut i := 0
  let mut stop := false
  while i < U.size && !stop do
    let c := U[i]!
    st := st.set! c 1
    cells := cells.push c
    nodes := nodes + 1
    let size := cells.size
    let r := N - size
    let ok := feasible2 st W c r && (r > checkAll || cells.all (fun d => feasible2 st W d r))
    if ok then
      if size == N then
        if cells.all (fun d => finalOK2 st W d) then
          acc := { acc with found := acc.found.push cells }
      else
        let mut newU := U.extract (i+1) U.size
        let start := newU.size
        for k in [0:6] do
          let d := nbI W c k
          if stat st d == 0 then
            st := st.set! d 2
            newU := newU.push d
        if size == splitAt then
          acc := { acc with frontier := acc.frontier.push (newU, st, cells) }
        else
          let (st', cells', acc') := search2 N W splitAt checkAll newU st cells acc
          st := st'; cells := cells'; acc := acc'
        for j in [start:newU.size] do
          st := st.set! newU[j]! 0
    st := st.set! c 3
    cells := cells.pop
    let r' := N - cells.size
    if !feasible2 st W (nbI W c 0) r' && stat st (nbI W c 0) == 1 then stop := true
    for k in [1:6] do
      let d := nbI W c k
      if stat st d == 1 && !(feasible2 st W d r') then stop := true
    i := i + 1
  for j in [0:i] do
    st := st.set! U[j]! 2
  return (st, cells, { acc with nodes := acc.nodes + nodes })

def initSearch (N : Nat) : Nat × Nat × ByteArray × Array Nat × Nat := Id.run do
  let W := 2 * N + 3
  let off := N + 1
  let H := N + 2
  let mut st := ByteArray.mk (Array.replicate (W * H) (0 : UInt8))
  for x in [0:W] do st := st.set! x 3
  for x in [0:off] do st := st.set! (W + x) 3
  for y in [0:H] do
    st := st.set! (y * W) 3
    st := st.set! (y * W + W - 1) 3
  let o := W + off
  st := st.set! o 1
  let mut U : Array Nat := #[]
  for k in [0:6] do
    let d := nbI W o k
    if stat st d == 0 then
      st := st.set! d 2
      U := U.push d
  return (W, off, st, U, o)

/-- Parallel pruned search: split the tree at `splitAt` cells, run the frontier as tasks.
Returns (nodes, fixed core candidates as points). -/
def runSearchPar (N splitAt checkAll nChunks : Nat) : Nat × Array (Array Pt) := Id.run do
  let (W, off, st, U, o) := initSearch N
  let (_, _, acc) := search2 N W splitAt checkAll U st #[o] {}
  let fr := acc.frontier
  let chunk := (fr.size + nChunks - 1) / max nChunks 1
  let mut tasks : Array (Task Acc2) := #[]
  for t in [0:nChunks] do
    let part := (List.range ((fr.size + nChunks - 1 - t) / nChunks)).toArray.map fun j => fr[t + j * nChunks]!
    tasks := tasks.push <| Task.spawn fun _ => Id.run do
      let mut a : Acc2 := {}
      for (u, s, cs) in part do
        let (_, _, a') := search2 N W 0 checkAll u s cs a
        a := a'
      return a
  let mut nodes := acc.nodes
  let mut found := acc.found
  for t in tasks do
    let a := t.get
    nodes := nodes + a.nodes
    found := found ++ a.found
  let toPt (c : Nat) : Pt := (Int.ofNat (c % W) - Int.ofNat off, Int.ofNat (c / W) - 1)
  return (nodes, found.map (·.map toPt))

/-- Parallel extension of a level: split into chunks, merge the maps. -/
def extendLevelPar (n : Nat) (prev : Level) (nChunks : Nat) : HashMap Nat Bool := Id.run do
  let arr := prev.toArray
  let chunk := (arr.size + nChunks - 1) / max nChunks 1
  let mut tasks : Array (Task (HashMap Nat Bool)) := #[]
  for t in [0:nChunks] do
    let part := arr.extract (t * chunk) (min arr.size ((t + 1) * chunk))
    tasks := tasks.push <| Task.spawn (prio := .dedicated) fun _ => Id.run do
      let mut m : HashMap Nat Bool := {}
      for (key, ir) in part do
        for (q, straight) in extensions (decode (n - 1) key) do
          let k := canonKey q
          let cert := ir && !straight
          match m.get? k with
          | some true => pure ()
          | _ => m := m.insert k cert
      return m
  let mut m : HashMap Nat Bool := {}
  for t in tasks do
    for (k, v) in t.get do
      match m.get? k with
      | some true => pure ()
      | _ => m := m.insert k v
  return m

end RA

namespace RA

def showPts (pts : Array Pt) : String :=
  "[" ++ ", ".intercalate (pts.toList.map fun p => s!"({p.1},{p.2})") ++ "]"

def histStr (h : HashMap Nat Nat) : String :=
  let l := h.toList.toArray.qsort (fun x y => x.1 < y.1)
  " ".intercalate (l.toList.map fun (k, v) => s!"{k}:{v}")

def bump (h : HashMap Nat Nat) (k : Nat) : HashMap Nat Nat :=
  h.insert k (h.getD k 0 + 1)

end RA

namespace RA

/-! ## Orderly generation (canonical deletion of a removable circle)

Every rigid lattice set `T` of `n ≥ 4` circles either has a removable circle (degree exactly 2,
the two neighbours not opposite) or is a *core*. A non-core `T` is generated exactly once:
from the canonical representative of `T \ v`, where `v` is the *canonical removable circle* of
`T` (the removable circle with the smallest code in the canonical image of `T`), up to
automorphisms. Infinitesimal rigidity is inherited exactly along such a step (a degree-2 vertex
with non-parallel bars). Cores come from the pruned search.

Canonical image: among the 12 lattice-symmetry images (each translated so that its bounding box
starts at `(0,0)`), the one minimising `(Σ codes, packed sorted codes)`. -/

/-- signature and full key of image `g` of `pts`, plus its translation. -/
@[inline] def imgMin (m : M2) (pts : Array Pt) : Int × Int := Id.run do
  let p0 := m.app pts[0]!
  let mut ma := p0.1
  let mut mb := p0.2
  for p in pts do
    let q := m.app p
    if q.1 < ma then ma := q.1
    if q.2 < mb then mb := q.2
  return (ma, mb)

@[inline] def code (m : M2) (ma mb : Int) (p : Pt) : Nat :=
  let q := m.app p
  ((q.1 - ma) * 64 + (q.2 - mb)).toNat

def fullKey (m : M2) (ma mb : Int) (pts : Array Pt) : Nat := Id.run do
  let codes := (pts.map (code m ma mb)).qsort (· < ·)
  let mut k := 0
  for c in codes do k := k * 4096 + c
  return k

/-- Canonical key, and the list of minimising images `(symmetry index, ma, mb)`. -/
def canonInfo (pts : Array Pt) : Nat × Array (Nat × Int × Int) := Id.run do
  let mut sigs : Array (Nat × Int × Int) := #[]
  let mut best := 0
  for gi in [0:12] do
    let m := syms[gi]!
    let (ma, mb) := imgMin m pts
    let mut s := 0
    for p in pts do s := s + code m ma mb p
    sigs := sigs.push (s, ma, mb)
    if gi == 0 || s < best then best := s
  let mut bestKey := 0
  let mut mins : Array (Nat × Int × Int) := #[]
  for gi in [0:12] do
    let (s, ma, mb) := sigs[gi]!
    if s == best then
      let k := fullKey syms[gi]! ma mb pts
      if mins.isEmpty || k < bestKey then
        bestKey := k
        mins := #[(gi, ma, mb)]
      else if k == bestKey then
        mins := mins.push (gi, ma, mb)
  return (best * 2 ^ (12 * pts.size) + bestKey, mins)   -- the signature is part of the key

def canonKey2 (pts : Array Pt) : Nat := (canonInfo pts).1

/-- decode a key produced by `canonKey2` (strip the signature). -/
def decode2 (n key : Nat) : Array Pt := decode n (key % 2 ^ (12 * n))

/-! ## Small local grids -/

structure LGrid where
  ma : Int
  mb : Int
  H : Nat
  g : ByteArray

@[inline] def LGrid.idx (L : LGrid) (p : Pt) : Nat := ((p.1 - L.ma + 2) * L.H + (p.2 - L.mb + 2)).toNat
@[inline] def LGrid.has (L : LGrid) (p : Pt) : Bool := L.g.get! (L.idx p) == 1
@[inline] def LGrid.mask (L : LGrid) (p : Pt) : UInt32 :=
  (if L.has (p.1+1, p.2) then 1 else 0) ||| (if L.has (p.1, p.2+1) then 2 else 0) |||
  (if L.has (p.1-1, p.2+1) then 4 else 0) ||| (if L.has (p.1-1, p.2) then 8 else 0) |||
  (if L.has (p.1, p.2-1) then 16 else 0) ||| (if L.has (p.1+1, p.2-1) then 32 else 0)

/-- grid with margin 2 (so neighbours of neighbours are in range). -/
def mkLGrid (pts : Array Pt) : LGrid := Id.run do
  let mut ma := pts[0]!.1
  let mut mb := pts[0]!.2
  let mut Ma := ma
  let mut Mb := mb
  for p in pts do
    if p.1 < ma then ma := p.1
    if p.2 < mb then mb := p.2
    if p.1 > Ma then Ma := p.1
    if p.2 > Mb then Mb := p.2
  let H := (Mb - mb + 5).toNat
  let Wd := (Ma - ma + 5).toNat
  let mut L : LGrid := ⟨ma, mb, H, ByteArray.mk (Array.replicate (Wd * H) 0)⟩
  for p in pts do L := { L with g := L.g.set! (L.idx p) 1 }
  return L

@[inline] def isStraightU (m : UInt32) : Bool := m == 9 || m == 18 || m == 36
@[inline] def rot1 (m : UInt32) : UInt32 := ((m <<< 1) ||| (m >>> 5)) &&& 63

/-! ## Statistics -/

structure St where
  count : Nat := 0
  sing : Nat := 0
  singStraight : Nat := 0
  sat : Nat := 0
  pcNonSat : Nat := 0
  covNoPC : Nat := 0
  gap : Nat := 0
  cores : Nat := 0
  hE : HashMap Nat Nat := {}
  hT : HashMap Nat Nat := {}
  exGap : Array Nat := #[]
  exCov : Array Nat := #[]
  exPC : Array Nat := #[]
  exSing : Array Nat := #[]

def St.merge (a b : St) : St :=
  let mh (x y : HashMap Nat Nat) := y.fold (fun acc k v => acc.insert k (acc.getD k 0 + v)) x
  { count := a.count + b.count, sing := a.sing + b.sing,
    singStraight := a.singStraight + b.singStraight, sat := a.sat + b.sat,
    pcNonSat := a.pcNonSat + b.pcNonSat, covNoPC := a.covNoPC + b.covNoPC, gap := a.gap + b.gap,
    cores := a.cores + b.cores, hE := mh a.hE b.hE, hT := mh a.hT b.hT,
    exGap := (a.exGap ++ b.exGap).extract 0 5, exCov := (a.exCov ++ b.exCov).extract 0 5,
    exPC := (a.exPC ++ b.exPC).extract 0 5, exSing := (a.exSing ++ b.exSing).extract 0 5 }

/-- triangle vertices: up `U(a,b) = {(a,b),(a+1,b),(a,b+1)}`,
down `D(a,b) = {(a+1,b),(a,b+1),(a+1,b+1)}`. -/
@[inline] def triVerts (q : Pt) (up : Bool) : Array Pt :=
  if up then #[q, (q.1+1, q.2), (q.1, q.2+1)] else #[(q.1+1, q.2), (q.1, q.2+1), (q.1+1, q.2+1)]

@[inline] def triExists (L : LGrid) (q : Pt) (up : Bool) : Bool :=
  (triVerts q up).all L.has

@[inline] def triNbrs (q : Pt) (up : Bool) : Array (Pt × Bool) :=
  if up then #[(q, false), ((q.1-1, q.2), false), ((q.1, q.2-1), false)]
  else #[(q, true), ((q.1+1, q.2), true), ((q.1, q.2+1), true)]

/-- edge-components of the triangles; returns the list of components (as triangle lists). -/
def triComponents (L : LGrid) (tris : Array (Pt × Bool)) : Array (Array (Pt × Bool)) := Id.run do
  let mut vis := ByteArray.mk (Array.replicate L.g.size 0)
  let bit (up : Bool) : UInt8 := if up then 1 else 2
  let mut comps := #[]
  for t in tris do
    let i := L.idx t.1
    if vis.get! i &&& bit t.2 == 0 then
      vis := vis.set! i (vis.get! i ||| bit t.2)
      let mut comp := #[t]
      let mut stack := #[t]
      while !stack.isEmpty do
        let u := stack.back!
        stack := stack.pop
        for w in triNbrs u.1 u.2 do
          if triExists L w.1 w.2 then
            let j := L.idx w.1
            if vis.get! j &&& bit w.2 == 0 then
              vis := vis.set! j (vis.get! j ||| bit w.2)
              comp := comp.push w
              stack := stack.push w
      comps := comps.push comp
  return comps

def analyze (st : St) (pts : Array Pt) (key : Nat) (ir isCore : Bool) : St := Id.run do
  let L := mkLGrid pts
  let mut e := 0
  let mut covered := true
  let mut straight2 := false
  let mut tris : Array (Pt × Bool) := #[]
  for p in pts do
    let m := L.mask p
    e := e + (popc6 m).toNat
    if m &&& rot1 m == 0 then covered := false
    if isStraightU m then straight2 := true
    if m &&& 3 == 3 then tris := tris.push (p, true)        -- up triangle anchored at p
    if m &&& 6 == 6 then tris := tris.push ((p.1-1, p.2), false)  -- down, with p = (a+1,b)
  e := e / 2
  let mut st := { st with count := st.count + 1, hE := bump st.hE e, hT := bump st.hT tris.size }
  if isCore then st := { st with cores := st.cores + 1 }
  if !ir then
    st := { st with sing := st.sing + 1, exSing := if st.exSing.size < 5 then st.exSing.push key else st.exSing }
    if straight2 then st := { st with singStraight := st.singStraight + 1 }
  if !covered then
    st := { st with gap := st.gap + 1, exGap := if st.exGap.size < 5 then st.exGap.push key else st.exGap }
  else
    let comps := triComponents L tris
    if comps.size == 1 then st := { st with sat := st.sat + 1 }
    else
      let coversAll (c : Array (Pt × Bool)) : Bool :=
        pts.all fun p => c.any fun t => (triVerts t.1 t.2).contains p
      if comps.any coversAll then
        st := { st with pcNonSat := st.pcNonSat + 1, exPC := if st.exPC.size < 5 then st.exPC.push key else st.exPC }
      else
        st := { st with covNoPC := st.covNoPC + 1, exCov := if st.exCov.size < 5 then st.exCov.push key else st.exCov }
  return st

/-! ## One generation step for one parent -/

/-- children of `S` (size `n-1`) by adding a circle with exactly two non-opposite neighbours,
accepted only when the new circle is the canonical removable circle of the child. -/
def children (S : Array Pt) : Array (Nat × Array Pt) := Id.run do
  let L := mkLGrid S
  let mut seen : Array Pt := #[]
  let mut out : Array (Nat × Array Pt) := #[]
  for p in S do
    for k in [0:6] do
      let x : Pt := (p.1 + dA[k]!, p.2 + dB[k]!)
      if !L.has x && !seen.contains x then
        seen := seen.push x
        let mx := L.mask x
        if popc6 mx == 2 && !isStraightU mx then
          let T := S.push x
          let (K, mins) := canonInfo T
          -- removable circles of T: masks in T = masks in S plus the bit towards x
          let (g0, ma0, mb0) := mins[0]!
          let mut cstar := code syms[g0]! ma0 mb0 x
          for v in S do
            let mut m := L.mask v
            for j in [0:6] do
              if v.1 + dA[j]! == x.1 && v.2 + dB[j]! == x.2 then m := m ||| (1 <<< j.toUInt32)
            if popc6 m == 2 && !isStraightU m then
              let c := code syms[g0]! ma0 mb0 v
              if c < cstar then cstar := c
          if mins.any (fun (g, ma, mb) => code syms[g]! ma mb x == cstar) then
            if !(out.any (·.1 == K)) then out := out.push (K, T)
  return out

/-- Process a chunk of parents: children keys with inherited flags, and statistics. -/
def processChunk (n : Nat) (part : Array (Nat × Bool)) : Array (Nat × Bool) × St := Id.run do
  let mut keys : Array (Nat × Bool) := #[]
  let mut st : St := {}
  for (kS, ir) in part do
    for (K, T) in children (decode2 (n - 1) kS) do
      keys := keys.push (K, ir)
      st := analyze st T K ir false
  return (keys, st)

/-- binary search in an array sorted by key. -/
def memSorted (a : Array (Nat × Bool)) (k : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := a.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let v := a[mid]!.1
    if v == k then return true
    if v < k then lo := mid + 1 else hi := mid
  return false

end RA

namespace RA

/-! ## Second-order rigidity (Connelly–Whiteley), exact over ℚ

In coordinates `(a,b)` the Euclidean inner product is `x ⬝ Q y` with `Q = [[2,1],[1,2]]` (up to
the factor 2). Rigidity matrix rows: edge `ij` has `Q(p_i - p_j)` in the columns of `i` and its
negative in the columns of `j`. -/

def rrefQ (M0 : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) × Array Nat := Id.run do
  let mut M := M0
  let m := M.size
  let mut r := 0
  let mut pivs : Array Nat := #[]
  for col in [0:ncols] do
    if r < m then
      let mut piv := m
      for i in [r:m] do
        if piv == m && M[i]![col]! != 0 then piv := i
      if piv < m then
        let rowP := M[piv]!
        M := (M.set! piv M[r]!).set! r rowP
        let inv := 1 / rowP[col]!
        let rowP := rowP.map (· * inv)
        M := M.set! r rowP
        for i in [0:m] do
          if i != r then
            let f := M[i]![col]!
            if f != 0 then
              M := M.set! i ((M[i]!).zipWith (fun x y => x - f * y) rowP)
        pivs := pivs.push col
        r := r + 1
  return (M.extract 0 r, pivs)

def nullspace (M : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let (R, pivs) := rrefQ M ncols
  let mut out := #[]
  for f in [0:ncols] do
    if !pivs.contains f then
      let mut v := Array.replicate ncols (0 : Rat)
      v := v.set! f 1
      for i in [0:R.size] do
        v := v.set! pivs[i]! (-(R[i]![f]!))
      out := out.push v
  return out

def transpose (M : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) :=
  (List.range ncols).toArray.map fun j => M.map (·[j]!)

@[inline] def qv (d : Rat × Rat) : Rat × Rat := (2 * d.1 + d.2, d.1 + 2 * d.2)

def rigMatQ (pts : Array Pt) (es : Array (Nat × Nat)) : Array (Array Rat) :=
  let n := pts.size
  es.map fun (i, j) =>
    let d : Rat × Rat := ((pts[i]!.1 - pts[j]!.1 : Int), (pts[i]!.2 - pts[j]!.2 : Int))
    let q := qv d
    ((((Array.replicate (2 * n) (0 : Rat)).set! (2*i) q.1).set! (2*i+1) q.2).set! (2*j) (-q.1)).set!
      (2*j+1) (-q.2)

/-- `b(u,v)_ij = (u_i - u_j) ⬝ Q (v_i - v_j)`. -/
def bvec (es : Array (Nat × Nat)) (u v : Array Rat) : Array Rat :=
  es.map fun (i, j) =>
    let du : Rat × Rat := (u[2*i]! - u[2*j]!, u[2*i+1]! - u[2*j+1]!)
    let dv : Rat × Rat := (v[2*i]! - v[2*j]!, v[2*i+1]! - v[2*j+1]!)
    let q := qv dv
    du.1 * q.1 + du.2 * q.2

def dot (x y : Array Rat) : Rat := (x.zipWith (· * ·) y).foldl (· + ·) 0

def rankQ (M : Array (Array Rat)) (ncols : Nat) : Nat := (rrefQ M ncols).2.size

/-- Verdict for a framework that is not infinitesimally rigid. -/
def secondOrder (pts : Array Pt) : String := Id.run do
  let n := pts.size
  let es := contacts pts
  let R := rigMatQ pts es
  let K := nullspace R (2 * n)
  let S := nullspace (transpose R (2 * n)) es.size
  -- trivial motions
  let tr : Array (Array Rat) := #[
    (List.range (2*n)).toArray.map (fun c => if c % 2 == 0 then 1 else 0),
    (List.range (2*n)).toArray.map (fun c => if c % 2 == 1 then 1 else 0),
    (List.range (2*n)).toArray.map (fun c =>
      let p := pts[c / 2]!
      if c % 2 == 0 then ((-p.1 - 2 * p.2 : Int) : Rat) else ((2 * p.1 + p.2 : Int) : Rat))]
  -- complete trivial motions to a basis of K: pick nontrivial representatives
  let mut basis := tr
  let mut nontriv : Array (Array Rat) := #[]
  for v in K do
    if rankQ (basis.push v) (2 * n) > basis.size then
      basis := basis.push v
      nontriv := nontriv.push v
  let k := nontriv.size
  let s := S.size
  if k == 0 then return "infinitesimally rigid?!"
  -- matrices M_t[a][b] = ω_t ⬝ b(u_a, u_b)
  let mats := S.map fun w => nontriv.map fun ua => nontriv.map fun ub => dot w (bvec es ua ub)
  let header := s!"k(nontrivial motions)={k} stresses={s}"
  if k == 1 then
    let vals := mats.map (·[0]![0]!)
    if vals.any (· != 0) then return s!"{header}: SECOND-ORDER RIGID (=> rigid) values={vals.toList}"
    else return s!"{header}: second-order flex exists (undecided)"
  -- k ≥ 2: look for a single stress (basis element or ± sums of two) that is definite
  let definite (M : Array (Array Rat)) : Bool := Id.run do
    -- Sylvester: all leading minors positive (or alternating for negative definite)
    let det (A : Array (Array Rat)) : Rat := Id.run do
      let m := A.size
      let mut A := A
      let mut d : Rat := 1
      for c in [0:m] do
        let mut piv := m
        for i in [c:m] do
          if piv == m && A[i]![c]! != 0 then piv := i
        if piv == m then return 0
        if piv != c then
          let t := A[piv]!; A := (A.set! piv A[c]!).set! c t; d := -d
        let pv := A[c]![c]!
        d := d * pv
        for i in [c+1:m] do
          let f := A[i]![c]! / pv
          A := A.set! i ((A[i]!).zipWith (fun x y => x - f * y) A[c]!)
      return d
    let minors := (List.range M.size).map fun r =>
      det ((M.extract 0 (r+1)).map (·.extract 0 (r+1)))
    return minors.all (· > 0) || (List.range M.size).all fun r =>
      let m := minors[r]!
      if r % 2 == 0 then m < 0 else m > 0
  let mut cands := mats
  for i in [0:mats.size] do
    for j in [i+1:mats.size] do
      cands := cands.push ((mats[i]!).zipWith (fun x y => x.zipWith (· + ·) y) mats[j]!)
      cands := cands.push ((mats[i]!).zipWith (fun x y => x.zipWith (· - ·) y) mats[j]!)
  if cands.any definite then return s!"{header}: PRESTRESS STABLE (=> rigid)"
  return s!"{header}: undecided by prestress search"

end RA

namespace RA

/-! ## Parallel-rotation flexes

Give every circle `v` a *centre* `c(v)` and an *arm* `a(v)` with `c(v) + a(v) = v`, and move it
by `v(θ) = c(v) + R_θ a(v)`. A contact `uv` keeps its length for all `θ` when `c(u) = c(v)` or
`a(u) = a(v)`; the motion changes the distance of `u, v` when `c(u) ≠ c(v)` and `a(u) ≠ a(v)`.
In a triangle all three circles share the centre or all share the arm, so each edge-component of
triangles (a *body*) is a *rotor* (common centre) or a *translator* (common arm). Fixing one body
(a translator with arm 0) loses no generality. Bodies are assigned in BFS order with the finitely
many parameters forced by their links to assigned bodies. The shear flex of `Flex.lean` is the
case "translators only". -/

def bodiesOf (pts : Array Pt) : Array (Array Nat) := Id.run do
  let L := mkLGrid pts
  let idxOf (p : Pt) : Nat := (pts.idxOf? p).getD 0
  let mut tris : Array (Pt × Bool) := #[]
  for p in pts do
    let m := L.mask p
    if m &&& 3 == 3 then tris := tris.push (p, true)
    if m &&& 6 == 6 then tris := tris.push ((p.1-1, p.2), false)
  let comps := triComponents L tris
  let mut out : Array (Array Nat) := #[]
  let mut covered := Array.replicate pts.size false
  for c in comps do
    let mut vs : Array Nat := #[]
    for t in c do
      for v in triVerts t.1 t.2 do
        let i := idxOf v
        if !vs.contains i then vs := vs.push i
        covered := covered.set! i true
    out := out.push vs
  for i in [0:pts.size] do
    if !covered[i]! then out := out.push #[i]
  return out

partial def pfSearch (pts : Array Pt) (es : Array (Nat × Nat)) (bods : Array (Array Nat))
    (order : Array Nat) (k : Nat) (ca : Array (Option (Pt × Pt))) : Bool := Id.run do
  if k == order.size then
    -- nontrivial?
    for i in [0:pts.size] do
      for j in [i+1:pts.size] do
        match ca[i]!, ca[j]! with
        | some (ci, ai), some (cj, aj) => if ci != cj && ai != aj then return true
        | _, _ => pure ()
    return false
  let b := order[k]!
  let vs := bods[b]!
  -- candidate parameters from links to assigned circles
  let mut cands : Array (Bool × Pt) := #[]   -- (isRotor, parameter)
  for v in vs do
    match ca[v]! with
    | some (c, a) => cands := cands ++ #[(true, c), (false, a)]
    | none => pure ()
  for (u, w) in es do
    for (x, y) in [(u, w), (w, u)] do
      if vs.contains y && !vs.contains x then
        match ca[x]! with
        | some (c, a) =>
          let v := pts[y]!
          cands := cands ++ #[(true, c), (false, (v.1 - c.1, v.2 - c.2)),
                              (true, (v.1 - a.1, v.2 - a.2)), (false, a)]
        | none => pure ()
  if k == 0 then cands := #[(false, (0, 0))]
  let mut tried : Array (Bool × Pt) := #[]
  for cand in cands do
    if !tried.contains cand then
      tried := tried.push cand
      let (rot, p) := cand
      let mut ca' := ca
      let mut ok := true
      for v in vs do
        let q := pts[v]!
        let val : Pt × Pt := if rot then (p, (q.1 - p.1, q.2 - p.2)) else ((q.1 - p.1, q.2 - p.2), p)
        match ca'[v]! with
        | some old => if old != val then ok := false
        | none => ca' := ca'.set! v (some val)
      if ok then
        for (u, w) in es do
          match ca'[u]!, ca'[w]! with
          | some (cu, au), some (cw, aw) => if cu != cw && au != aw then ok := false
          | _, _ => pure ()
      if ok && pfSearch pts es bods order (k + 1) ca' then return true
  return false

/-- A nontrivial parallel-rotation flex exists (sufficient for flexibility). -/
def hasParallelFlex (pts : Array Pt) : Bool := Id.run do
  let es := contacts pts
  let bods := bodiesOf pts
  -- BFS order of bodies through shared circles and contacts
  let linked (b c : Nat) : Bool :=
    bods[b]!.any (fun v => bods[c]!.contains v) ||
    es.any fun (u, w) => (bods[b]!.contains u && bods[c]!.contains w) ||
                         (bods[b]!.contains w && bods[c]!.contains u)
  let mut order := #[0]
  let mut i := 0
  while i < order.size do
    for c in [0:bods.size] do
      if !order.contains c && linked order[i]! c then order := order.push c
    i := i + 1
  if order.size < bods.size then return true   -- disconnected: slide a part away
  return pfSearch pts es bods order 0 (Array.replicate pts.size none)

end RA

namespace RA

/-- Solve a 3×3 linear system by Cramer's rule. -/
def solve3 (A : Array (Array Float)) (b : Array Float) : Array Float :=
  let det3 (M : Array (Array Float)) : Float :=
    M[0]![0]! * (M[1]![1]! * M[2]![2]! - M[1]![2]! * M[2]![1]!) -
    M[0]![1]! * (M[1]![0]! * M[2]![2]! - M[1]![2]! * M[2]![0]!) +
    M[0]![2]! * (M[1]![0]! * M[2]![1]! - M[1]![1]! * M[2]![0]!)
  let d := det3 A
  (List.range 3).toArray.map fun j =>
    det3 (A.mapIdx fun i row => row.set! j b[i]!) / d

/-- Least squares for `log a(n) = c + n log μ + θ log n` over `n ∈ [lo, hi]`; returns `(μ, θ)`. -/
def fitMuTheta (a : Array Nat) (lo hi : Nat) : Float × Float := Id.run do
  let mut A := #[#[0.0, 0.0, 0.0], #[0.0, 0.0, 0.0], #[0.0, 0.0, 0.0]]
  let mut b := #[0.0, 0.0, 0.0]
  for n in [lo:hi+1] do
    let x : Array Float := #[1.0, n.toFloat, Float.log n.toFloat]
    let y := Float.log (a[n-1]!).toFloat
    for i in [0:3] do
      b := b.set! i (b[i]! + x[i]! * y)
      for j in [0:3] do
        A := A.set! i (A[i]!.set! j (A[i]![j]! + x[i]! * x[j]!))
  let s := solve3 A b
  return (Float.exp s[1]!, s[2]!)

/-- Ratio table: `r_n = a(n)/a(n-1)`; two-step extrapolation `μ_n² = (n q_n − (n−2) q_{n−2})/2`
with `q_n = a(n)/a(n−2)` (cancels the even/odd oscillation, removes the `1/n` term). -/
def ratioTable (a : Array Nat) : String := Id.run do
  let f (n : Nat) : Float := (a[n-1]!).toFloat
  let mut s := "n | a(n) | a(n)/a(n-1) | sqrt(a(n)/a(n-2)) | mu_n (extrapolated)\n"
  for n in [2:a.size+1] do
    let r := f n / f (n-1)
    let q := if n ≥ 3 then Float.sqrt (f n / f (n-2)) else 0
    let mu := if n ≥ 7 then
      let qn := f n / f (n-2)
      let qm := f (n-2) / f (n-4)
      Float.sqrt ((n.toFloat * qn - (n.toFloat - 2) * qm) / 2) else 0
    s := s ++ s!"{n} | {a[n-1]!} | {r} | {q} | {mu}\n"
  return s

end RA

namespace RA

/-! ## Higher-order analysis (exact, over ℚ, metric `Q` in lattice coordinates) -/

/-- particular solution of `M x = rhs` with free variables 0 (none if inconsistent). -/
def solveQ (M : Array (Array Rat)) (rhs : Array Rat) (ncols : Nat) : Option (Array Rat) := Id.run do
  let aug := (List.range M.size).toArray.map fun i => M[i]!.push rhs[i]!
  let (R, pivs) := rrefQ aug (ncols + 1)
  if pivs.contains ncols then return none
  let mut x := Array.replicate ncols (0 : Rat)
  for i in [0:R.size] do
    x := x.set! pivs[i]! R[i]![ncols]!
  return some x

/-- gauge rows: fix circle 0 and the rotation about it. -/
def gaugeRows (pts : Array Pt) : Array (Array Rat) :=
  let n := pts.size
  let d : Pt := (pts[1]!.1 - pts[0]!.1, pts[1]!.2 - pts[0]!.2)
  let vd : Rat × Rat := (((-d.1 - 2 * d.2 : Int)) , ((2 * d.1 + d.2 : Int)))   -- rotation velocity
  let qv' := qv vd
  #[ (Array.replicate (2*n) (0 : Rat)).set! 0 1,
     (Array.replicate (2*n) (0 : Rat)).set! 1 1,
     ((Array.replicate (2*n) (0 : Rat)).set! 2 qv'.1).set! 3 qv'.2 ]

/-- Series of the bifurcation function for a framework whose gauge-fixed kernel is
one-dimensional: returns `(g_2, …, g_maxOrd)` for each stress, where
`G(s) = Σ g_k s^k`, `g_k = ω ⬝ Σ_{i+j=k} B(a_i, a_j)` and `2 R a_k = -P(Σ B(a_i,a_j))`. -/
def bifurcation (pts : Array Pt) (maxOrd : Nat) : String := Id.run do
  let n := pts.size
  let es := contacts pts
  let R := rigMatQ pts es
  let G := gaugeRows pts
  let K := nullspace (R ++ G) (2 * n)
  let S := nullspace (transpose R (2 * n)) es.size
  if K.size != 1 then return s!"gauge-fixed kernel has dim {K.size}"
  let u := K[0]!
  let proj (v : Array Rat) : Array Rat := Id.run do
    -- orthogonal projection onto the complement of the stress space (Gram–Schmidt)
    let mut basis : Array (Array Rat) := #[]
    for w in S do
      let mut w' := w
      for b in basis do
        w' := w'.zipWith (fun x y => x - (dot w b / dot b b) * y) b
      basis := basis.push w'
    let mut r := v
    for b in basis do
      r := r.zipWith (fun x y => x - (dot v b / dot b b) * y) b
    return r
  let two : Rat := 2
  let M := (R.map (·.map (· * two))) ++ G
  let mut as : Array (Array Rat) := #[u]       -- a_1 = u
  let mut out := ""
  for k in [2:maxOrd+1] do
    let mut rhs := Array.replicate es.size (0 : Rat)
    for i in [1:k] do
      let j := k - i
      rhs := rhs.zipWith (· + ·) (bvec es as[i-1]! as[j-1]!)
    let gs := S.map (fun w => dot w rhs)
    out := out ++ s!" g{k}={gs.toList}"
    if gs.any (· != 0) then return s!"RIGID (bifurcation function has nonzero coefficient of order {k}):{out}"
    let pr := proj rhs
    match solveQ M ((pr.map (fun x => -x)) ++ #[0, 0, 0]) (2 * n) with
    | some a => as := as.push a
    | none => return s!"inconsistent at order {k}?!{out}"
  return s!"all coefficients vanish up to order {maxOrd}:{out}"

/-- For `T' = T minus the straight degree-2 circles`: regularity, motion dimension, and the
first-order and second-order change of each removed span `|a - b|²` along each basis motion. -/
def cableAnalysis (pts : Array Pt) : String := Id.run do
  let L := mkLGrid pts
  let straight := pts.filter (fun p => isStraightU (L.mask p))
  let rest := pts.filter (fun p => !isStraightU (L.mask p))
  let n := rest.size
  let es := contacts rest
  let R := rigMatQ rest es
  let G := gaugeRows rest
  let K := nullspace (R ++ G) (2 * n)
  let (rk, gr) := ranks rest
  let mut out := s!"T' = T minus {straight.toList}: n'={n} rank={rk} generic={gr} regular={rk == gr} gauge-fixed motion dim={K.size}"
  let idx (p : Pt) : Nat := (rest.idxOf? p).getD 0
  for w in straight do
    let m := L.mask w
    let ks := (List.range 6).filter (fun (k : Nat) => m &&& ((1 : UInt32) <<< k.toUInt32) != 0)
    let a : Pt := (w.1 + dA[ks[0]!]!, w.2 + dB[ks[0]!]!)
    let b : Pt := (w.1 + dA[ks[1]!]!, w.2 + dB[ks[1]!]!)
    let (ia, ib) := (idx a, idx b)
    let dp : Rat × Rat := ((a.1 - b.1 : Int), (a.2 - b.2 : Int))
    let grad := K.map fun u =>
      let du : Rat × Rat := (u[2*ia]! - u[2*ib]!, u[2*ia+1]! - u[2*ib+1]!)
      let q := qv du
      dp.1 * q.1 + dp.2 * q.2
    out := out ++ s!"\n   span {a}-{b} (via {w}): first-order change along motion basis = {grad.toList}"
  return out

end RA

namespace RA

/-- For `T'` (gauge-fixed kernel of dim 1, regular), the Taylor coefficients of
`|a(s) - b(s)|²_Q - |a - b|²_Q` along the curve of configurations `x(s) = p + Σ s^k a_k`. -/
def spanSeries (pts : Array Pt) (a b : Pt) (maxOrd : Nat) : String := Id.run do
  let n := pts.size
  let es := contacts pts
  let R := rigMatQ pts es
  let G := gaugeRows pts
  let K := nullspace (R ++ G) (2 * n)
  let S := nullspace (transpose R (2 * n)) es.size
  if K.size != 1 then return s!"gauge-fixed kernel has dim {K.size}"
  let proj (v : Array Rat) : Array Rat := Id.run do
    let mut basis : Array (Array Rat) := #[]
    for w in S do
      let mut w' := w
      for bb in basis do
        w' := w'.zipWith (fun x y => x - (dot w bb / dot bb bb) * y) bb
      basis := basis.push w'
    let mut r := v
    for bb in basis do
      r := r.zipWith (fun x y => x - (dot v bb / dot bb bb) * y) bb
    return r
  let two : Rat := 2
  let M := (R.map (·.map (· * two))) ++ G
  let ia := (pts.idxOf? a).getD 0
  let ib := (pts.idxOf? b).getD 0
  let dp : Rat × Rat := ((a.1 - b.1 : Int), (a.2 - b.2 : Int))
  let dl (v : Array Rat) : Rat × Rat := (v[2*ia]! - v[2*ib]!, v[2*ia+1]! - v[2*ib+1]!)
  let ip (x y : Rat × Rat) : Rat := let q := qv y; x.1 * q.1 + x.2 * q.2
  let mut as : Array (Array Rat) := #[K[0]!]
  let mut out := ""
  for k in [2:maxOrd+1] do
    let mut rhs := Array.replicate es.size (0 : Rat)
    for i in [1:k] do
      rhs := rhs.zipWith (· + ·) (bvec es as[i-1]! as[k-i-1]!)
    let gs := S.map (fun w => dot w rhs)
    if gs.any (· != 0) then return s!"obstruction at order {k}: {gs.toList} (T' not regular?)"
    match solveQ M ((proj rhs).map (fun x => -x) ++ #[0, 0, 0]) (2 * n) with
    | some x => as := as.push x
    | none => return "inconsistent"
  -- span coefficients: order k: 2 Δp·QΔa_k + Σ_{i+j=k} Δa_i·QΔa_j
  for k in [1:maxOrd+1] do
    let mut c := 2 * ip dp (dl as[k-1]!)
    for i in [1:k] do
      c := c + ip (dl as[i-1]!) (dl as[k-i-1]!)
    out := out ++ s!" f{k}={c}"
  return out

end RA

/-! ## Classification of core candidates -/

namespace RA

structure CoreRes where
  key : Nat
  rigid : Bool := false
  infRigid : Bool := false
  inExt : Bool := false
  kind : String := ""        -- infRigid | singularHenneberg | singular2ndOrder | flexCutShear |
                             -- flexAsimowRoth | flexParallel | UNDECIDED
  conflict : Bool := false   -- a rigidity certificate and a flex certificate both hold
  line : String := ""

/-- Classify one core candidate (connected, min degree ≥ 2, no removable circle). -/
def classifyCore (n : Nat) (prev : Array (Nat × Bool)) (k : Nat) : CoreRes := Id.run do
  let pts := decode2 n k
  let ir := infRigid pts
  let inExt := (List.range n).any fun i => memSorted prev (canonKey2 (pts.eraseIdx! i))
  if ir || inExt then
    return { key := k, rigid := true, infRigid := ir, inExt,
             kind := if ir then "infRigid" else "singularHenneberg",
             line := s!"core n={n} infRigid={ir} irreducible={!inExt} {showPts pts}" }
  let cs := hasCutCircle pts || hasShear pts
  let (rk, gr) := ranks pts
  let ar := rk == gr
  let pf := hasParallelFlex pts
  -- the second-order test is run whenever p is not a regular point (and as a control otherwise)
  let so := secondOrder pts
  let soRigid := (so.splitOn "=> rigid").length > 1
  let flex := cs || ar || pf
  let conflict := soRigid && flex
  if flex then
    return { key := k, kind := if cs then "flexCutShear" else if ar then "flexAsimowRoth" else "flexParallel",
             conflict, line := s!"flexible core candidate n={n} cutShear={cs} AR={ar} parallel={pf} rank={rk} generic={gr} {showPts pts}" }
  if soRigid then
    return { key := k, rigid := true, kind := "singular2ndOrder",
             line := s!"irreducible core n={n} SINGULAR rank={rk} generic={gr} 2n-3={2*n-3}: {so} {showPts pts}" }
  return { key := k, kind := "UNDECIDED",
           line := s!"UNDECIDED n={n} rank={rk} generic={gr} 2n-3={2*n-3}: {so} {showPts pts}" }

end RA

/-! ## Command-line driver -/

open RA in
/-- Validation: unpruned Redelmeier (all fixed polyhexes) against the pruned searches. -/
def polyhexMode (hi : Nat) : IO Unit := do
  for N in [2:hi+1] do
    let t0 ← IO.monoMsNow
    let (accU, fu) := runSearch N false
    let t1 ← IO.monoMsNow
    let (accP, fp) := runSearch N true
    let (nodes2, f2) := runSearchPar N (if N ≥ 12 then 9 else 0) 8 64
    let t2 ← IO.monoMsNow
    let free (f : Array (Array Pt)) := ((f.map canonKey).qsort (· < ·)).toList.eraseDups.length
    IO.println s!"N={N} fixedPolyhexes={accU.leaves} coreCandidates: unpruned fixed {fu.size} free {free fu} | pruned fixed {fp.size} free {free fp} (nodes {accP.nodes}) | parallel fixed {f2.size} free {free f2} (nodes {nodes2}) | ms unpruned {t1-t0}, pruned {t2-t1}"
    (← IO.getStdout).flush

open RA in
/-- Cross-check: all extensions by a site touching ≥ 2 sites, global hash set, exact ranks. -/
def hashMode (maxN : Nat) : IO Unit := do
  let mut prev : Level := HashMap.emptyWithCapacity 4 |>.insert (canonKey #[(0,0),(1,0)]) true
  let mut counts : Array Nat := #[1, 1]
  let mut sings : Array Nat := #[0, 0]
  for n in [3:maxN+1] do
    let t0 ← IO.monoMsNow
    let ext := extendLevelPar n prev 64
    let (_, fixedCands) := runSearchPar n (if n ≥ 12 then 9 else 0) 8 64
    let candKeys := ((fixedCands.map canonKey).qsort (· < ·)).toList.eraseDups
    let mut level := ext
    let mut undec := 0
    for k in candKeys do
      let pts := decode n k
      if infRigid pts then level := level.insert k true
      else if ext.contains k then pure ()
      else if hasCutCircle pts || hasShear pts || hasParallelFlex pts then pure ()
      else
        let (rk, gr) := ranks pts
        if rk != gr then
          if ((secondOrder pts).splitOn "=> rigid").length > 1 then level := level.insert k false
          else undec := undec + 1
    for (k, v) in ext do
      if !v then level := level.insert k (infRigid (decode n k))
    let nsing := level.fold (fun acc _ v => if v then acc else acc + 1) 0
    let t1 ← IO.monoMsNow
    counts := counts.push level.size
    sings := sings.push nsing
    IO.println s!"[hash] n={n} rigid={level.size} singular={nsing} undecided={undec} ({t1-t0} ms)"
    (← IO.getStdout).flush
    prev := level
  IO.println s!"[hash] counts {counts}"
  IO.println s!"[hash] singular {sings}"

open RA in
/-- Main enumeration: orderly generation + core search + exact classification of cores. -/
def orderlyMode (maxN : Nat) (nChunks : Nat) : IO Unit := do
  let mut prev : Array (Nat × Bool) := #[(canonKey2 #[(0,0),(1,0)], true)]
  let mut counts : Array Nat := #[1, 1]
  for n in [3:maxN+1] do
    let t0 ← IO.monoMsNow
    let mut tasks : Array (Task (Array (Nat × Bool) × St)) := #[]
    for t in [0:nChunks] do
      let part := (List.range ((prev.size + nChunks - 1 - t) / nChunks)).toArray.map
        fun j => prev[t + j * nChunks]!
      tasks := tasks.push <| Task.spawn fun _ => processChunk n part
    let mut keys : Array (Nat × Bool) := #[]
    let mut st : St := {}
    for t in tasks do
      let (k, s) := t.get
      keys := keys ++ k
      st := st.merge s
    let nExt := keys.size
    let t1 ← IO.monoMsNow
    let (nodes, fixedCands) := runSearchPar n (if n ≥ 12 then 9 else 0) 8 64
    let candKeys := ((fixedCands.map canonKey2).qsort (· < ·)).toList.eraseDups.toArray
    let t2 ← IO.monoMsNow
    let pv := prev
    let mut ctasks : Array (Task (Array CoreRes)) := #[]
    for t in [0:nChunks] do
      let part := (List.range ((candKeys.size + nChunks - 1 - t) / nChunks)).toArray.map
        fun j => candKeys[t + j * nChunks]!
      ctasks := ctasks.push <| Task.spawn fun _ => part.map (classifyCore n pv)
    let mut kinds : HashMap String Nat := {}
    let mut nIrr := 0
    let mut nConf := 0
    let mut lines : Array String := #[]
    for t in ctasks do
      for r in t.get do
        kinds := kinds.insert r.kind (kinds.getD r.kind 0 + 1)
        if r.conflict then
          nConf := nConf + 1
          lines := lines.push s!"  CONFLICT {r.line}"
        if r.rigid then
          keys := keys.push (r.key, r.infRigid)
          st := analyze st (decode2 n r.key) r.key r.infRigid true
          if !r.inExt then nIrr := nIrr + 1
          if !r.inExt || !r.infRigid || n ≤ 16 then lines := lines.push s!"  {r.line}"
        else if r.kind == "UNDECIDED" || r.kind == "flexParallel" then lines := lines.push s!"  {r.line}"
    let t3 ← IO.monoMsNow
    keys := keys.qsort (fun a b => a.1 < b.1)
    let t4 ← IO.monoMsNow
    let a := keys.size
    counts := counts.push a
    let kstr := " ".intercalate ((kinds.toList.toArray.qsort (fun x y => x.1 < y.1)).toList.map
      fun (s, c) => s!"{s}={c}")
    IO.println s!"n={n} rigid={a} withRemovable={nExt} rigidCores={a - nExt} irreducibleCores={nIrr} coreCandidates={candKeys.size} (fixed {fixedCands.size}, search nodes {nodes}) [{kstr}] conflicts={nConf}"
    IO.println s!"   singular={st.sing} (with straight deg-2 circle: {st.singStraight}) saturatedPolyiamondCorners={st.sat} nonSaturatedPolyiamondCorners={st.pcNonSat} allInTrianglesNotPolyiamond={st.covNoPC} circleInNoTriangle={st.gap} coresCounted={st.cores}"
    IO.println s!"   contacts: {histStr st.hE}"
    IO.println s!"   triangles: {histStr st.hT}"
    IO.println s!"   time ms: generate={t1-t0} coreSearch={t2-t1} coreClassify={t3-t2} sort={t4-t3}"
    for l in lines do IO.println l
    for (nm, ex) in [("gap", st.exGap), ("coveredNotPolyiamond", st.exCov), ("nonSatPolyiamond", st.exPC), ("singular", st.exSing)] do
      for k in ex.extract 0 3 do IO.println s!"  example {nm} n={n} {showPts (decode2 n k)}"
    (← IO.getStdout).flush
    prev := keys
  IO.println s!"counts n=1..{maxN}: {counts}"
  IO.println (ratioTable counts)
  for lo in [12, 14, 16, 18] do
    if lo + 4 ≤ counts.size then
      let (mu, th) := fitMuTheta counts lo counts.size
      IO.println s!"LSQ fit of log a(n) = c + n log mu + theta log n over n={lo}..{counts.size}: mu={mu} theta={th}"

open RA in
/-- Controls: the second-order test and the parallel-flex test against known answers. -/
def controlsMode (hi : Nat) : IO Unit := do
  let sing18 : Array Pt := #[(-1, 1), (0, 0), (-1, 0), (-2, 1), (-2, 2), (-1, 2), (-2, 3), (-1, 3),
    (0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (2, 1), (3, 1), (3, 0), (2, 0), (1, 0)]
  IO.println s!"sing18 (repo, rigid): rank={rigRank sing18}/{2*18-3} generic={genericRank 18 (contacts sing18)} {secondOrder sing18}; parallel flex: {hasParallelFlex sing18}"
  -- (1) core candidates proven flexible (cut/shear/Asimow–Roth) must not be second-order rigid
  let mut bad := 0
  let mut tested := 0
  let mut pfFound := 0
  for n in [10:hi+1] do
    let (_, fixed) := runSearchPar n (if n ≥ 12 then 9 else 0) 8 64
    let keys := ((fixed.map canonKey).qsort (· < ·)).toList.eraseDups
    for k in keys do
      let pts := decode n k
      if !infRigid pts && (hasCutCircle pts || hasShear pts || (let (r, g) := ranks pts; r == g)) then
        tested := tested + 1
        if hasParallelFlex pts then pfFound := pfFound + 1
        if ((secondOrder pts).splitOn "=> rigid").length > 1 then
          bad := bad + 1
          IO.println s!"BAD n={n} {showPts pts}"
  IO.println s!"(1) n=10..{hi}: {tested} flexible core candidates; second-order test wrongly says rigid for {bad}; parallel-flex test also finds a flex for {pfFound}"
  -- (2) no rigid set (orderly generation) may have a parallel flex
  let mut prev : Array (Nat × Bool) := #[(canonKey2 #[(0,0),(1,0)], true)]
  let mut badPF := 0
  let mut total := 0
  for n in [3:hi+1] do
    let (ks, _) := processChunk n prev
    let mut lvl := ks
    let (_, fixedCands) := runSearchPar n (if n ≥ 12 then 9 else 0) 8 64
    for k in ((fixedCands.map canonKey2).qsort (· < ·)).toList.eraseDups do
      let r := classifyCore n prev k
      if r.rigid then lvl := lvl.push (k, r.infRigid)
    for (k, _) in lvl do
      total := total + 1
      if hasParallelFlex (decode2 n k) then badPF := badPF + 1
    prev := lvl.qsort (fun a b => a.1 < b.1)
  IO.println s!"(2) n=3..{hi}: {total} rigid sets; parallel-flex test wrongly finds a flex for {badPF}"


open RA in
/-- Exact decision of the four candidates left UNDECIDED by `orderly 25`. -/
def decide25Mode : IO Unit := do
  let U1 : Array Pt := #[(5,3), (5,2), (4,4), (4,3), (4,2), (4,1), (4,0), (3,4), (3,2), (3,1), (3,0), (2,5), (2,4), (2,3), (2,0), (1,5), (1,4), (1,3), (1,2), (1,1), (1,0), (0,4), (0,3), (0,2), (0,1)]
  let U2 : Array Pt := #[(5,3), (5,2), (5,1), (5,0), (4,4), (4,3), (4,2), (4,1), (4,0), (3,4), (3,1), (2,5), (2,4), (2,3), (2,2), (2,1), (1,6), (1,5), (1,2), (1,1), (0,6), (0,5), (0,4), (0,3), (0,2)]
  let U3 : Array Pt := #[(5,2), (5,1), (5,0), (4,3), (4,2), (4,1), (4,0), (3,4), (3,3), (3,1), (3,0), (2,5), (2,4), (2,2), (2,0), (1,5), (1,4), (1,3), (1,1), (1,0), (0,5), (0,4), (0,3), (0,2), (0,1)]
  let U4 : Array Pt := #[(5,3), (5,2), (5,1), (4,4), (4,3), (4,2), (4,1), (4,0), (3,5), (3,4), (3,2), (3,1), (3,0), (2,5), (2,3), (2,1), (2,0), (1,5), (1,4), (1,2), (1,1), (0,5), (0,4), (0,3), (0,2)]
  let S20 : Array Pt := #[(4,3), (4,2), (4,1), (3,4), (3,3), (3,2), (3,1), (3,0), (2,4), (2,2), (2,1), (2,0), (1,4), (1,3), (1,1), (1,0), (0,4), (0,3), (0,2), (0,1)]
  let F24 : Array Pt := #[(5,2), (5,1), (5,0), (4,3), (4,2), (4,1), (4,0), (3,4), (3,2), (3,0), (2,5), (2,4), (2,3), (2,2), (2,1), (2,0), (1,5), (1,4), (1,2), (1,1), (0,5), (0,4), (0,3), (0,2)]
  IO.println s!"control S20 (second-order rigid): {bifurcation S20 6}"
  IO.println s!"control F24 (parallel flex, flexible): {bifurcation F24 8}"
  IO.println s!"U1: {bifurcation U1 8}"
  let st := analyze {} U1 0 false true
  IO.println s!"U1 statistics: contacts {histStr st.hE} triangles {histStr st.hT} sat={st.sat} covNoPC={st.covNoPC} gap={st.gap}"
  IO.println s!"U2: {cableAnalysis U2}"
  IO.println s!"U3: {cableAnalysis U3}"
  IO.println s!"U3: span (1,3)-(3,1) along T' = U3 - (2,2): {spanSeries (U3.filter (· != (2,2))) (1,3) (3,1) 4}"
  IO.println s!"U4: {cableAnalysis U4}"
  IO.println s!"U4: span (1,4)-(3,2) along T' = U4 - (2,3): {spanSeries (U4.filter (· != (2,3))) (1,4) (3,2) 4}"

def main (args : List String) : IO Unit := do
  match args with
  | ["polyhex", n] => polyhexMode n.toNat!
  | ["hash", n] => hashMode n.toNat!
  | ["orderly", n] => orderlyMode n.toNat! 64
  | ["controls", n] => controlsMode n.toNat!
  | ["decide25"] => decide25Mode
  | _ => IO.println "usage: polyhex N | hash N | orderly N | controls N | decide25"

-- The `#eval` route (interpreted; small n only). The compiled binary runs the large cases.
#eval main ["orderly", "13"]
