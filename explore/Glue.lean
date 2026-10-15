import Std.Data.HashSet
import Std.Data.HashMap
open Std
/-! Exploratory check of the lattice concatenation lemma behind a Fekete argument.
Fixed rigid lattice sets (translation classes), lex order on (b, a). A ≤ t := lexmax A,
B ≥ s := lexmin B. Hinge-glue: translate B so s ↦ t. If some contact joins A∖t and B'∖t,
the union is rigid (hinge-and-bar lemma). Otherwise add one connector circle next to t. -/

abbrev Pt := Int × Int
def dA : Array Int := #[1, 0, -1, -1, 0, 1]
def dB : Array Int := #[0, 1, 1, 0, -1, -1]
def lexLt (p q : Pt) : Bool := p.2 < q.2 || (p.2 == q.2 && p.1 < q.1)
def touch (p q : Pt) : Bool :=
  let x := p.1 - q.1; let y := p.2 - q.2; x*x + x*y + y*y == 1
def norm (s : Array Pt) : Array Pt :=
  let s := s.qsort lexLt
  let o := s[0]!
  s.map (fun p => (p.1 - o.1, p.2 - o.2))

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
            if j > col then nr := nr.set! j ((pv * rowI[j]! - f * rowP[j]!) / prev)
          nr := nr.set! col 0
          M := M.set! i nr
        prev := pv
        r := r + 1
  return r

def rigRank (pts : Array Pt) : Nat := Id.run do
  let n := pts.size
  let mut rows : Array (Array Int) := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      if touch pts[i]! pts[j]! then
        let x := pts[i]!.1 - pts[j]!.1
        let y := pts[i]!.2 - pts[j]!.2
        rows := rows.push ((((Array.replicate (2*n) (0:Int)).set! (2*i) x).set! (2*i+1) y).set! (2*j) (-x) |>.set! (2*j+1) (-y))
  return intRank rows (2*n)

/-- fixed rigid sets of size 3..N by closure under adding a site touching ≥ 2 sites (valid as
the full class for N ≤ 13 by the exploratory census; here only used as test data). -/
def levels (N : Nat) : Array (Array (Array Pt)) := Id.run do
  let tri1 : Array Pt := norm #[(0,0),(1,0),(0,1)]
  let tri2 : Array Pt := norm #[(1,0),(0,1),(1,1)]
  let mut lv : Array (Array (Array Pt)) := #[#[], #[], #[], #[tri1, tri2]]
  for n in [4:N+1] do
    let mut seen : HashSet (Array Pt) := {}
    let mut out := #[]
    for S in lv[n-1]! do
      for p in S do
        for k in [0:6] do
          let x : Pt := (p.1 + dA[k]!, p.2 + dB[k]!)
          if !S.contains x && (S.filter (touch x)).size ≥ 2 then
            let T := norm (S.push x)
            if !seen.contains T then
              seen := seen.insert T; out := out.push T
    lv := lv.push out
  return lv

def glue (A B : Array Pt) : String × Array Pt := Id.run do
  let t := A.back!          -- lexmax (A sorted)
  let B' := B.map (fun p => (p.1 + t.1, p.2 + t.2))   -- B normalized: lexmin at origin
  let has (S : Array Pt) (d : Pt) : Bool := S.contains (t.1 + d.1, t.2 + d.2)
  let L : Pt := (-1,0); let D : Pt := (0,-1); let DR : Pt := (1,-1)
  let R : Pt := (1,0); let U : Pt := (0,1); let UL : Pt := (-1,1)
  let cross := A.any (fun x => x != t && B'.any (fun y => y != t && touch x y))
  let C := (A ++ B'.filter (· != t))
  if cross then return ("hinge", C)
  -- failing cases
  if has A L && has A D && !has A DR && has B' R && has B' U && !has B' UL then
    return ("connDR", C.push (t.1 + DR.1, t.2 + DR.2))
  if !has A L && has A D && has A DR && !has B' R && has B' U && has B' UL then
    return ("connL", C.push (t.1 + L.1, t.2 + L.2))
  return ("FAIL", C)

def main (args : List String) : IO Unit := do
  let N := (args.headD "8").toNat!
  let lv := levels N
  IO.println s!"fixed counts 3..{N}: {(List.range (N-2)).map (fun i => lv[i+3]!.size)}"
  -- monotonicity injection
  for n in [3:N] do
    let mut imgs : HashSet (Array Pt) := {}
    let mut bad := 0
    for S in lv[n]! do
      let t := S.back!
      let x : Pt := if S.contains (t.1 - 1, t.2) then (t.1 - 1, t.2 + 1) else (t.1 + 1, t.2)
      let T := S.push x
      if (T.filter (touch x)).size < 2 || T.any (fun p => p != x && !lexLt p x) then bad := bad + 1
      imgs := imgs.insert (norm T)
    IO.println s!"monotone n={n}->{n+1}: {lv[n]!.size} sets, distinct images {imgs.size}, bad {bad}"
  for m in [3:N+1] do
    for n in [3:N+1] do
      if m + n ≤ N + 6 then
        let mut cnt : HashMap String Nat := {}
        let mut imgs : HashMap String (HashSet (Array Pt)) := {}
        let mut deficient := 0
        let mut overlap := 0
        for A in lv[m]! do
          for B in lv[n]! do
            let (k, C) := glue A B
            cnt := cnt.insert k (cnt.getD k 0 + 1)
            let Cn := norm C
            if (Cn.toList.eraseDups).length != C.size then overlap := overlap + 1
            imgs := imgs.insert k ((imgs.getD k {}).insert Cn)
            if rigRank C != 2 * C.size - 3 then deficient := deficient + 1
        let ks := cnt.toList.map (fun (k, v) => s!"{k}:{v} (distinct {(imgs.getD k {}).size})")
        IO.println s!"m={m} n={n} pairs={lv[m]!.size * lv[n]!.size} {ks} rankDeficient={deficient} overlaps={overlap}"
