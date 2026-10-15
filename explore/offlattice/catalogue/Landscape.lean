namespace OL

/-! # Float linear algebra -/

abbrev Mat := Array (Array Float)

/-- solve `M x = b` (square) by Gaussian elimination with partial pivoting; `none` if singular. -/
def solveSq (M : Mat) (b : Array Float) : Option (Array Float) := Id.run do
  let n := M.size
  let mut A := M
  let mut r := b
  for c in [0:n] do
    let mut piv := c
    let mut best := (A[c]![c]!).abs
    for i in [c+1:n] do
      if (A[i]![c]!).abs > best then
        best := (A[i]![c]!).abs
        piv := i
    if best < 1e-14 then return none
    if piv != c then
      let t := A[piv]!
      A := A.set! piv A[c]!
      A := A.set! c t
      let tb := r[piv]!
      r := r.set! piv r[c]!
      r := r.set! c tb
    let rowC := A[c]!
    let pv := rowC[c]!
    for i in [c+1:n] do
      let rowI := A[i]!
      let f := rowI[c]! / pv
      if f != 0 then
        let mut nr := rowI
        for j in [c:n] do
          nr := nr.set! j (rowI[j]! - f * rowC[j]!)
        A := A.set! i nr
        r := r.set! i (r[i]! - f * r[c]!)
  -- back substitution
  let mut x := Array.replicate n 0.0
  for ii in [0:n] do
    let i := n - 1 - ii
    let mut s := r[i]!
    for j in [i+1:n] do
      s := s - A[i]![j]! * x[j]!
    x := x.set! i (s / A[i]![i]!)
  return some x

/-- rank and (if exactly one free column) a null vector, by RREF with partial pivoting. -/
def rrefNull (M : Mat) (ncols : Nat) (tolr : Float := 1e-9) : Nat × Option (Array Float) := Id.run do
  let m := M.size
  let mut A := M
  let mut r := 0
  let mut pivCols : Array Nat := #[]
  for c in [0:ncols] do
    if r < m then
      let mut piv := r
      let mut best := (A[r]![c]!).abs
      for i in [r+1:m] do
        if (A[i]![c]!).abs > best then
          best := (A[i]![c]!).abs
          piv := i
      if best > tolr then
        let t := A[piv]!
        A := A.set! piv A[r]!
        A := A.set! r t
        let pv := A[r]![c]!
        let rowR := A[r]!.map (· / pv)
        A := A.set! r rowR
        for i in [0:m] do
          if i != r then
            let rowI := A[i]!
            let f := rowI[c]!
            if f != 0 then
              let mut nr := rowI
              for j in [c:ncols] do
                nr := nr.set! j (rowI[j]! - f * rowR[j]!)
              A := A.set! i nr
        pivCols := pivCols.push c
        r := r + 1
  if r + 1 != ncols then return (r, none)
  -- free column
  let mut free := ncols
  for c in [0:ncols] do
    if free == ncols && !pivCols.contains c then free := c
  let mut v := Array.replicate ncols 0.0
  v := v.set! free 1.0
  for i in [0:r] do
    v := v.set! pivCols[i]! (-(A[i]![free]!))
  return (r, some v)

def vnorm (v : Array Float) : Float := Float.sqrt (v.foldl (fun s x => s + x * x) 0)
def vdot (v w : Array Float) : Float := Id.run do
  let mut s := 0.0
  for i in [0:v.size] do s := s + v[i]! * w[i]!
  return s

/-! # Mechanisms -/

/-- flatten points -/
def flat (P : Array CF) : Array Float := Id.run do
  let mut x := #[]
  for p in P do
    x := x.push p.x
    x := x.push p.y
  return x
def unflat (x : Array Float) : Array CF := Id.run do
  let mut P := #[]
  for i in [0:x.size / 2] do P := P.push ⟨x[2*i]!, x[2*i+1]!⟩
  return P

/-- constraint rows: contacts (gradient of |pi - pj|^2) and 3 pin rows (point a fixed, b's
rotation about a fixed). -/
def jacRows (x : Array Float) (E : Array (Nat × Nat)) (a b : Nat) : Mat := Id.run do
  let N := x.size
  let mut M : Mat := #[]
  for (i, j) in E do
    let dx := x[2*i]! - x[2*j]!
    let dy := x[2*i+1]! - x[2*j+1]!
    let mut row := Array.replicate N 0.0
    row := row.set! (2*i) (2*dx)
    row := row.set! (2*i+1) (2*dy)
    row := row.set! (2*j) (-2*dx)
    row := row.set! (2*j+1) (-2*dy)
    M := M.push row
  let r1 := (Array.replicate N 0.0).set! (2*a) 1.0
  let r2 := (Array.replicate N 0.0).set! (2*a+1) 1.0
  let ex := x[2*b]! - x[2*a]!
  let ey := x[2*b+1]! - x[2*a+1]!
  let r3 := ((Array.replicate N 0.0).set! (2*b) (-ey)).set! (2*b+1) ex
  return M.push r1 |>.push r2 |>.push r3

def resid (x : Array Float) (E : Array (Nat × Nat)) : Array Float :=
  E.map fun (i, j) =>
    let dx := x[2*i]! - x[2*j]!
    let dy := x[2*i+1]! - x[2*j+1]!
    dx * dx + dy * dy - 1

/-- tangent of the 1-DOF mechanism (unit), or none -/
def tangent (x : Array Float) (E : Array (Nat × Nat)) (a b : Nat) : Option (Array Float) :=
  let M := jacRows x E a b
  match rrefNull M x.size with
  | (_, some v) => let nv := vnorm v; some (v.map (· / nv))
  | _ => none

/-- Newton projection onto `E` (with pins and orthogonality to `t`), least-norm steps. -/
def newtonProj (x0 : Array Float) (E : Array (Nat × Nat)) (a b : Nat) (t : Option (Array Float))
    (maxIt : Nat := 12) : Option (Array Float) := Id.run do
  let mut x := x0
  for _ in [0:maxIt] do
    let g := resid x E
    let err := g.foldl (fun s v => max s v.abs) 0
    if err < 1e-13 then return some x
    let J0 := jacRows x E a b
    let J := match t with
      | some tv => J0.push tv
      | none => J0
    let rhs := g ++ (Array.replicate (J.size - g.size) 0.0)
    -- (J J^T + λ I) y = rhs ; Δ = -J^T y
    let m := J.size
    let mut G : Mat := Array.replicate m (Array.replicate m 0.0)
    for i in [0:m] do
      for j in [i:m] do
        let s := vdot J[i]! J[j]!
        G := G.modify i (·.set! j (s + (if i == j then 1e-12 else 0)))
        if j != i then G := G.modify j (·.set! i s)
    match solveSq G rhs with
    | none => return none
    | some y =>
      let mut dx := Array.replicate x.size 0.0
      for i in [0:m] do
        let yi := y[i]!
        if yi != 0 then
          let row := J[i]!
          for k in [0:x.size] do
            dx := dx.set! k (dx[k]! - yi * row[k]!)
      x := (Array.range x.size).map fun k => x[k]! + dx[k]!
  let g := resid x E
  if g.foldl (fun s v => max s v.abs) 0 < 1e-11 then return some x else return none

def minGap (x : Array Float) (isE : Nat → Nat → Bool) (n : Nat) : Float × Nat × Nat := Id.run do
  let mut best := 1e9
  let mut bi := 0
  let mut bj := 0
  for i in [0:n] do
    for j in [i+1:n] do
      if !isE i j then
        let dx := x[2*i]! - x[2*j]!
        let dy := x[2*i+1]! - x[2*j+1]!
        let d := dx * dx + dy * dy - 1
        if d < best then
          best := d
          bi := i
          bj := j
  return (best, bi, bj)

inductive TraceRes where
  | blocked
  | endpoint (x : Array Float)
  | fail (why : String)
  deriving Inhabited

/-- gap of pair (i, j): squared distance minus 1 -/
def pairGap (x : Array Float) (i j : Nat) : Float :=
  let dx := x[2*i]! - x[2*j]!
  let dy := x[2*i+1]! - x[2*j+1]!
  dx * dx + dy * dy - 1

/-- most violating monitored pair (gap < -1e-9), if any -/
def worstPair (x : Array Float) (isE : Nat → Nat → Bool) (n : Nat) : Option (Nat × Nat) := Id.run do
  let mut best := -1e-9
  let mut res := none
  for i in [0:n] do
    for j in [i+1:n] do
      if !isE i j then
        let g := pairGap x i j
        if g < best then
          best := g
          res := some (i, j)
  return res

/-- follow the mechanism `E` from `x0` in direction `dir` until a new contact forms. -/
def trace (x0 : Array Float) (E : Array (Nat × Nat)) (dir : Float) (maxSteps : Nat := 3000) :
    TraceRes := Id.run do
  let n := x0.size / 2
  let (a, b) := E[0]!
  let mut Eset : Std.HashSet (Nat × Nat) := {}
  for (i, j) in E do
    Eset := Eset.insert (i, j)
    Eset := Eset.insert (j, i)
  let isE (i j : Nat) : Bool := Eset.contains (i, j)
  let some t0 := tangent x0 E a b | return .fail "no tangent at start"
  let mut t := t0.map (· * dir)
  let mut x := x0
  let mut h := 0.02
  let mut first := true
  for _ in [0:maxSteps] do
    let xp := (Array.range x.size).map fun k => x[k]! + h * t[k]!
    match newtonProj xp E a b (some t) with
    | none =>
      h := h / 2
      if h < 1e-9 then return .fail "step underflow"
    | some xn =>
      match worstPair xn isE n with
      | some (pi, pj) =>
        -- bisect on the gap of pair (pi, pj), then re-check other pairs
        let mut hiS := h
        let mut pr := (pi, pj)
        let mut xbest := x
        let mut loS := 0.0
        for _ in [0:4] do
          let mut lo := 0.0
          let mut hi := hiS
          let mut xl := x
          for _ in [0:90] do
            let mid := (lo + hi) / 2
            let xm := (Array.range x.size).map fun k => x[k]! + mid * t[k]!
            match newtonProj xm E a b (some t) with
            | none => hi := mid
            | some xc =>
              if pairGap xc pr.1 pr.2 < 0 then hi := mid else
                lo := mid
                xl := xc
          xbest := xl
          loS := lo
          match worstPair xl isE n with
          | some p2 =>
            pr := p2
            hiS := lo
          | none => break
        if first && loS < 1e-7 then return .blocked
        return .endpoint xbest
      | none =>
        match tangent xn E a b with
        | none => return .fail "singular point"
        | some tn =>
          let s := if vdot tn t ≥ 0 then 1.0 else -1.0
          t := tn.map (· * s)
          x := xn
          first := false
          h := min (h * 1.5) 0.05
  return .fail "max steps"

end OL
