/-
Float checks and decimal output for the figure examples of the off-lattice synthesis.
Radius-1 units: tangent circles have centres exactly 2 apart.
Run: cd /home/user/rigid-arrangements && lake env lean /tmp/claude-0/offlat/synth/Figs.lean
-/

abbrev Pt := Float × Float

def s2 : Float := Float.sqrt 2
def s3 : Float := Float.sqrt 3
def s5 : Float := Float.sqrt 5
def s6 : Float := Float.sqrt 6
def s11 : Float := Float.sqrt 11
def s15 : Float := Float.sqrt 15
def s33 : Float := Float.sqrt 33

/-- lattice site (a,b) ↦ (2a+b, √3 b) -/
def lat (a b : Int) : Pt := (Float.ofInt (2*a+b), s3 * Float.ofInt b)

def dist (p q : Pt) : Float := Float.sqrt ((p.1-q.1)^2 + (p.2-q.2)^2)

def tol : Float := 1e-9

/-- rank of a dense matrix by Gaussian elimination with partial pivoting -/
partial def rank (m : Array (Array Float)) : Nat := Id.run do
  let rows := m.size
  if rows == 0 then return 0
  let cols := m[0]!.size
  let mut a := m
  let mut r := 0
  for c in [0:cols] do
    if r < rows then
      -- find pivot
      let mut best := r
      let mut bv : Float := 0
      for i in [r:rows] do
        let v := (a[i]!)[c]!.abs
        if v > bv then
          best := i
          bv := v
      if bv > 1e-8 then
        let tmp := a[r]!
        a := a.set! r a[best]!
        a := a.set! best tmp
        let pr := a[r]!
        for i in [r+1:rows] do
          let f := (a[i]!)[c]! / pr[c]!
          if f != 0 then
            let row := a[i]!
            let mut nrow := row
            for k in [c:cols] do
              nrow := nrow.set! k (row[k]! - f * pr[k]!)
            a := a.set! i nrow
        r := r + 1
  return r

structure Report where
  n : Nat
  overlaps : Nat
  contacts : Nat
  maxDev : Float
  minNonContact : Float
  minDeg : Nat
  rk : Nat

def analyse (ps : Array Pt) : Report := Id.run do
  let n := ps.size
  let mut ov := 0
  let mut cs : Array (Nat × Nat) := #[]
  let mut maxDev : Float := 0
  let mut minNC : Float := 1e300
  let mut deg : Array Nat := Array.replicate n 0
  for i in [0:n] do
    for j in [i+1:n] do
      let d := dist ps[i]! ps[j]!
      if (d - 2).abs < tol then
        cs := cs.push (i, j)
        if (d-2).abs > maxDev then maxDev := (d-2).abs
        deg := deg.set! i (deg[i]! + 1)
        deg := deg.set! j (deg[j]! + 1)
      else if d < 2 then
        ov := ov + 1
      else if d < minNC then
        minNC := d
  let mut mat : Array (Array Float) := #[]
  for (i, j) in cs do
    let mut row := Array.replicate (2*n) (0:Float)
    let dx := ps[i]!.1 - ps[j]!.1
    let dy := ps[i]!.2 - ps[j]!.2
    row := row.set! (2*i) dx
    row := row.set! (2*i+1) dy
    row := row.set! (2*j) (-dx)
    row := row.set! (2*j+1) (-dy)
    mat := mat.push row
  let md := deg.foldl min 1000
  return { n := n, overlaps := ov, contacts := cs.size, maxDev := maxDev,
           minNonContact := minNC, minDeg := md, rk := rank mat }

/-- fixed-point decimal with 14 fractional digits (|x| < 90) -/
def fmt (x : Float) : String :=
  let neg := x < 0
  let y := (x.abs * 1e14).round
  let k : Nat := y.toUInt64.toNat
  let ip := k / 100000000000000
  let fp := k % 100000000000000
  let fs := toString fp
  let fs := String.ofList (List.replicate (14 - fs.length) '0') ++ fs
  -- trim to 15 significant digits overall
  let ipS := toString ip
  let keep := if ip == 0 then 15 else 15 - ipS.length
  let keep := if keep > 14 then 14 else keep
  let fs := (fs.take keep).toString
  (if neg && k != 0 then "-" else "") ++ ipS ++ "." ++ fs

def parseBack (s : String) : Float := Id.run do
  -- crude parser for the strings produced by fmt
  let neg := s.startsWith "-"
  let t := if neg then (s.drop 1).toString else s
  let parts := t.splitOn "."
  let ip := (parts[0]!).toNat!
  let fr := parts[1]!
  let fv := (fr.toNat!).toFloat / (10:Float)^(fr.length.toFloat)
  let v := ip.toFloat + fv
  return if neg then -v else v

def json (ps : Array Pt) : String :=
  "[" ++ ", ".intercalate (ps.toList.map fun p => "[" ++ fmt p.1 ++ ", " ++ fmt p.2 ++ "]") ++ "]"

def roundTrip (ps : Array Pt) : Array Pt :=
  ps.map fun p => (parseBack (fmt p.1), parseBack (fmt p.2))

def report (name : String) (ps : Array Pt) : IO Unit := do
  let r := analyse ps
  let r2 := analyse (roundTrip ps)
  IO.println s!"== {name}: n={r.n} overlaps={r.overlaps} contacts={r.contacts} 2n-3={2*r.n-3} rank={r.rk} minDeg={r.minDeg} maxDev={r.maxDev} minNonContact={r.minNonContact}"
  IO.println s!"   after decimal round-trip: overlaps={r2.overlaps} contacts={r2.contacts} rank={r2.rk} maxDev={r2.maxDev}"
  IO.println (json ps)

/-! ### The examples -/

def o11 : Array Pt := #[
  (0,0), (1,s3), (1,-s3), (2,0), (3,s3), (3,-s3),
  (11/2 + s33/6, s3/6 + s11/2),
  (14/3 + s33/3, -2*s3/3 + s11/3),
  (14/3, s3 + s11/3),
  (23/6 + s33/6, s3/6 + s11/6),
  (3 + s33/3, -2*s3/3)]

def o11z : Array Pt := o11.push (7/2 + s33/6, -(5*s3/6 + s11/2))

def q13 : Array Pt := #[
  (0,0), (1,s3), (2,2*s3), (2,0), (3,s3),
  (-21/8 - 3*s5/8, 7*s3/8 - 3*s15/8),
  (-7/4 - 3*s5/4, 7*s3/4 - s15/4),
  (-7/8 - 9*s5/8, 21*s3/8 - s15/8),
  (-7/4, -s15/4),
  (-7/8 - 3*s5/8, 7*s3/8 - s15/8),
  (-3*s5/4, 7*s3/4),
  (7/8 - 9*s5/8, 21*s3/8 + s15/8),
  (7/4 - 3*s5/4, 7*s3/4 + s15/4)]

def t14 : Array Pt := #[
  (0,0), (1,s3), (1,-s3), (2,0), (3,s3), (3,-s3),
  (3 + 4*s6/3, -s3/3),
  (3 + 2*s6/3, s3/3),
  (4 + s6, s2),
  (4 + s6/3, 2*s3/3 + s2),
  (4 + 2*s6/3, -(2*s3/3 + 2*s2)),
  (11/3, -(s3 + 4*s2/3)),
  (11/3 + 4*s6/3, -(s3/3 + 4*s2/3)),
  (10/3 + 2*s6/3, -(2*s3/3 + 2*s2/3))]

def s15sig : Array Pt := #[
  (0,0), (1,s3), (2,2*s3), (1,-s3), (2,0), (3,s3), (4,2*s3), (3,-s3),
  (8,0), (45/7, -5*s3/7), (34/7, -10*s3/7), (54/7, 8*s3/7), (43/7, 3*s3/7),
  (32/7, -2*s3/7), (41/7, 11*s3/7)]

def dh17 : Array Pt := #[
  (-4, -2*s3), (-3, -s3), (-2, 0), (-3, -3*s3), (-2, -2*s3), (-1, -s3), (0,0), (-1, -3*s3),
  (4, -2*s3), (26/7, -6*s3/7), (24/7, 2*s3/7), (17/7, -19*s3/7), (15/7, -11*s3/7),
  (13/7, -3*s3/7), (11/7, 5*s3/7), (6/7, -24*s3/7), (4/7, -16*s3/7)]

/-! H30: closing function in u. -/
def h30G (u : Float) : Float :=
  let v := Float.sqrt (4 - (u+3)^2)
  let t := -3*u*(u+3) / (v - 2*s3*u)
  let s := 9 + 3*u - 2*s3*t
  (s-1)^2 + (t-2*s3)^2 - 4

partial def bisect (f : Float → Float) (a b : Float) (k : Nat) : Float :=
  if k == 0 then (a+b)/2 else
  let m := (a+b)/2
  if (f a) * (f m) ≤ 0 then bisect f a m (k-1) else bisect f m b (k-1)

def h30u : Float := bisect h30G (-1.055627) (-1.055427) 80

def h30Body : List (Int × Int) :=
  [(-2,1),(-2,2),(-2,3),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,-2),(0,-1),(0,0),(0,2),(0,3),
   (1,-3),(1,-2),(1,2),(1,3),(2,-3),(2,-2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)]

def h30 : Array Pt :=
  let u := h30u
  let v := Float.sqrt (4 - (u+3)^2)
  let t := -3*u*(u+3) / (v - 2*s3*u)
  let s := 9 + 3*u - 2*s3*t
  let c : Pt := (3, 0)
  let w1 : Pt := (c.1 + u, c.2 + v)
  let w2 : Pt := (c.1 + s, c.2 + t)
  let w3 : Pt := (c.1 - u, c.2 - v)
  let w4 : Pt := (c.1 - s, c.2 - t)
  (h30Body.map fun (a, b) => lat a b).toArray ++ #[w1, w2, w3, w4]

def e30Body : List (Int × Int) :=
  [(0,0),(-1,0),(-1,1),(-2,1),(-2,2),(-1,2),(-2,3),(-1,3),(-2,4),(-1,4),(0,3),(0,4),(-1,5),
   (0,5),(-1,6),(0,6),(1,5),(1,6),(0,7),(1,7),(2,6),(2,7),(3,6),(3,5)]

def e30 : Array Pt :=
  (e30Body.map fun (a, b) => lat a b).toArray ++
    ((List.range 6).map fun j =>
      let jj := (j+1).toFloat
      ((11*jj/7 : Float), 5*s3*jj/7)).toArray

#eval report "O11" o11
#eval report "O11+Z" o11z
#eval report "Q13" q13
#eval report "T14" t14
#eval report "S15sigma7" s15sig
#eval report "DH17" dh17
#eval IO.println s!"H30 u = {h30u}  G(u) = {h30G h30u}"
#eval report "H30" h30
#eval report "E30" e30

/-- contact directions mod 60° (degrees), clustered to 1e-6 -/
def frames (ps : Array Pt) : List (Float × Nat) := Id.run do
  let n := ps.size
  let pi : Float := 3.14159265358979323846
  let mut cl : List (Float × Nat) := []
  for i in [0:n] do
    for j in [i+1:n] do
      let d := dist ps[i]! ps[j]!
      if (d - 2).abs < tol then
        let a := Float.atan2 (ps[j]!.2 - ps[i]!.2) (ps[j]!.1 - ps[i]!.1) * 180 / pi
        let m := a - 60 * (a / 60).floor
        let m := if m > 60 - 1e-6 then m - 60 else m
        match cl.find? (fun (c, _) => (c - m).abs < 1e-6) with
        | some _ => cl := cl.map (fun (c, k) => if (c - m).abs < 1e-6 then (c, k+1) else (c, k))
        | none => cl := cl ++ [(m, 1)]
  return cl

def maxDevSci (ps : Array Pt) : Float := (analyse ps).maxDev * 1e15

#eval [("O11", frames o11), ("O11Z", frames o11z), ("Q13", frames q13), ("T14", frames t14),
       ("S15", frames s15sig), ("DH17", frames dh17), ("H30", frames h30), ("E30", frames e30)]
#eval [maxDevSci o11, maxDevSci o11z, maxDevSci q13, maxDevSci t14, maxDevSci s15sig,
       maxDevSci dh17, maxDevSci h30, maxDevSci e30]

def ex15 : Array Pt := #[
  (0,0), (1,s3), (2,2*s3), (2,0), (3,s3),
  (-4, 2*s3), (-26/7, 6*s3/7), (-24/7, -2*s3/7), (-17/7, 19*s3/7), (-15/7, 11*s3/7),
  (-13/7, 3*s3/7), (-11/7, -5*s3/7), (-6/7, 24*s3/7), (-4/7, 16*s3/7), (1, 3*s3)]

#eval report "ex15" ex15
#eval frames ex15
#eval frames o11
#eval maxDevSci ex15

def s7 : Float := Float.sqrt 7
def s21 : Float := Float.sqrt 21

def ii15b : Array Pt := #[
  (-5, s3), (-4, 2*s3), (-3, s3), (-2, 2*s3), (-1, s3), (0, 2*s3), (0,0), (1, s3),
  (-236/49, -62*s3/49), (-37/7, -s3/7), (-142/49, -78*s3/49), (-165/49, -23*s3/49),
  (-48/49, -94*s3/49), (-71/49, -39*s3/49), (23/49, -55*s3/49)]

def ring15 : Array Pt := #[
  (-4,0), (-3,s3), (-2,0), (-1,s3), (0,0),
  (-1/2, -3*s7/2),
  ((-3+3*s21)/8, (-s3-9*s7)/8),
  (-1/4, -3*s7/4),
  ((-1+3*s21)/8, (-s3-3*s7)/8),
  ((-21-9*s21)/28, (-21*s3-39*s7)/28),
  ((-49-3*s21)/28, (-7*s3-27*s7)/28),
  ((-14-3*s21)/7, (-7*s3-6*s7)/7),
  ((-42-3*s21)/14, (-7*s3-6*s7)/14),
  ((-91-15*s21)/28, (-35*s3-9*s7)/28),
  ((-119-9*s21)/28, (-21*s3+3*s7)/28)]

#eval report "II15b" ii15b
#eval frames ii15b
#eval report "Ring15" ring15
#eval frames ring15

def ii15c : Array Pt := #[
  (-5, s3), (-4, 2*s3), (-3, s3), (-2, 2*s3), (-1, s3), (0, 2*s3), (0,0), (1, s3),
  (-39/7, -9*s3/7), (-37/7, -s3/7), (-4, -2*s3), (-26/7, -6*s3/7), (-15/7, -11*s3/7),
  (-13/7, -3*s3/7), (-2/7, -8*s3/7)]

def ii15a : Array Pt := #[
  (-4,0), (-3,s3), (-2,0), (-1,s3), (0,0),
  (-33/7, -15*s3/7), (-5, -s3), (-20/7, -18*s3/7), (-22/7, -10*s3/7), (-1, -3*s3),
  (-9/7, -13*s3/7), (4/7, -16*s3/7), (2/7, -8*s3/7), (15/7, -11*s3/7), (13/7, -3*s3/7)]

def dkey (ps : Array Pt) : Array Float := Id.run do
  let mut l : Array Float := #[]
  for i in [0:ps.size] do
    for j in [i+1:ps.size] do
      let d := (ps[i]!.1-ps[j]!.1)^2 + (ps[i]!.2-ps[j]!.2)^2
      l := l.push d
  return l.qsort (· < ·)

def sameKey (a b : Array Pt) : Bool :=
  a.size == b.size && ((dkey a).zip (dkey b)).all (fun (x, y) => (x - y).abs < 1e-9)

#eval (sameKey s15sig ii15c, sameKey s15sig ii15b, sameKey ex15 ii15a, sameKey dh17 dh17)
#eval report "II15c" ii15c
#eval report "II15a" ii15a
