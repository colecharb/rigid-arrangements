namespace CaseB

/-!
# The braced-rhombus ("case (b)", |C| = 4) search

For an infinitesimally rigid case-(b) arrangement with a 4-circle off-lattice cluster the shape
is forced (`docs/offlattice.md` Theorem 5 and the bound `e(C) ≤ 2|C| − 4`, `e(C,L) ≤ |C|`):
the four free circles form a **side-2 rhombus** and each is tethered to exactly one body circle.
So the unknowns are only the four anchor sites `x₁ x₂ x₃ x₄` (lattice) and the four free centres
`w₁ w₂ w₃ w₄` with

    |wᵢ − xᵢ| = 2  (i = 1..4),   |w₁w₂| = |w₂w₃| = |w₃w₄| = |w₄w₁| = 2.

**Parametrisation.**  `w₁` runs over the circle of radius 2 about `x₁` (angle `θ`); then `w₂` is
one of the two points at distance 2 from both `w₁` and `x₂` (sign `σ₂`), `w₄` likewise from `w₁`
and `x₄` (sign `σ₄`), and `w₃` one of the two points at distance 2 from both `w₂` and `w₄`
(sign `σ₃`).  Every solution appears for some `(θ, σ₂, σ₄, σ₃)`, so scanning `θ` over the eight
sign branches and solving `F(θ) := |w₃ − x₃|² − 4 = 0` is complete.

**Two facts that shape the search.**
* A closed side-2 quadrilateral is automatically a rhombus — centrally symmetric with
  perpendicular diagonals — so `|w₁w₃|² + |w₂w₄|² = 16` and each diagonal lies in `[2, 2√3]`.
* Every side-2 rhombus **on** the lattice has a diagonal of length exactly 2, i.e. contains a
  triangle.  Since the cluster must be triangle-free, both diagonals are `> 2` and the rhombus is
  therefore *not* a lattice rhombus; some rhombus edge then points outside the lattice directions
  and the arrangement is off-lattice by the frame criterion.  (Checked numerically all the same,
  via `z⁶ − 64`.)

**Bounds on the anchors.**  `|xᵢ − xᵢ₊₁| ≤ 2 + 2 + 2 = 6` (eN ≤ 9) and
`|x₁ − x₃| ≤ 2 + 2√3 + 2 < 7.47` (eN ≤ 13); opposite anchors may coincide, adjacent ones may not
(they would make a triangle).  These bounds are exhaustive for `|C| = 4`.
-/

/-- the 8 relabellings of a 4-cycle (D₄). -/
def cycPerms : Array (Array Nat) :=
  #[#[0,1,2,3], #[1,2,3,0], #[2,3,0,1], #[3,0,1,2],
    #[0,3,2,1], #[1,0,3,2], #[2,1,0,3], #[3,2,1,0]]

def tupKey (xs : Array Site) : Nat :=
  let o := xs[0]!
  let enc (p : Site) : Nat := ((p.1 - o.1 + 16).toNat) * 32 + ((p.2 - o.2 + 16).toNat)
  (enc xs[1]! * 1024 + enc xs[2]!) * 1024 + enc xs[3]!

/-- canonical key of an anchor 4-cycle under translation, the 12 lattice symmetries and D₄. -/
def canonTup (xs : Array Site) : Nat := Id.run do
  let mut best : Nat := 0
  let mut first := true
  for m in syms do
    let ys := xs.map m.app
    for p in cycPerms do
      let k := tupKey (p.map (ys[·]!))
      if first || k < best then best := k; first := false
  return best

/-- all sites with `lo ≤ eN ≤ hi`. -/
def pool (lo hi : Int) : Array Site := Id.run do
  let mut out := #[]
  let r : Int := 5
  for a in [0:11] do
    for b in [0:11] do
      let p : Site := ((a : Int) - r, (b : Int) - r)
      let e := eN p
      if lo ≤ e && e ≤ hi then out := out.push p
  return out

/-! ## The closure function -/

/-- `F(θ) = |w₃ − x₃|² − 4`; `NaN` where the branch is undefined.  Monolithic (no allocation)
for the scan. -/
@[inline] def closeF (x1x x1y x2x x2y x3x x3y x4x x4y : Float)
    (c s sg2 sg4 sg3 : Float) : Float :=
  let w1x := x1x + 2.0 * c
  let w1y := x1y + 2.0 * s
  let d2x := x2x - w1x; let d2y := x2y - w1y
  let l2 := d2x * d2x + d2y * d2y
  let g2 := sg2 * Float.sqrt ((16.0 - l2) / (4.0 * l2))
  let w2x := w1x + 0.5 * d2x - g2 * d2y
  let w2y := w1y + 0.5 * d2y + g2 * d2x
  let d4x := x4x - w1x; let d4y := x4y - w1y
  let l4 := d4x * d4x + d4y * d4y
  let g4 := sg4 * Float.sqrt ((16.0 - l4) / (4.0 * l4))
  let w4x := w1x + 0.5 * d4x - g4 * d4y
  let w4y := w1y + 0.5 * d4y + g4 * d4x
  let d3x := w4x - w2x; let d3y := w4y - w2y
  let l3 := d3x * d3x + d3y * d3y
  let g3 := sg3 * Float.sqrt ((16.0 - l3) / (4.0 * l3))
  let w3x := w2x + 0.5 * d3x - g3 * d3y
  let w3y := w2y + 0.5 * d3y + g3 * d3x
  (w3x - x3x) * (w3x - x3x) + (w3y - x3y) * (w3y - x3y) - 4.0

/-- the four free centres of a branch (same formulas, allocating version). -/
def closeW (xf : Array P2) (θ : Float) (sg2 sg4 sg3 : Float) : Array P2 :=
  let x1 := xf[0]!; let x2 := xf[1]!; let x4 := xf[3]!
  let w1 : P2 := ⟨x1.x + 2.0 * Float.cos θ, x1.y + 2.0 * Float.sin θ⟩
  let step (A B : P2) (sg : Float) : P2 :=
    let dx := B.x - A.x; let dy := B.y - A.y
    let l := dx * dx + dy * dy
    let g := sg * Float.sqrt ((16.0 - l) / (4.0 * l))
    ⟨A.x + 0.5 * dx - g * dy, A.y + 0.5 * dy + g * dx⟩
  let w2 := step w1 x2 sg2
  let w4 := step w1 x4 sg4
  let w3 := step w2 w4 sg3
  #[w1, w2, w3, w4]

/-! ## Candidates -/

structure Cand where
  xs : Array Site
  ws : Array P2
  θ : Float
  sg2 : Float
  sg4 : Float
  sg3 : Float
  d13 : Float          -- squared diagonals
  d24 : Float
  sep : Float          -- min over non-tether anchor/ring pairs of d² − 4
  offMax : Float       -- max |z⁶ − 64| over the 8 contact vectors
  det8 : Float         -- determinant of the 8×8 ring-relative rigidity matrix
  deriving Inhabited

/-- determinant of the 8×8 ring-relative rigidity matrix (4 tether rows, 4 rhombus rows). -/
def det8 (xs ws : Array P2) : Float := Id.run do
  let z : Float := 0.0
  let mut M : Array (Array Float) := #[]
  for i in [0:4] do
    let d := ws[i]!.sub xs[i]!
    M := M.push (((Array.replicate 8 z).set! (2*i) d.x).set! (2*i+1) d.y)
  for i in [0:4] do
    let j := (i + 1) % 4
    let d := ws[i]!.sub ws[j]!
    M := M.push (((((Array.replicate 8 z).set! (2*i) d.x).set! (2*i+1) d.y).set!
      (2*j) (-d.x)).set! (2*j+1) (-d.y))
  let mut det : Float := 1.0
  for col in [0:8] do
    let mut piv := col
    for i in [col:8] do
      if (M[i]![col]!).abs > (M[piv]![col]!).abs then piv := i
    if (M[piv]![col]!).abs < 1e-14 then return 0.0
    if piv != col then
      let r := M[piv]!
      M := (M.set! piv M[col]!).set! col r
      det := -det
    let p := M[col]![col]!
    det := det * p
    for i in [col+1:8] do
      let f := M[i]![col]! / p
      let mut row := M[i]!
      for j in [col:8] do
        row := row.set! j (row[j]! - f * M[col]![j]!)
      M := M.set! i row
  return det

/-- how badly the three geometric tests fail: `> 0` means the configuration is not a legal
arrangement (a ring diagonal below 2 means two free circles overlap — and a diagonal of exactly
2 is a lattice rhombus, i.e. a triangle; `sep ≤ 0` means a free circle overlaps or touches an
anchor it is not tethered to).  The minimum of this over all rejected closures is the safety
margin of the floating-point screen. -/
def Cand.worstFail (C : Cand) : Float :=
  max (max (4.0 - C.d13) (4.0 - C.d24)) (-C.sep)

def mkCand (xs : Array Site) (θ sg2 sg4 sg3 : Float) : Cand :=
  let xf := xs.map siteF
  let ws := closeW xf θ sg2 sg4 sg3
  let d13 := P2.d2 ws[0]! ws[2]!
  let d24 := P2.d2 ws[1]! ws[3]!
  let sep := Id.run do
    let mut m : Float := 1e9
    for i in [0:4] do
      for j in [0:4] do
        if i != j then m := min m (P2.d2 ws[i]! xf[j]! - 4.0)
    return m
  let offMax := Id.run do
    let mut m : Float := 0.0
    for i in [0:4] do
      m := max m (z6m64 (ws[i]!.sub xf[i]!))
      m := max m (z6m64 (ws[i]!.sub ws[(i+1) % 4]!))
    return m
  ⟨xs, ws, θ, sg2, sg4, sg3, d13, d24, sep, offMax, det8 xf ws⟩

/-- the tests a candidate must pass (all floating point; hits and near-misses are re-checked
with interval arithmetic in `Interval.lean`). -/
def Cand.ok (C : Cand) (tol : Float := 1e-7) : Bool :=
  C.worstFail < -tol                          -- triangle-free, no overlap, no extra contact
    && C.offMax > 1e-4                        -- off the lattice (frame criterion)
    && C.det8.abs > 1e-9                      -- infinitesimally rigid rhombus

/-- is this closure an exact lattice configuration?  The four sites are guessed from the floats
and then every tether and every rhombus edge is verified to be a lattice unit vector by integer
arithmetic, so a positive answer is exact.  A side-2 lattice rhombus always has a diagonal of
exactly 2, i.e. contains a triangle, so these closures are not case-(b) clusters. -/
def latticeClosure (xs : Array Site) (ws : Array P2) : Option (Array Site) := do
  let ps ← ws.mapM nearSite
  guard ((List.range 4).all fun i => eN (sub ps[i]! xs[i]!) == 1)
  guard ((List.range 4).all fun i => eN (sub ps[i]! ps[(i+1) % 4]!) == 1)
  return ps

/-- scan one anchor tuple: all transversal roots of `F` on the eight branches, plus the number
of *flat* sign changes discarded.

A flat sign change is one where `F` is at float noise level on both sides: there `F ≡ 0` on a
whole interval, i.e. the closed rhombus **flexes**.  The clearest such family is an anchor
4-cycle that is itself a side-2 lattice rhombus: then `wᵢ = xᵢ + t` closes for *every* `t` of
length 2 (the linkage-held translation of `docs/offlattice.md` Q5).  Such a configuration has a
singular 8×8 ring matrix, so it is never infinitesimally rigid and is correctly discarded; it is
counted separately only to keep the root counts meaningful (otherwise they grow linearly with
the scan resolution). -/
structure ScanOut where
  cands : Array Cand
  /-- flat sign changes, i.e. ones discarded as noise on a branch where `F ≡ 0`. -/
  nFlat : Nat
  /-- how many of the discarded flat sign changes would have passed *every* test.  This is the
  audit of the flat heuristic: it must be `0`, or the heuristic is throwing away answers. -/
  flatOk : Nat
  /-- the largest `|det8|` among flat sign changes that pass the geometric tests: how close any
  of them comes to being an infinitesimally rigid configuration. -/
  flatMaxDet : Float
  /-- the smallest `worstFail` among flat sign changes: how close any of them comes to being a
  legal arrangement (`< 0` means legal). -/
  flatWorst : Float
  /-- largest slope `|ΔF| · steps` classified flat, and smallest classified transversal: the two
  populations must be far apart for the `1e-3` cut to be safe. -/
  flatMaxSlope : Float
  transMinSlope : Float
  deriving Inhabited

def scanTupleF (xs : Array Site) (steps : Nat) : ScanOut := Id.run do
  let xf := xs.map siteF
  let x1 := xf[0]!; let x2 := xf[1]!; let x3 := xf[2]!; let x4 := xf[3]!
  let mut out : Array Cand := #[]
  let mut nFlat : Nat := 0
  let mut flatOk : Nat := 0
  let mut flatMaxDet : Float := 0.0
  let mut flatWorst : Float := 1.0e9
  let mut flatMaxSlope : Float := 0.0
  let mut transMinSlope : Float := 1.0e9
  let twoPi := 6.283185307179586476925286766559
  for br in [0:8] do
    let sg2 : Float := if br &&& 1 == 0 then 1.0 else -1.0
    let sg4 : Float := if br &&& 2 == 0 then 1.0 else -1.0
    let sg3 : Float := if br &&& 4 == 0 then 1.0 else -1.0
    let mut prevθ : Float := 0.0
    let mut prevF : Float := 0.0/0.0
    for k in [0:steps+1] do
      let θ := twoPi * k.toFloat / steps.toFloat
      let f := closeF x1.x x1.y x2.x x2.y x3.x x3.y x4.x x4.y
        (Float.cos θ) (Float.sin θ) sg2 sg4 sg3
      if !f.isNaN && !prevF.isNaN && ((prevF < 0.0 && f > 0.0) || (prevF > 0.0 && f < 0.0)) then
        let slope := (f - prevF).abs * steps.toFloat
        if slope ≤ 1.0e-3 then
          -- a flat sign change has |F'| at noise level: the closed rhombus flexes there.  It is
          -- still built and tested, so that the discard is audited rather than trusted.
          nFlat := nFlat + 1
          if slope > flatMaxSlope then flatMaxSlope := slope
          let C := mkCand xs (0.5 * (prevθ + θ)) sg2 sg4 sg3
          if C.ok then flatOk := flatOk + 1
          if C.worstFail < flatWorst then flatWorst := C.worstFail
          if C.worstFail < 0.0 && C.det8.abs > flatMaxDet then flatMaxDet := C.det8.abs
        else
          if slope < transMinSlope then transMinSlope := slope
          -- bisect
          let mut a := prevθ; let mut b := θ
          let mut fa := prevF
          for _ in [0:60] do
            let m := 0.5 * (a + b)
            let fm := closeF x1.x x1.y x2.x x2.y x3.x x3.y x4.x x4.y
              (Float.cos m) (Float.sin m) sg2 sg4 sg3
            if fm.isNaN then break
            if (fm < 0.0) == (fa < 0.0) then a := m; fa := fm else b := m
          out := out.push (mkCand xs (0.5 * (a + b)) sg2 sg4 sg3)
      prevθ := θ; prevF := f
  return ⟨out, nFlat, flatOk, flatMaxDet, flatWorst, flatMaxSlope, transMinSlope⟩

def scanTuple (xs : Array Site) (steps : Nat) : Array Cand := (scanTupleF xs steps).cands

end CaseB
