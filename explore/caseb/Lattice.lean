import Std.Data.HashSet
import Std.Data.HashMap
open Std

/-!
# Case (b): shared lattice / geometry layer

Exploratory (plain Lean + Std, no Mathlib, no theorems).  Lattice site `(a, b)` is the plane
point `(2a + b, √3 b)`; two circles of radius 1 touch iff the site difference has `eN = 1`.

Used by `Rhombus.lean` (the braced-rhombus / "case (b)" search) and `Chain.lean` (E30-type taut
chains).  See `explore/caseb/README.md`.
-/

namespace CaseB

abbrev Site := Int × Int

/-- `N(a + bω) = a² + ab + b²`; real squared distance between sites is `4 * eN Δ`. -/
@[inline] def eN (p : Site) : Int := p.1 * p.1 + p.1 * p.2 + p.2 * p.2

@[inline] def sub (p q : Site) : Site := (p.1 - q.1, p.2 - q.2)
@[inline] def add (p q : Site) : Site := (p.1 + q.1, p.2 + q.2)

/-- the six unit vectors, counterclockwise. -/
def units : Array Site := #[(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

/-! ## The 12 lattice symmetries -/

structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Inhabited, BEq, Hashable

@[inline] def M2.app (m : M2) (p : Site) : Site := (m.a * p.1 + m.b * p.2, m.c * p.1 + m.d * p.2)
def M2.mul (m n : M2) : M2 :=
  ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d, m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d⟩

/-- rotation by 60°: `(a,b) ↦ (-b, a+b)`.  reflection: `(a,b) ↦ (b,a)`.  Both preserve `eN`. -/
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

/-! ## Exact rank of the rigidity matrix (fraction-free elimination over ℤ)

In the affine coordinates `(a, b)` the rigidity row of a contact is `(Δa, Δb)`: the real row is
`M (Δa, Δb)` with `M = [[2,1],[0,√3]]` invertible, so the rank is the same. -/

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
        M := (M.set! piv M[r]!).set! r rowP
        let pv := rowP[col]!
        for i in [r+1:m] do
          let rowI := M[i]!
          let f := rowI[col]!
          let mut nr := rowI
          for j in [0:ncols] do
            if j > col then nr := nr.set! j ((pv * rowI[j]! - f * rowP[j]!) / prev)
          M := M.set! i (nr.set! col 0)
        prev := pv
        r := r + 1
  return r

def contacts (pts : Array Site) : Array (Nat × Nat) := Id.run do
  let mut es := #[]
  for i in [0:pts.size] do
    for j in [i+1:pts.size] do
      if eN (sub pts[i]! pts[j]!) == 1 then es := es.push (i, j)
  return es

def rigRank (pts : Array Site) : Nat := Id.run do
  let n := pts.size
  let mut rows : Array (Array Int) := #[]
  for (i, j) in contacts pts do
    let d := sub pts[i]! pts[j]!
    rows := rows.push ((((((Array.replicate (2*n) (0 : Int)).set! (2*i) d.1).set! (2*i+1) d.2).set!
      (2*j) (-d.1)).set! (2*j+1) (-d.2)))
  return intRank rows (2 * n)

/-- infinitesimally rigid: exact rank `2n - 3`. -/
def infRigid (pts : Array Site) : Bool :=
  pts.size ≤ 1 || rigRank pts == 2 * pts.size - 3

def showSite (p : Site) : String := s!"({p.1},{p.2})"
def showSites (ps : Array Site) : String :=
  "[" ++ String.intercalate ", " (ps.toList.map showSite) ++ "]"

/-! ## Floating-point plane geometry (screening only) -/

structure P2 where
  x : Float
  y : Float
  deriving Inhabited

def r3f : Float := 1.7320508075688772935
@[inline] def P2.sub (a b : P2) : P2 := ⟨a.x - b.x, a.y - b.y⟩
@[inline] def P2.add (a b : P2) : P2 := ⟨a.x + b.x, a.y + b.y⟩
@[inline] def P2.n2 (a : P2) : Float := a.x * a.x + a.y * a.y
@[inline] def P2.d2 (a b : P2) : Float := (a.sub b).n2
@[inline] def siteF (p : Site) : P2 := ⟨2.0 * p.1.toFloat + p.2.toFloat, r3f * p.2.toFloat⟩

/-- the two points at distance 2 from both `A` and `B` (radius-2 circle intersection);
`σ = true` picks the one on the left of `A → B`.  `none` if they do not meet. -/
@[inline] def cci (A B : P2) (σ : Bool) : Option P2 :=
  let dx := B.x - A.x
  let dy := B.y - A.y
  let l2 := dx * dx + dy * dy
  if l2 < 1e-9 || l2 > 16.0 - 1e-12 then none
  else
    let g := Float.sqrt ((16.0 - l2) / (4.0 * l2))
    let s := if σ then g else -g
    some ⟨A.x + 0.5 * dx - s * dy, A.y + 0.5 * dy + s * dx⟩

def roundToInt (x : Float) : Int :=
  if x < 0.0 then -(((-x).round.toUInt64.toNat : Nat) : Int) else (((x.round.toUInt64.toNat : Nat) : Int))

/-- the lattice site nearest to a plane point, when the point is within `tol` of one. -/
def nearSite (q : P2) (tol : Float := 1e-6) : Option Site :=
  let b := roundToInt (q.y / r3f)
  let a := roundToInt ((q.x - b.toFloat) / 2.0)
  let p : Site := (a, b)
  if P2.d2 (siteF p) q < tol * tol then some p else none

/-- `z⁶ - 64` for a contact vector `z` of length 2: zero exactly on the lattice directions
(frame criterion, `docs/offlattice.md` Theorem 2). -/
def z6m64 (z : P2) : Float :=
  let a := z.x; let b := z.y
  let re2 := a * a - b * b; let im2 := 2.0 * a * b          -- z²
  let re3 := re2 * a - im2 * b; let im3 := re2 * b + im2 * a -- z³
  Float.sqrt ((re3 * re3 - im3 * im3 - 64.0) ^ 2 + (2.0 * re3 * im3) ^ 2)

end CaseB
