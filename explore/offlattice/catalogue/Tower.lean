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
