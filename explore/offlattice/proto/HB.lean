import RigidArrangements
open RigidArrangements

/-!
Exploratory (computed-exact) two-body hinge + bar assembler.

Body 1 sits on the standard lattice with its hinge at the origin; body 2 is placed by
`t ↦ α · t'` (or `α · conj t'`), `t' = latticePoint (t - h₂)`, where `α` is fixed by the bar
`|X - Y| = 2`. Writing `u = x - h₁`, `v = y - h₂`, `Nᵢ = eNorm`, `c = N₁ + N₂ - 1`,
`D = 4 N₁ N₂ - c²`, the exact placement is `α = w · U / V'` with `w = (c ± i√D) / (2N₁)`.
Every squared distance between a circle of body 1 and one of body 2 is `A + B √(3D)` with
`A, B ∈ ℚ`; all arithmetic below is exact (integers and rationals; no floats).
Eisenstein integers `a + bρ` (`ρ = e^{iπ/3}`, `ρ² = ρ - 1`) are pairs `(a, b)`; lattice
coordinates are Eisenstein coordinates (`latticePoint v = 2 v`).
-/

abbrev E := Int × Int
def emul (x y : E) : E := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)
def econj (x : E) : E := (x.1 + x.2, -x.2)
def en (x : E) : Int := eNorm x

def units6 : List E := [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
def touchE (p q : E) : Bool := en (p - q) == 1

/-! ### Canonical forms of lattice sets under the 12 symmetries and translations -/

def lexLe (p q : E) : Bool := p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)
def sortPts (l : List E) : List E := l.mergeSort lexLe
def normPts (l : List E) : List E :=
  match sortPts l with
  | [] => []
  | o :: rest => (o :: rest).map fun p => p - o
def listLt : List E → List E → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a == b then listLt as bs else lexLe a b
def canon (l : List E) : List E := Id.run do
  let mut best := normPts l
  for M in latticeSymmetries do
    let c := normPts (l.map (latticeMatApply M))
    if listLt c best then best := c
  return best

/-- rigid lattice bodies of size `k`, free classes, grown from the triangle by adding a site
touching at least two sites (the Henneberg closure of a triangle; this is all rigid lattice sets
for `k ≤ 13` by the census, and every set produced is rigid by Henneberg steps). -/
def bodiesUpTo (K : Nat) : Array (Array (List E)) := Id.run do
  let tri := canon [(0, 0), (1, 0), (0, 1)]
  let mut lv : Array (Array (List E)) := #[#[], #[], #[[(0, 0), (1, 0)]], #[tri]]
  for k in [4:K+1] do
    let mut seen : Std.HashSet (List E) := {}
    let mut out : Array (List E) := #[]
    for S in lv[k-1]! do
      for p in S do
        for d in units6 do
          let x := p + d
          if !S.contains x && (S.filter (touchE x)).length ≥ 2 then
            let T := canon (x :: S)
            if !seen.contains T then
              seen := seen.insert T
              out := out.push T
    lv := lv.push out
  return lv

/-! ### Exact numbers `p + q √M` -/

/-- `p + q √M ≥ 0`, for `M ≥ 0`. -/
def nonnegSqrt (p q : Rat) (M : Int) : Bool :=
  (p ≥ 0 && q ≥ 0) || (p ≥ 0 && q < 0 && p * p ≥ q * q * M) || (p < 0 && q > 0 && q * q * M ≥ p * p)

def isSqInt (n : Int) : Option Int :=
  if n < 0 then none else
  let r := n.toNat.sqrt
  if r * r == n.toNat then some r else none

/-- `p + q √M = 0`. -/
def zeroSqrt (p q : Rat) (M : Int) : Bool :=
  match isSqInt M with
  | some r => p + q * r == 0
  | none => p == 0 && q == 0

structure HB where
  B₁ : List E
  h₁ : E
  x : E
  B₂ : List E
  h₂ : E
  y : E
  flip : Bool
  sgn : Int   -- ±1
deriving Repr

/-- squared distance between body-1 site `s` and body-2 site `t`, as `(A, B)` with
`dist² = A + B √(3D)`. -/
def crossDist2 (d : HB) (s t : E) : Rat × Rat :=
  let u := d.x - d.h₁
  let v := d.y - d.h₂
  let N₁ := en u
  let N₂ := en v
  let c := N₁ + N₂ - 1
  let s' := s - d.h₁
  let t' := t - d.h₂
  let z := emul (emul (econj s') u) (if d.flip then emul (econj t') v else emul t' (econj v))
  let A : Rat := 4 * en s' + 4 * en t' - (2 * c * (2 * z.1 + z.2) : Rat) / (N₁ * N₂ : Rat)
  let B : Rat := (2 * d.sgn * z.2 : Rat) / (N₁ * N₂ : Rat)
  (A, B)

def discr (d : HB) : Int :=
  let N₁ := en (d.x - d.h₁)
  let N₂ := en (d.y - d.h₂)
  4 * N₁ * N₂ - (N₁ + N₂ - 1) ^ 2

/-- Result of the exact check: `none` if some pair overlaps, else the number of contacts. -/
def check (d : HB) : Option Nat := Id.run do
  let M := 3 * discr d
  let b2 := d.B₂.filter (· != d.h₂)
  let mut contacts := 0
  -- inside each body
  for s in d.B₁ do
    for s' in d.B₁ do
      if lexLe s s' && s != s' && touchE s s' then contacts := contacts + 1
  for t in d.B₂ do
    for t' in d.B₂ do
      if lexLe t t' && t != t' && touchE t t' then contacts := contacts + 1
  -- across (the hinge is shared: skip it on both sides)
  for s in d.B₁.filter (· != d.h₁) do
    for t in b2 do
      let (A, B) := crossDist2 d s t
      if !nonnegSqrt (A - 4) B M then return none
      if zeroSqrt (A - 4) B M then contacts := contacts + 1
  return some contacts

/-- `α` as an element of `ℚ(ρ)` when `D = 3k²` (else `none`): `α = (c ± k(2ρ - 1)) e / (2N₁N₂)`,
`e = u · conj v''`. The union is on the lattice iff `α` is a sixth root of unity. -/
def onLattice (d : HB) : Bool :=
  let u := d.x - d.h₁
  let v := d.y - d.h₂
  let N₁ := en u
  let N₂ := en v
  let c := N₁ + N₂ - 1
  let D := discr d
  if D % 3 != 0 then false else
  match isSqInt (D / 3) with
  | none => false
  | some k =>
    let v'' := if d.flip then econj v else v
    let e := emul u (econj v'')
    -- (c - σk + 2σk ρ) * e, then divide by 2 N₁ N₂
    let num := emul (c - d.sgn * k, 2 * d.sgn * k) e
    let den := 2 * N₁ * N₂
    units6.any fun r => num == (r.1 * den, r.2 * den)

/-- Exact invariant for deduplication: sorted list of all squared distances `(A, B)`, with `M`. -/
def distKey (d : HB) : Int × List (Rat × Rat) :=
  let M := 3 * discr d
  let b2 := d.B₂.filter (· != d.h₂)
  let inner₁ := (d.B₁.flatMap fun s => d.B₁.filterMap fun s' =>
    if lexLe s s' && s != s' then some ((4 * en (s - s') : Rat), (0 : Rat)) else none)
  let inner₂ := (d.B₂.flatMap fun t => d.B₂.filterMap fun t' =>
    if lexLe t t' && t != t' then some ((4 * en (t - t') : Rat), (0 : Rat)) else none)
  let cross := (d.B₁.filter (· != d.h₁)).flatMap fun s => b2.map fun t => crossDist2 d s t
  let all := (inner₁ ++ inner₂ ++ cross).mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)
  -- if 3D is a square, fold the irrational part in
  match isSqInt M with
  | some r => (0, (all.map fun ab => (ab.1 + ab.2 * (r : Rat), (0 : Rat))).mergeSort fun a b => a.1 ≤ b.1)
  | none => (M, all)

def o11data (flip : Bool) (sgn : Int) : HB :=
  { B₁ := [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (-1, 2)], h₁ := (-1, 2), x := (0, 0),
    B₂ := [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (-1, 2)], h₂ := (-1, 2), y := (0, 0),
    flip := flip, sgn := sgn }

#eval [(false, 1), (false, -1), (true, 1), (true, -1)].map fun (f, s) =>
  let d := o11data f s
  (f, s, discr d, check d, onLattice d)

/-- search all two-body hinge + bar assemblies with `n = |B₁| + |B₂| - 1 ≤ nmax`. -/
def search (nmax : Nat) : IO Unit := do
  let lv := bodiesUpTo (nmax - 1)
  IO.println s!"bodies by size: {(List.range lv.size).map fun k => lv[k]!.size}"
  for n in [3:nmax+1] do
    let mut keysOff : Std.HashSet (Int × List (Rat × Rat)) := {}
    let mut keysOn : Std.HashSet (Int × List (Rat × Rat)) := {}
    let mut rawOff := 0
    let mut exampleOff : Option HB := none
    for k₁ in [2:n] do
      let k₂ := n + 1 - k₁
      if k₂ ≥ 2 && k₂ < lv.size && k₁ < lv.size then
        for B₁ in lv[k₁]! do
          for B₂ in lv[k₂]! do
            for h₁ in B₁ do
              for x in B₁ do
                if x != h₁ then
                  for h₂ in B₂ do
                    for y in B₂ do
                      if y != h₂ then
                        let N₁ := en (x - h₁)
                        let N₂ := en (y - h₂)
                        let D := 4 * N₁ * N₂ - (N₁ + N₂ - 1) ^ 2
                        if D ≥ 0 then
                          for (f, s) in [(false, (1 : Int)), (false, -1), (true, 1), (true, -1)] do
                            let d : HB := ⟨B₁, h₁, x, B₂, h₂, y, f, s⟩
                            match check d with
                            | none => pure ()
                            | some _ =>
                              if onLattice d then
                                keysOn := keysOn.insert (distKey d)
                              else
                                rawOff := rawOff + 1
                                if !keysOff.contains (distKey d) then
                                  if exampleOff.isNone then exampleOff := some d
                                keysOff := keysOff.insert (distKey d)
    IO.println s!"n={n}: off-lattice valid assemblies {rawOff}, distinct distance-keys off {keysOff.size}, on-lattice keys {keysOn.size}"
    if let some d := exampleOff then
      IO.println s!"   first off-lattice example: {repr d}  D={discr d}"
#eval search 11
