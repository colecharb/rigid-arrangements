import Std.Data.HashMap
import Std.Data.HashSet
open Std

/-!
# Transfer matrix for infinitesimally rigid sets in a strip of `W` rows

## The criterion that makes it local

A *line* of a lattice set is a maximal run of consecutive occupied sites along one of the three
lattice directions (singletons included); `L = 3n − |E|`. Writing the three lattice directions
as `d₀ = (1,0)`, `d₁ = (0,1)`, `d₂ = (−1,1)`, their images in the plane satisfy
`u₀ − u₁ + u₂ = 0`.

For an infinitesimal flex `v`, the component `⟨v_i, u_k⟩` is constant along every line in
direction `k` (the bars of that line are parallel to `u_k`), so a flex is the same thing as one
scalar `x_ℓ` per line, and the only constraint is that at each site the three components come
from one vector of the plane, i.e.

    x_{ℓ₀(i)} − x_{ℓ₁(i)} + x_{ℓ₂(i)} = 0.

So `dim (flexes) = L − rank M` for the `n × L` site/line matrix `M`, and the set is
infinitesimally rigid iff that nullity is `3`.

## The state

Scan column by column. After column `a` the lines that can still grow are: the direction-0 line
of each occupied `(a,b)` (it continues to `(a+1,b)`) and the direction-2 line of each occupied
`(a,b)` with `b ≥ 1` (it continues to `(a+1,b−1)`). Direction-1 lines live inside one column.
So the open slots are determined by the column mask: at most `2W − 1` of them.

The state is `(m, P, k)`: the column mask, the subspace `P ⊆ ℚ^{slots(m)}` of restrictions to
the open slots of partial solutions, and `k`, the dimension of the partial solutions that vanish
on all open slots. Then `dim (partial flexes) = k + dim P`, `k` is non-decreasing, and closing
the strip gives nullity `k + dim P`. So: reject as soon as `k > 3`, accept when `k + dim P = 3`.

The empirical question is whether the reachable `P` close up into a finite set. They do for
`W ≤ 5`; see the journal entry / the report.

Modes:
* `scan W N [maxOrder]`  – close the state set for every width up to `W` (fails if it does not
                           close), run the stationary transfer matrix for `N` terms, take
                           second differences to get `T_w` (fixed count, `b`-span exactly `w`),
                           fit a linear recurrence and report the GF and the growth constant.
* `layer W N [maxOrder]`  – the same series without needing the state set to close: a layered
                           (non-stationary) dynamic program over the column count, exact for
                           `n ≤ N`. This is what to use for `W ≥ 5`.
* `probe W cap`          – breadth-first search by column count, reporting new states per level
                           and the size of the rationals in their subspaces; this is how the
                           non-closure at `W = 5` was diagnosed.
-/

namespace TM

/-! ## Linear algebra over ℚ -/

/-- row-reduced echelon form; returns the nonzero reduced rows and their pivot columns. -/
def rref (M0 : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) × Array Nat := Id.run do
  let mut M := M0
  let m := M.size
  let mut r := 0
  let mut piv : Array Nat := #[]
  for col in [0:ncols] do
    if r < m then
      let mut p := m
      for i in [r:m] do
        if p == m && M[i]![col]! != 0 then p := i
      if p < m then
        let rowP0 := M[p]!
        M := M.set! p M[r]!
        let c := rowP0[col]!
        let rowP := rowP0.map (· / c)
        M := M.set! r rowP
        for i in [0:m] do
          if i != r then
            let f := M[i]![col]!
            if f != 0 then
              M := M.set! i (Array.ofFn (n := ncols) fun j => M[i]![j.val]! - f * rowP[j.val]!)
        piv := piv.push col
        r := r + 1
  return (M.extract 0 r, piv)

/-- basis of `{x : M x = 0}` in `ℚ^ncols`. -/
def kernel (M : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let (R, piv) := rref M ncols
  let mut isPiv := Array.replicate ncols false
  for c in piv do isPiv := isPiv.set! c true
  let mut out : Array (Array Rat) := #[]
  for c in [0:ncols] do
    if !isPiv[c]! then
      let mut v := Array.replicate ncols (0 : Rat)
      v := v.set! c 1
      for i in [0:R.size] do
        v := v.set! piv[i]! (-R[i]![c]!)
      out := out.push v
  return out

/-- `K · G`. -/
def matMul (K G : Array (Array Rat)) (ncols : Nat) : Array (Array Rat) := Id.run do
  let mut out : Array (Array Rat) := #[]
  for row in K do
    let mut v := Array.replicate ncols (0 : Rat)
    for i in [0:G.size] do
      if row[i]! != 0 then
        for j in [0:ncols] do
          if G[i]![j]! != 0 then v := v.set! j (v[j]! + row[i]! * G[i]![j]!)
    out := out.push v
  return out

/-! ## Strip states -/

/-- open slots of column mask `m`: direction-0 line of each occupied row, then direction-2 line
of each occupied row `≥ 1`. -/
def slotsOf (W m : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for b in [0:W] do
    if m &&& (1 <<< b) != 0 then out := out.push (0, b)
  for b in [1:W] do
    if m &&& (1 <<< b) != 0 then out := out.push (2, b)
  return out

def slotIdx (W m kind b : Nat) : Nat := Id.run do
  let s := slotsOf W m
  for i in [0:s.size] do
    if s[i]! == (kind, b) then return i
  return s.size   -- unreachable when called correctly

def pc (m : Nat) : Nat := Id.run do
  let mut c := 0
  let mut m := m
  while m > 0 do
    if m % 2 == 1 then c := c + 1
    m := m / 2
  return c

structure State where
  m : Nat
  k : Nat
  basis : Array (Array Rat)    -- RREF basis of `P ⊆ ℚ^{slots m}`
  deriving Inhabited

def State.key (st : State) : String := Id.run do
  let mut s := s!"{st.m}|{st.k}|{st.basis.size}|"
  for row in st.basis do
    for x in row do s := s ++ s!"{x.num}/{x.den},"
    s := s ++ ";"
  return s

/-- One column step. `none` means the branch cannot reach nullity 3 (`k > 3`). -/
def step (W : Nat) (st : State) (m' : Nat) : Option State := Id.run do
  let s := (slotsOf W st.m).size
  let mut nv := s
  -- direction-1 variable for each maximal run of `m'`
  let mut v1 := Array.replicate W 0
  let mut cur := nv
  for b in [0:W] do
    if m' &&& (1 <<< b) != 0 then
      if b == 0 || m' &&& (1 <<< (b-1)) == 0 then
        cur := nv
        nv := nv + 1
      v1 := v1.set! b cur
  -- direction-0 and direction-2 variables
  let mut v0 := Array.replicate W 0
  let mut v2 := Array.replicate W 0
  for b in [0:W] do
    if m' &&& (1 <<< b) != 0 then
      if st.m &&& (1 <<< b) != 0 then
        v0 := v0.set! b (slotIdx W st.m 0 b)
      else
        v0 := v0.set! b nv; nv := nv + 1
      if b + 1 < W && st.m &&& (1 <<< (b+1)) != 0 then
        v2 := v2.set! b (slotIdx W st.m 2 (b+1))
      else
        v2 := v2.set! b nv; nv := nv + 1
  let ncols := nv
  let nNew := nv - s
  -- relations
  let mut R : Array (Array Rat) := #[]
  for b in [0:W] do
    if m' &&& (1 <<< b) != 0 then
      let mut row := Array.replicate ncols (0 : Rat)
      row := row.set! (v0[b]!) (row[v0[b]!]! + 1)
      row := row.set! (v1[b]!) (row[v1[b]!]! - 1)
      row := row.set! (v2[b]!) (row[v2[b]!]! + 1)
      R := R.push row
  -- basis of `P ⊕ ℚ^{new}`
  let mut G : Array (Array Rat) := #[]
  for row in st.basis do
    let mut v := Array.replicate ncols (0 : Rat)
    for j in [0:s] do v := v.set! j row[j]!
    G := G.push v
  for t in [0:nNew] do
    G := G.push ((Array.replicate ncols (0 : Rat)).set! (s + t) 1)
  -- `A c = 0` where `x = Gᵗ c`
  let g := G.size
  let mut A : Array (Array Rat) := #[]
  for rrow in R do
    let mut v := Array.replicate g (0 : Rat)
    for i in [0:g] do
      let mut acc : Rat := 0
      for j in [0:ncols] do
        if rrow[j]! != 0 && G[i]![j]! != 0 then acc := acc + rrow[j]! * G[i]![j]!
      v := v.set! i acc
    A := A.push v
  let K := kernel A g
  let Q := matMul K G ncols
  -- project onto the open slots of `m'`
  let sl' := slotsOf W m'
  let mut cols : Array Nat := #[]
  for (kind, b) in sl' do
    cols := cols.push (if kind == 0 then v0[b]! else v2[b]!)
  let mut Pr : Array (Array Rat) := #[]
  for row in Q do
    let mut v : Array Rat := #[]
    for c in cols do v := v.push row[c]!
    Pr := Pr.push v
  let (P', _) := rref Pr cols.size
  let k' := st.k + (Q.size - P'.size)
  if k' > 3 then return none
  return some ⟨m', k', P'⟩

/-- Close the state set by breadth-first search. Returns the states, their keys, the transition
list `(from, m', to)`, and whether the closure succeeded within `cap`. -/
def closure (W cap : Nat) :
    Array State × Array (Nat × Nat × Nat) × Bool := Id.run do
  let S := 1 <<< W
  let init : State := ⟨0, 0, #[]⟩
  let mut states : Array State := #[init]
  let mut idx : HashMap String Nat := (HashMap.emptyWithCapacity 1024).insert init.key 0
  let mut trans : Array (Nat × Nat × Nat) := #[]
  let mut frontier : Array Nat := #[0]
  let mut ok := true
  while frontier.size > 0 && ok do
    let mut next : Array Nat := #[]
    for i in frontier do
      for m' in [1:S] do
        match step W states[i]! m' with
        | none => pure ()
        | some st' =>
          let key := st'.key
          match idx[key]? with
          | some j => trans := trans.push (i, m', j)
          | none =>
            if states.size ≥ cap then ok := false
            else
              let j := states.size
              states := states.push st'
              idx := idx.insert key j
              next := next.push j
              trans := trans.push (i, m', j)
    frontier := next
  return (states, trans, ok)

/-- `A_W(n)`: sets in rows `0 … W−1` up to horizontal translation, columns contiguous and
nonempty, line-nullity 3. -/
def seriesA (W N cap : Nat) : Array Nat × Nat × Bool := Id.run do
  let (states, trans, ok) := closure W cap
  if !ok then return (#[], states.size, false)
  let mut acc : Array Bool := #[]
  for st in states do acc := acc.push (st.k + st.basis.size == 3)
  let ns := states.size
  -- cnt[n * ns + s]
  let mut cnt := Array.replicate ((N+1) * ns) (0 : Nat)
  cnt := cnt.set! 0 1
  for n in [1:N+1] do
    for (i, m', j) in trans do
      let w := pc m'
      if w ≤ n then
        let v := cnt[(n - w) * ns + i]!
        if v != 0 then cnt := cnt.set! (n * ns + j) (cnt[n * ns + j]! + v)
  let mut out : Array Nat := #[]
  for n in [0:N+1] do
    let mut s := 0
    for t in [0:ns] do
      if acc[t]! then s := s + cnt[n * ns + t]!
    out := out.push s
  return (out, ns, true)

/-! ## Linear recurrences -/

/-- Smallest `d ≤ maxD` such that some `c` satisfies `a n = Σ_{i=1}^d c i * a (n−i)` for every
`n` in `[n₀, N]` with `n₀ ≤ N − 3d`. `c` is fitted on the top `d` equations, so the fit is only
accepted when it then reproduces a long stretch below. Returns `(d, c, n₀)`. -/
def findRec (a : Array Nat) (maxD : Nat) : Option (Array Rat × Nat) := Id.run do
  let N := a.size - 1
  let q : Nat → Rat := fun n => Rat.ofInt (Int.ofNat a[n]!)
  for d in [1:maxD+1] do
    if 4 * d + 2 ≤ N then
      let mut M : Array (Array Rat) := #[]
      for r in [0:d] do
        let n := N - d + 1 + r
        let mut row : Array Rat := #[]
        for i in [1:d+1] do row := row.push (q (n-i))
        row := row.push (q n)
        M := M.push row
      let (R, piv) := rref M (d + 1)
      if !piv.contains d && piv.size == d then
        let mut c := Array.replicate d (0 : Rat)
        for i in [0:R.size] do c := c.set! piv[i]! (R[i]![d]!)
        let holds (n : Nat) : Bool := Id.run do
          let mut s : Rat := 0
          for i in [1:d+1] do s := s + c[i-1]! * q (n-i)
          return s == q n
        -- smallest n₀ with the recurrence valid throughout [n₀, N]
        let mut n0 := N + 1
        let mut n := N
        while n ≥ d && holds n do
          n0 := n
          n := n - 1
        if n0 ≤ N - 3 * d then return some (c, n0)
  return none

/-- numerator of the rational GF, given the recurrence; `none` if it does not terminate. -/
def numerator (a : Array Nat) (c : Array Rat) : Option (Array Rat) := Id.run do
  let N := a.size - 1
  let d := c.size
  let q : Nat → Rat := fun n => Rat.ofInt (Int.ofNat a[n]!)
  let mut p : Array Rat := #[]
  for n in [0:N+1] do
    let mut s := q n
    for i in [1:d+1] do
      if i ≤ n then s := s - c[i-1]! * q (n-i)
    p := p.push s
  -- highest nonzero coefficient
  let mut hi := 0
  for n in [0:N+1] do
    if p[n]! != 0 then hi := n
  if hi + 2 * d ≥ N then return none
  return some (p.extract 0 (hi+1))

/-- per-circle growth: the reciprocal of the smallest positive root of `1 − Σ cᵢ xⁱ`. -/
def growth (c : Array Rat) : Float := Id.run do
  let d := c.size
  let g (x : Float) : Float := Id.run do
    let mut s : Float := 1
    for i in [1:d+1] do
      s := s - Float.ofInt c[i-1]!.num / Float.ofNat c[i-1]!.den * x ^ (Float.ofNat i)
    return s
  let mut lo : Float := 0
  let mut found := false
  let mut t : Float := 0
  while !found && t < 1.0 do
    t := t + 1e-5
    if g t ≤ 0 then
      found := true
      lo := t - 1e-5
  if !found then return 0
  let mut hi := t
  for _ in [0:120] do
    let mid := (lo + hi) / 2
    if g mid > 0 then lo := mid else hi := mid
  return 2 / (lo + hi)

def ratStr (c : Array Rat) : String :=
  String.intercalate " " (c.toList.map fun x => if x.den == 1 then s!"{x.num}" else s!"{x.num}/{x.den}")

def scanMode (W N maxD : Nat) : IO Unit := do
  let mut As : Array (Array Nat) := #[Array.replicate (N+1) 0]   -- A_0 = 0
  for w in [1:W+1] do
    let t0 ← IO.monoMsNow
    let (a, ns, ok) := seriesA w N 20000
    let t1 ← IO.monoMsNow
    if !ok then
      IO.println s!"W={w}: state closure FAILED (over {ns} states)"
      return
    IO.println s!"W={w}: {ns} states, {t1-t0} ms"
    As := As.push a
  IO.println ""
  IO.println "# A_W(n) = sets in rows 0..W-1 (horizontal translation only), nullity 3"
  let shown := min N 30
  let hdr := String.intercalate " " ((List.range (W+1)).map fun w => s!"A{w}")
  IO.println s!"n {hdr}"
  for n in [1:shown+1] do
    let row := String.intercalate " " ((List.range (W+1)).map fun w => s!"{As[w]![n]!}")
    IO.println s!"{n} {row}"
  IO.println ""
  IO.println "# T_W(n) = A_W - 2A_{W-1} + A_{W-2}: fixed count, b-span exactly W"
  for w in [2:W+1] do
    let mut t : Array Nat := #[]
    for n in [0:N+1] do
      let v : Int := Int.ofNat As[w]![n]! - 2 * Int.ofNat As[w-1]![n]! + Int.ofNat As[w-2]![n]!
      t := t.push v.toNat
      if v < 0 then IO.println s!"  NEGATIVE T_{w}({n}) = {v}"
    IO.println s!"T{w}: {(t.toList.drop 2).take 40}"
    let r := t[t.size-1]!
    let r2 := t[t.size-2]!
    if r2 != 0 then
      IO.println s!"  T{w}: last ratio {Float.ofNat r / Float.ofNat r2}"
    match findRec t maxD with
    | none => IO.println s!"  T{w}: no linear recurrence of order ≤ {maxD} found"
    | some (c, n0) =>
      IO.println s!"  T{w}: order {c.size}, valid from n = {n0}, a(n) = Σ cᵢ a(n−i) with \
cᵢ = {ratStr c}"
      IO.println s!"  T{w}: denominator 1 − ({ratStr c})·(x, x², …)"
      match numerator t c with
      | none => IO.println s!"  T{w}: numerator not determined within the series"
      | some p => IO.println s!"  T{w}: numerator coefficients {ratStr p}"
      let mut dsum : Rat := 1
      for x in c do dsum := dsum - x
      IO.println s!"  T{w}: denominator at x = 1 is {dsum} (zero ⟺ (1−x) divides it)"
      IO.println s!"  T{w}: per-circle growth {growth c}"

/-- Exact series without needing the state set to close: a layered dynamic program over the
number of columns. A set of `n` circles occupies at most `n` columns, so `N` layers suffice for
`A_W(n)`, `n ≤ N`. States are interned and transitions memoised, so the cost is one `step` per
(state, mask) pair actually met. -/
def seriesLayered (W N : Nat) : Array Nat × Nat := Id.run do
  let S := 1 <<< W
  let init : State := ⟨0, 0, #[]⟩
  let mut states : Array State := #[init]
  let mut idx : HashMap String Nat := (HashMap.emptyWithCapacity 8192).insert init.key 0
  let mut memo : HashMap (Nat × Nat) (Option Nat) := HashMap.emptyWithCapacity 65536
  let mut out := Array.replicate (N+1) (0 : Nat)
  -- layer: state index ↦ counts by circles used
  let mut layer : HashMap Nat (Array Nat) :=
    HashMap.emptyWithCapacity 1024 |>.insert 0 ((Array.replicate (N+1) (0 : Nat)).set! 0 1)
  for _col in [1:N+1] do
    let mut next : HashMap Nat (Array Nat) := HashMap.emptyWithCapacity 4096
    for (i, cnt) in layer do
      for m' in [1:S] do
        let w := pc m'
        -- is there anything left to shift?
        let mut any := false
        for n in [0:N+1-w] do
          if cnt[n]! != 0 then any := true
        if any then
          let tgt : Option Nat ←
            match memo[(i, m')]? with
            | some t => pure t
            | none =>
              match step W states[i]! m' with
              | none => memo := memo.insert (i, m') none; pure none
              | some st' =>
                match idx[st'.key]? with
                | some j => memo := memo.insert (i, m') (some j); pure (some j)
                | none =>
                  let j := states.size
                  states := states.push st'
                  idx := idx.insert st'.key j
                  memo := memo.insert (i, m') (some j)
                  pure (some j)
          match tgt with
          | none => pure ()
          | some j =>
            let mut acc := (next[j]?).getD (Array.replicate (N+1) 0)
            for n in [0:N+1-w] do
              if cnt[n]! != 0 then acc := acc.set! (n+w) (acc[n+w]! + cnt[n]!)
            next := next.insert j acc
    for (j, cnt) in next do
      let st := states[j]!
      if st.k + st.basis.size == 3 then
        for n in [0:N+1] do
          if cnt[n]! != 0 then out := out.set! n (out[n]! + cnt[n]!)
    layer := next
  return (out, states.size)

/-- Diagnostic: BFS by levels, reporting new states and the arithmetic size of their
subspaces, to see whether the reachable subspaces close up. -/
def probeMode (W cap : Nat) : IO Unit := do
  let S := 1 <<< W
  let init : State := ⟨0, 0, #[]⟩
  let mut states : Array State := #[init]
  let mut idx : HashMap String Nat := (HashMap.emptyWithCapacity 4096).insert init.key 0
  let mut frontier : Array Nat := #[0]
  let mut depth := 0
  IO.println s!"# W = {W}: BFS by column count"
  IO.println "depth newStates total maxNum maxDen maxDimP"
  while frontier.size > 0 && states.size < cap do
    depth := depth + 1
    let mut next : Array Nat := #[]
    let mut mx : Int := 0
    let mut md : Nat := 1
    let mut mdim := 0
    for i in frontier do
      for m' in [1:S] do
        match step W states[i]! m' with
        | none => pure ()
        | some st' =>
          let key := st'.key
          if !idx.contains key then
            if states.size < cap then
              idx := idx.insert key states.size
              next := next.push states.size
              states := states.push st'
              if st'.basis.size > mdim then mdim := st'.basis.size
              for row in st'.basis do
                for x in row do
                  let a := x.num.natAbs
                  if Int.ofNat a > mx then mx := Int.ofNat a
                  if x.den > md then md := x.den
    IO.println s!"{depth} {next.size} {states.size} {mx} {md} {mdim}"
    frontier := next
  IO.println s!"# stopped: {states.size} states after depth {depth}"

def layerMode (W N maxD : Nat) : IO Unit := do
  let mut As : Array (Array Nat) := #[Array.replicate (N+1) 0]
  for w in [1:W+1] do
    let t0 ← IO.monoMsNow
    let (a, ns) := seriesLayered w N
    let t1 ← IO.monoMsNow
    IO.println s!"W={w}: {ns} distinct states within {N} columns, {t1-t0} ms"
    As := As.push a
  IO.println ""
  for w in [2:W+1] do
    let mut t : Array Nat := #[]
    for n in [0:N+1] do
      let v : Int := Int.ofNat As[w]![n]! - 2 * Int.ofNat As[w-1]![n]! + Int.ofNat As[w-2]![n]!
      if v < 0 then IO.println s!"  NEGATIVE T_{w}({n}) = {v}"
      t := t.push v.toNat
    IO.println s!"T{w}: {(t.toList.drop 2)}"
    if t.size ≥ 3 then
      let r := t[t.size-1]!
      let r2 := t[t.size-2]!
      if r2 != 0 then IO.println s!"  T{w}: last ratio {Float.ofNat r / Float.ofNat r2}"
    match findRec t maxD with
    | none => IO.println s!"  T{w}: NO linear recurrence of order ≤ {maxD} within {N} terms"
    | some (c, n0) =>
      IO.println s!"  T{w}: order {c.size}, valid from n = {n0}, cᵢ = {ratStr c}"
      match numerator t c with
      | none => IO.println s!"  T{w}: numerator not determined"
      | some p => IO.println s!"  T{w}: numerator {ratStr p}"
      let mut dsum : Rat := 1
      for x in c do dsum := dsum - x
      IO.println s!"  T{w}: denominator at x = 1 is {dsum} (zero ⟺ (1−x) divides it)"
      IO.println s!"  T{w}: per-circle growth {growth c}"

def main (args : List String) : IO Unit := do
  match args with
  | ["layer", w, n] => layerMode (w.toNat!) (n.toNat!) 30
  | ["layer", w, n, d] => layerMode (w.toNat!) (n.toNat!) (d.toNat!)
  | ["probe", w, c] => probeMode (w.toNat!) (c.toNat!)
  | ["scan", w, n] => scanMode (w.toNat!) (n.toNat!) 30
  | ["scan", w, n, d] => scanMode (w.toNat!) (n.toNat!) (d.toNat!)
  | _ => IO.println "usage: scan W N [maxOrder]"

end TM

def main (args : List String) : IO Unit := TM.main args
