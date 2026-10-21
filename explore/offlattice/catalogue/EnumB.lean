namespace OL

def cabs2 (a : CF) : Float := a.x * a.x + a.y * a.y
def csub (a b : CF) : CF := ⟨a.x - b.x, a.y - b.y⟩
def cexpi (t : Float) : CF := ⟨Float.cos t, Float.sin t⟩

/-- intersection of circle(c1, r1) and circle(c2, r2); branch σ = ±1. -/
def circInt (c1 : CF) (r1 : Float) (c2 : CF) (r2 : Float) (σ : Float) : Option CF :=
  let d := csub c2 c1
  let D2 := cabs2 d
  if D2 < 1e-18 then none else
  let a := (r1 * r1 - r2 * r2 + D2) / (2 * D2)   -- along d, as fraction
  let h2 := r1 * r1 / D2 - a * a                   -- (perp/|d|)^2
  if h2 < 0 then none else
  let h := Float.sqrt h2
  some ⟨c1.x + a * d.x - σ * h * d.y, c1.y + a * d.y + σ * h * d.x⟩

/-- a generic float placement result of a 1-parameter closing search -/
structure FHit where
  pts : Array CF
  info : String
  deriving Inhabited

/-- find roots of `f` on `[0, 2π)` (sign changes on a grid, then bisection);
`f` returns `none` where undefined. Also flags near-tangential minima. -/
def scanRoots (f : Float → Option Float) (M : Nat := 2000) : Array Float × Array Float := Id.run do
  let twoPi := 6.283185307179586
  let mut roots := #[]
  let mut tang := #[]
  let mut prevT := 0.0
  let mut prev : Option Float := f 0
  let mut prev2 : Option Float := none
  let mut prevT2 := 0.0
  for i in [1:M+1] do
    let t := twoPi * (Float.ofNat i) / (Float.ofNat M)
    let cur := f t
    match prev, cur with
    | some a, some b =>
      if a == 0 then roots := roots.push prevT
      else if a * b < 0 then
        let mut lo := prevT
        let mut hi := t
        let mut flo := a
        for _ in [0:80] do
          let mid := (lo + hi) / 2
          match f mid with
          | some fm =>
            if flo * fm ≤ 0 then hi := mid else
              lo := mid
              flo := fm
          | none => hi := mid
        roots := roots.push ((lo + hi) / 2)
      -- tangency check: local min of |f| without sign change
      match prev2 with
      | some c =>
        if a.abs < c.abs && a.abs < b.abs && a.abs < 1e-3 && a * b > 0 && a * c > 0 then
          -- golden-section minimize |f| on [prevT2, t]
          let mut lo := prevT2
          let mut hi := t
          for _ in [0:100] do
            let m1 := lo + (hi - lo) * 0.381966
            let m2 := lo + (hi - lo) * 0.618034
            let v1 := (f m1).getD 1e9
            let v2 := (f m2).getD 1e9
            if v1.abs < v2.abs then hi := m2 else lo := m1
          let tm := (lo + hi) / 2
          if ((f tm).getD 1).abs < 1e-10 then tang := tang.push tm
      | none => pure ()
    | _, _ => pure ()
    prev2 := prev
    prevT2 := prevT
    prev := cur
    prevT := t
  return (roots, tang)

/-- float contacts/overlap/core analysis of a float configuration -/
structure FAnal where
  overlap : Bool
  contacts : Array (Nat × Nat)
  core : Bool
  lattice : Bool
  deriving Inhabited

def analyzeF (P : Array CF) : FAnal := Id.run do
  let n := P.size
  let mut cs := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      let d := cfd2 P[i]! P[j]!
      if d < 1 - 1e-7 then return { overlap := true, contacts := #[], core := false, lattice := false }
      if d < 1 + 1e-7 then cs := cs.push (i, j)
  let mut nb := Array.replicate n (#[] : Array Nat)
  for (i, j) in cs do
    nb := nb.modify i (·.push j)
    nb := nb.modify j (·.push i)
  let mut core := true
  for i in [0:n] do
    if nb[i]!.size < 2 then core := false
    if nb[i]!.size == 2 then
      if cfd2 P[nb[i]![0]!]! P[nb[i]![1]!]! < 4 - 1e-7 then core := false
  -- lattice: all contact directions differ by multiples of 60°
  let mut lat := true
  if cs.size > 0 then
    let d0 := csub P[cs[0]!.2]! P[cs[0]!.1]!
    for (i, j) in cs do
      let d := csub P[j]! P[i]!
      let w := cmul d (cconj d0)
      let w6 := cmul (cmul (cmul w w) w) (cmul (cmul w w) w)
      if (w6.x - 1).abs > 1e-6 || w6.y.abs > 1e-6 then lat := false
  return { overlap := false, contacts := cs, core, lattice := lat }

def rigRankPF (P : Array CF) (cs : Array (Nat × Nat)) : Nat :=
  let A : ExArr := { T := Tower.base, pts := P.map (fun _ => Cx.zero), pf := P, contacts := cs }
  A.rigRankF

/-- Type B: two lattice bodies joined by three disjoint bars; float search. -/
def enumB (bodies : Array (Array (Array Pt))) (n : Nat) (M : Nat := 2000) :
    Array FHit × Nat × Nat × Nat × Nat := Id.run do
  let mut hits := #[]
  let mut nComb := 0
  let mut nTang := 0
  let mut nDeg := 0
  let mut nLat := 0
  for s1 in [3:n] do
    let s2 := n - s1
    if s2 ≥ 3 && s1 ≤ s2 && s2 < bodies.size then
      for b1 in [0:bodies[s1]!.size] do
        let B1 := bodies[s1]![b1]!
        let B1f := B1.map ofLatF
        for b2 in [0:bodies[s2]!.size] do
          for mir in [false, true] do
            let B2 : Array Pt := if mir then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
            let B2f := B2.map ofLatF
            for x1 in [0:s1] do
              for x2 in [x1+1:s1] do
                for x3 in [x2+1:s1] do
                  let X := #[B1f[x1]!, B1f[x2]!, B1f[x3]!]
                  for y1 in [0:s2] do
                    for y2 in [0:s2] do
                      for y3 in [0:s2] do
                        if y1 != y2 && y1 != y3 && y2 != y3 then
                          let Y := #[B2f[y1]!, B2f[y2]!, B2f[y3]!]
                          -- prune: |Yi - Yj| within |Xi - Xj| ± 2
                          let mut okp := true
                          for (i, j) in [(0,1),(0,2),(1,2)] do
                            let dx := Float.sqrt (cfd2 X[i]! X[j]!)
                            let dy := Float.sqrt (cfd2 Y[i]! Y[j]!)
                            if dy > dx + 2 + 1e-9 || dy < dx - 2 - 1e-9 then okp := false
                          if okp then
                            nComb := nComb + 1
                            let D12 := Float.sqrt (cfd2 Y[0]! Y[1]!)
                            let dY := csub Y[1]! Y[0]!
                            for σ in [1.0, -1.0] do
                              let place (α : Float) : Option (CF × CF) := do
                                let p1 := cadd X[0]! (cexpi α)
                                let p2 ← circInt p1 D12 X[1]! 1 σ
                                -- R = (p2 - p1) / dY  (|.| = 1)
                                let R := csc (1 / (D12 * D12)) (cmul (csub p2 p1) (cconj dY))
                                let t := csub p1 (cmul R Y[0]!)
                                return (R, t)
                              let f (α : Float) : Option Float := do
                                let (R, t) ← place α
                                let p3 := cadd t (cmul R Y[2]!)
                                return cfd2 p3 X[2]! - 1
                              let (roots, tang) := scanRoots f M
                              nTang := nTang + tang.size
                              -- identically vanishing residual (sliding family): skip
                              let mut nz := 0
                              for i in [0:64] do
                                match f (6.283185307179586 * Float.ofNat i / 64) with
                                | some v => if v.abs < 1e-9 then nz := nz + 1
                                | none => pure ()
                              if nz ≥ 3 then nDeg := nDeg + 1
                              let isolated (α : Float) : Bool :=
                                match f (α - 1e-4), f (α + 1e-4) with
                                | some a, some b => a.abs > 1e-12 && b.abs > 1e-12
                                | _, _ => true
                              let roots := roots.filter isolated
                              let tang := tang.filter isolated
                              for α in roots ++ tang do
                                match place α with
                                | none => pure ()
                                | some (R, t) =>
                                  let P2 := B2f.map fun w => cadd t (cmul R w)
                                  let P := B1f ++ P2
                                  let an := analyzeF P
                                  if !an.overlap && an.lattice then nLat := nLat + 1
                                  if !an.overlap && !an.lattice then
                                    let rk := rigRankPF P an.contacts
                                    hits := hits.push { pts := P, info := s!"B s=({s1},{s2}) B1={s1}#{b1} B2={s2}#{b2}{if mir then "m" else ""} x=({x1},{x2},{x3}) y=({y1},{y2},{y3}) sigma={σ} alpha={α} contacts={an.contacts.size} core={an.core} rank={rk}/{2*n-3} tangential={tang.contains α}" }
  return (hits, nComb, nTang, nDeg, nLat)

end OL
