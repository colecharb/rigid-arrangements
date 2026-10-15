namespace OL

def sqrt3F : Float := Float.sqrt 3

def ofLatF (v : Pt) : CF := ⟨Float.ofInt v.1 + Float.ofInt v.2 / 2, Float.ofInt v.2 * sqrt3F / 2⟩
def cmul (a b : CF) : CF := ⟨a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x⟩
def cconj (a : CF) : CF := ⟨a.x, -a.y⟩
def cadd (a b : CF) : CF := ⟨a.x + b.x, a.y + b.y⟩
def csc (c : Float) (a : CF) : CF := ⟨c * a.x, c * a.y⟩

def isLatRotF (R : CF) : Bool :=
  let R2 := cmul R R
  let R3 := cmul R2 R
  let R6 := cmul R3 R3
  (R6.x - 1).abs < 1e-9 && R6.y.abs < 1e-9

/-- ordered pairs of distinct indices up to the automorphisms of the body -/
def pairOrbits (S : Array Pt) : Array (Nat × Nat) := Id.run do
  let auts := autPerms S
  let mut seen : Std.HashSet (Nat × Nat) := {}
  let mut out := #[]
  for i in [0:S.size] do
    for j in [0:S.size] do
      if i != j && !seen.contains (i, j) then
        out := out.push (i, j)
        for pm in auts do seen := seen.insert (pm[i]!, pm[j]!)
  return out

structure Found where
  all : Store := {}
  cores : Store := {}
  nCand : Nat := 0
  nExact : Nat := 0
  wantLat : Bool := false
  latCores : Array ExArr := #[]
  deriving Inhabited

def Found.add (F : Found) (A : ExArr) : Found := Id.run do
  let F := { F with nExact := F.nExact + 1 }
  match A.validate with
  | none => return F
  | some A =>
    if !A.connected then return F
    if A.onLattice then
      if F.wantLat && A.isCore then return { F with latCores := F.latCores.push A }
      return F
    let (all, _, _) := F.all.insert A
    let mut cores := F.cores
    if A.isCore then
      let (c, _, _) := cores.insert A
      cores := c
    return { F with all, cores }

/-- exact rotation `R = g (m - iε√Δ) / (2pq)`; returns tower, level, R. -/
def hingeRot (u v : Pt) (p q m Δ : Int) (ε : Int) : Tower × Cx := Id.run do
  let T0 := Tower.base
  let (T, sD, _) := T0.sqrtOrPush (.q Δ)
  let k := T.lvl
  let g1 := Cx.mul T0.rad 1 (Cx.ofLat u.1 u.2) (Cx.conj (Cx.ofLat v.1 v.2))
  let g := Cx.lift (k - 1) g1
  let fac : Cx := ⟨.q m, tScale (-(ε : Rat)) sD⟩
  let R := Cx.scale (1 / (2 * (p * q : Rat))) (Cx.mul T.rad k g fac)
  return (T, R)

/-- Type A: bodies `B1` (size s1) and `B2` (size s2), hinge + bar. -/
def enumA (bodies : Array (Array (Array Pt))) (n : Nat) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for s1 in [3:n] do
    let s2 := n + 1 - s1
    if s2 ≥ 3 && s1 ≤ s2 && s2 < bodies.size then
      for b1 in [0:bodies[s1]!.size] do
        let B1 := bodies[s1]![b1]!
        let pr1 := pairOrbits B1
        let B1f := B1.map ofLatF
        for b2 in [0:bodies[s2]!.size] do
          for mir in [false, true] do
            let B2 : Array Pt := if mir then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
            for ih2 in [0:s2] do
              for iy in [0:s2] do
                if iy != ih2 then
                  let h2 := B2[ih2]!
                  let y := B2[iy]!
                  let v := psub y h2
                  let q := eN v
                  for (ih1, ix) in pr1 do
                    let h1 := B1[ih1]!
                    let x := B1[ix]!
                    let u := psub x h1
                    let p := eN u
                    let m := p + q - 1
                    let Δ := 4 * p * q - m * m
                    if Δ ≥ 0 then
                      let eps : List Int := if Δ == 0 then [1] else [1, -1]
                      for ε in eps do
                        F := { F with nCand := F.nCand + 1 }
                        let g := cmul (ofLatF u) (cconj (ofLatF v))
                        let fac : CF := ⟨Float.ofInt m, -(Float.ofInt ε) * Float.sqrt (Float.ofInt Δ)⟩
                        let R := csc (1 / (2 * Float.ofInt (p * q))) (cmul g fac)
                        if F.wantLat || !isLatRotF R then
                          let h1f := ofLatF h1
                          let mut ok := true
                          for iw in [0:s2] do
                            if ok && iw != ih2 then
                              let P := cadd h1f (cmul R (ofLatF (psub B2[iw]! h2)))
                              for z in B1f do
                                if ok && cfd2 P z < 1 - 1e-6 then ok := false
                          if ok then
                            let (T, Rx) := hingeRot u v p q m Δ ε
                            let k := T.lvl
                            let mut pts : Array Cx := B1.map fun w => Cx.lift (k - 1) (Cx.ofLat w.1 w.2)
                            for iw in [0:s2] do
                              if iw != ih2 then
                                let w := Cx.lift (k - 1) (Cx.ofLat (B2[iw]!.1 - h2.1) (B2[iw]!.2 - h2.2))
                                pts := pts.push (Cx.add k (Cx.lift (k-1) (Cx.ofLat h1.1 h1.2)) (Cx.mul T.rad k Rx w))
                            let info := s!"A s=({s1},{s2}) B1={s1}#{b1} B2={s2}#{b2}{if mir then "m" else ""} hinge=({ih1},{ih2}) bar=({ix},{iy}) p={p} q={q} Delta={Δ} eps={ε}"
                            F := F.add (mkArr T pts info)
  return F

end OL
