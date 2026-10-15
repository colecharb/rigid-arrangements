namespace OL

/-- apex at distance 1 from `p` and `q` (diameter-1 units), branch σ -/
def apexF (p q : CF) (σ : Float) : Option CF :=
  let w := csub q p
  let d2 := cabs2 w
  if d2 > 4 || d2 < 1e-18 then none else
  let h := Float.sqrt (max 0 (1 / d2 - 0.25))
  some ⟨(p.x + q.x) / 2 - σ * h * w.y, (p.y + q.y) / 2 + σ * h * w.x⟩

/-- Type D2: bodies B1, B2 sharing a hinge; free circles f1 (touching a1 ∈ B1, b1 ∈ B2) and
f2 (touching a2 ∈ B1, b2 ∈ B2) touching each other. Float 1-D search over the hinge angle. -/
def enumD2 (bodies : Array (Array (Array Pt))) (n : Nat) (M : Nat := 720) :
    Array FHit × Nat × Nat := Id.run do
  let mut hits := #[]
  let mut nComb := 0
  let mut nLat := 0
  for s1 in [3:n] do
    if n ≥ s1 + 4 then
      let s2 := n - 1 - s1
      if s2 ≥ 3 && s1 ≤ s2 && s2 < bodies.size then
        for b1 in [0:bodies[s1]!.size] do
          let B1 := bodies[s1]![b1]!
          let B1f := B1.map ofLatF
          for b2 in [0:bodies[s2]!.size] do
            for mir in [false, true] do
              let B2 : Array Pt := if mir then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
              let B2f := B2.map ofLatF
              for h1 in [0:s1] do
                for h2 in [0:s2] do
                  let H1 := B1f[h1]!
                  let H2 := B2f[h2]!
                  let rel (w : CF) : CF := csub w H2
                  -- hinge angles where the two bodies do not overlap (slack 0.05)
                  let mut mask : Array Bool := Array.replicate M false
                  let mut anyOk := false
                  for t in [0:M] do
                    let R := cexpi (6.283185307179586 * Float.ofNat t / Float.ofNat M)
                    let mut ok := true
                    for iw in [0:s2] do
                      if ok && iw != h2 then
                        let P := cadd H1 (cmul R (rel B2f[iw]!))
                        for iz in [0:s1] do
                          if ok && iz != h1 && cfd2 P B1f[iz]! < 0.95 then ok := false
                    if ok then
                      mask := mask.set! t true
                      anyOk := true
                  let allowed (θ : Float) : Bool :=
                    let t := (Float.round (θ / 6.283185307179586 * Float.ofNat M)).toUInt64.toNat % M
                    mask[t]!
                  if anyOk then
                    for a1 in [0:s1] do
                      for bb1 in [0:s2] do
                        if !(a1 == h1 && bb1 == h2) then
                          let ra1 := Float.sqrt (cfd2 B1f[a1]! H1)
                          let rb1 := Float.sqrt (cfd2 B2f[bb1]! H2)
                          if (ra1 - rb1).abs ≤ 2 + 1e-9 then
                            for a2 in [0:s1] do
                              for bb2 in [0:s2] do
                                if !(a2 == h1 && bb2 == h2) && (a1 < a2 || (a1 == a2 && bb1 < bb2)) && !(a1 == a2 && bb1 == bb2) then
                                  let ra2 := Float.sqrt (cfd2 B1f[a2]! H1)
                                  let rb2 := Float.sqrt (cfd2 B2f[bb2]! H2)
                                  if (ra2 - rb2).abs ≤ 2 + 1e-9 && cfd2 B1f[a1]! B1f[a2]! ≤ 9 + 1e-9 && cfd2 B2f[bb1]! B2f[bb2]! ≤ 9 + 1e-9 then
                                    nComb := nComb + 1
                                    for σ1 in [1.0, -1.0] do
                                      for σ2 in [1.0, -1.0] do
                                        let place (θ : Float) : Option (CF × CF × CF) := do
                                          let R := cexpi θ
                                          let pb1 := cadd H1 (cmul R (rel B2f[bb1]!))
                                          let pb2 := cadd H1 (cmul R (rel B2f[bb2]!))
                                          let f1 ← apexF B1f[a1]! pb1 σ1
                                          let f2 ← apexF B1f[a2]! pb2 σ2
                                          return (R, f1, f2)
                                        let f (θ : Float) : Option Float := do
                                          if !allowed θ then none
                                          let (_, f1, f2) ← place θ
                                          return cfd2 f1 f2 - 1
                                        let (roots, tang) := scanRoots f M
                                        let isolated (α : Float) : Bool :=
                                          match f (α - 1e-4), f (α + 1e-4) with
                                          | some a, some b => a.abs > 1e-12 && b.abs > 1e-12
                                          | _, _ => true
                                        for θ in (roots ++ tang).filter isolated do
                                          match place θ with
                                          | none => pure ()
                                          | some (R, f1, f2) =>
                                            let mut P2 : Array CF := #[]
                                            for iw in [0:s2] do
                                              if iw != h2 then P2 := P2.push (cadd H1 (cmul R (rel B2f[iw]!)))
                                            let P := B1f ++ P2 ++ #[f1, f2]
                                            let an := analyzeF P
                                            if !an.overlap && an.lattice then nLat := nLat + 1
                                            if !an.overlap && !an.lattice then
                                              let rk := rigRankPF P an.contacts
                                              hits := hits.push { pts := P, info := s!"D2 s=({s1},{s2}) B1={s1}#{b1} B2={s2}#{b2}{if mir then "m" else ""} hinge=({h1},{h2}) f1~({a1},{bb1}) f2~({a2},{bb2}) sig=({σ1},{σ2}) theta={θ} contacts={an.contacts.size} core={an.core} rank={rk}/{2*n-3} tangential={tang.contains θ}" }
  return (hits, nComb, nLat)

end OL
