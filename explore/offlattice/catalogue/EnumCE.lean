namespace OL

/-- Type C: ring of three bodies, three hinges. B1 is a largest body (fixed orientation). -/
def enumC (bodies : Array (Array (Array Pt))) (n : Nat) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for s1 in [3:bodies.size] do
    for s2 in [3:s1+1] do
      if n + 3 ≥ s1 + s2 + 3 then
        let s3 := n + 3 - s1 - s2
        if s3 ≥ 3 && s3 ≤ s1 then
          for b1 in [0:bodies[s1]!.size] do
            let B1 := bodies[s1]![b1]!
            let pr1 := pairOrbits B1
            let B1f := B1.map ofLatF
            for b2 in [0:bodies[s2]!.size] do
              for mir2 in [false, true] do
                let B2 : Array Pt := if mir2 then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
                for b3 in [0:bodies[s3]!.size] do
                  for mir3 in [false, true] do
                    let B3 : Array Pt := if mir3 then (bodies[s3]![b3]!).map mirr else bodies[s3]![b3]!
                    for (i12, i13) in pr1 do
                      let a := psub B1[i13]! B1[i12]!
                      let e1 := eN a
                      for j12 in [0:s2] do
                        for j23 in [0:s2] do
                          if j12 != j23 then
                            let b := psub B2[j23]! B2[j12]!
                            let e2 := eN b
                            for k23 in [0:s3] do
                              for k13 in [0:s3] do
                                if k23 != k13 then
                                  let c := psub B3[k13]! B3[k23]!
                                  let e3 := eN c
                                  let m := e1 + e2 - e3
                                  let Δ := 4 * e1 * e2 - m * m
                                  if Δ ≥ 0 then
                                    let eps : List Int := if Δ == 0 then [1] else [1, -1]
                                    for ε in eps do
                                      F := { F with nCand := F.nCand + 1 }
                                      let g := cmul (ofLatF a) (cconj (ofLatF b))
                                      let fac : CF := ⟨Float.ofInt m, -(Float.ofInt ε) * Float.sqrt (Float.ofInt Δ)⟩
                                      let R2 := csc (1 / (2 * Float.ofInt (e1 * e2))) (cmul g fac)
                                      let h12f := ofLatF B1[i12]!
                                      let H23 := cadd h12f (cmul R2 (ofLatF b))
                                      let amb := cadd (ofLatF a) (csc (-1) (cmul R2 (ofLatF b)))
                                      let R3 := csc (1 / Float.ofInt e3) (cmul amb (cconj (ofLatF c)))
                                      let mut ok := !(isLatRotF R2 && isLatRotF R3)
                                      let mut P2 : Array CF := #[]
                                      for iw in [0:s2] do
                                        if ok && iw != j12 then
                                          let P := cadd h12f (cmul R2 (ofLatF (psub B2[iw]! B2[j12]!)))
                                          for z in B1f do
                                            if ok && cfd2 P z < 1 - 1e-6 then ok := false
                                          P2 := P2.push P
                                      if ok then
                                        for iw in [0:s3] do
                                          if ok && iw != k23 && iw != k13 then
                                            let P := cadd H23 (cmul R3 (ofLatF (psub B3[iw]! B3[k23]!)))
                                            for z in B1f do
                                              if ok && cfd2 P z < 1 - 1e-6 then ok := false
                                            for z in P2 do
                                              if ok && cfd2 P z < 1 - 1e-6 then ok := false
                                      if ok then
                                        -- exact
                                        let (T, R2x) := hingeRot a b e1 e2 m Δ ε
                                        let K := T.lvl
                                        let rad := T.rad
                                        let L (v : Pt) : Cx := Cx.lift (K - 1) (Cx.ofLat v.1 v.2)
                                        let h12 := L B1[i12]!
                                        let bx := L b
                                        let H23x := Cx.add K h12 (Cx.mul rad K R2x bx)
                                        let ambx := Cx.sub K (L a) (Cx.mul rad K R2x bx)
                                        let R3x := Cx.scale (1 / (e3 : Rat)) (Cx.mul rad K ambx (Cx.conj (L c)))
                                        let mut pts : Array Cx := B1.map L
                                        for iw in [0:s2] do
                                          if iw != j12 then
                                            pts := pts.push (Cx.add K h12 (Cx.mul rad K R2x (L (psub B2[iw]! B2[j12]!))))
                                        for iw in [0:s3] do
                                          if iw != k23 && iw != k13 then
                                            pts := pts.push (Cx.add K H23x (Cx.mul rad K R3x (L (psub B3[iw]! B3[k23]!))))
                                        let info := s!"C s=({s1},{s2},{s3}) B1={s1}#{b1} B2={s2}#{b2}{if mir2 then "m" else ""} B3={s3}#{b3}{if mir3 then "m" else ""} h12=({i12},{j12}) h13=({i13},{k13}) h23=({j23},{k23}) e=({e1},{e2},{e3}) Delta={Δ} eps={ε}"
                                        F := F.add (mkArr T pts info)
  return F

/-- Type E: two bodies sharing two circles at distance √N (N with ≥ 2 rotation orbits). -/
def enumE (bodies : Array (Array (Array Pt))) (n : Nat) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for s1 in [3:bodies.size] do
    let s2 := n + 2 - s1
    if s2 ≥ 3 && s1 ≤ s2 && s2 < bodies.size then
      for b1 in [0:bodies[s1]!.size] do
        let B1 := bodies[s1]![b1]!
        let pr1 := pairOrbits B1
        let B1f := B1.map ofLatF
        for b2 in [0:bodies[s2]!.size] do
          for mir in [false, true] do
            let B2 : Array Pt := if mir then (bodies[s2]![b2]!).map mirr else bodies[s2]![b2]!
            for (iu1, iv1) in pr1 do
              let a := psub B1[iv1]! B1[iu1]!
              let N := eN a
              if N ≥ 7 then
                for iu2 in [0:s2] do
                  for iv2 in [0:s2] do
                    if iu2 != iv2 && eN (psub B2[iv2]! B2[iu2]!) == N then
                      F := { F with nCand := F.nCand + 1 }
                      let b := psub B2[iv2]! B2[iu2]!
                      let R := csc (1 / Float.ofInt N) (cmul (ofLatF a) (cconj (ofLatF b)))
                      if !isLatRotF R then
                        let u1f := ofLatF B1[iu1]!
                        let mut ok := true
                        for iw in [0:s2] do
                          if ok && iw != iu2 && iw != iv2 then
                            let P := cadd u1f (cmul R (ofLatF (psub B2[iw]! B2[iu2]!)))
                            for z in B1f do
                              if ok && cfd2 P z < 1 - 1e-6 then ok := false
                        if ok then
                          let T := Tower.base
                          let rad := T.rad
                          let L (v : Pt) : Cx := Cx.ofLat v.1 v.2
                          let Rx := Cx.scale (1 / (N : Rat)) (Cx.mul rad 1 (L a) (Cx.conj (L b)))
                          let mut pts : Array Cx := B1.map L
                          for iw in [0:s2] do
                            if iw != iu2 && iw != iv2 then
                              pts := pts.push (Cx.add 1 (L B1[iu1]!) (Cx.mul rad 1 Rx (L (psub B2[iw]! B2[iu2]!))))
                          let info := s!"E s=({s1},{s2}) B1={s1}#{b1} B2={s2}#{b2}{if mir then "m" else ""} shared=({iu1},{iu2}),({iv1},{iv2}) N={N}"
                          F := F.add (mkArr T pts info)
  return F

end OL
