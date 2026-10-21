namespace OL

/-- Type B with B1 an arbitrary (float) rigid arrangement and B2 a lattice body. -/
def enumBComp (B1f : Array CF) (B2s : Array (Array Pt)) (M : Nat := 1440) : Array FHit × Nat := Id.run do
  let mut hits := #[]
  let mut nComb := 0
  let s1 := B1f.size
  for b2 in [0:B2s.size] do
    for mir in [false, true] do
      let B2 : Array Pt := if mir then B2s[b2]!.map mirr else B2s[b2]!
      let B2f := B2.map ofLatF
      let s2 := B2.size
      for x1 in [0:s1] do
        for x2 in [x1+1:s1] do
          for x3 in [x2+1:s1] do
            let X := #[B1f[x1]!, B1f[x2]!, B1f[x3]!]
            for y1 in [0:s2] do
              for y2 in [0:s2] do
                for y3 in [0:s2] do
                  if y1 != y2 && y1 != y3 && y2 != y3 then
                    let Y := #[B2f[y1]!, B2f[y2]!, B2f[y3]!]
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
                          let R := csc (1 / (D12 * D12)) (cmul (csub p2 p1) (cconj dY))
                          let t := csub p1 (cmul R Y[0]!)
                          return (R, t)
                        let f (α : Float) : Option Float := do
                          let (R, t) ← place α
                          let p3 := cadd t (cmul R Y[2]!)
                          return cfd2 p3 X[2]! - 1
                        let (roots, tang) := scanRoots f M
                        let isolated (α : Float) : Bool :=
                          match f (α - 1e-4), f (α + 1e-4) with
                          | some a, some b => a.abs > 1e-12 && b.abs > 1e-12
                          | _, _ => true
                        for α in (roots ++ tang).filter isolated do
                          match place α with
                          | none => pure ()
                          | some (R, t) =>
                            let P := B1f ++ B2f.map fun w => cadd t (cmul R w)
                            let an := analyzeF P
                            if !an.overlap then
                              let rk := rigRankPF P an.contacts
                              hits := hits.push { pts := P, info := s!"Bcomp B2={s2}#{b2}{if mir then "m" else ""} x=({x1},{x2},{x3}) y=({y1},{y2},{y3}) contacts={an.contacts.size} core={an.core} rank={rk}/{2*P.size-3} lattice={an.lattice}" }
  return (hits, nComb)

end OL
