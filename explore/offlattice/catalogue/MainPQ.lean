open OL in
def main : IO Unit := do
  -- eNorm values up to 28 and their vectors
  let mut vecs : Array (Int × Array Pt) := #[]
  for N in [1:29] do
    let mut vs2 : Array Pt := #[]
    for a in List.range 13 do
      for b in List.range 13 do
        let v : Pt := ((a : Int) - 6, (b : Int) - 6)
        if eN v == (N : Int) then vs2 := vs2.push v
    if vs2.size > 0 then vecs := vecs.push ((N : Int), vs2)
  IO.println s!"eNorm values: {vecs.map (·.1)}"
  for (p, us) in vecs do
    for (q, vs) in vecs do
      if p ≤ q then
        let m := p + q - 1
        let Δ := 4 * p * q - m * m
        if Δ ≥ 0 then
          -- off-lattice for which orientations? fix u = us[0], all v, ε = ±1, check R^6 = 1 in floats
          let u := us[0]!
          let mut nLat := 0
          let mut nOff := 0
          for v in vs do
            for ε in [1, -1] do
              let g := cmul (ofLatF u) (cconj (ofLatF v))
              let fac : CF := ⟨Float.ofInt m, -(Float.ofInt ε) * Float.sqrt (Float.ofInt Δ)⟩
              let R := csc (1 / (2 * Float.ofInt (p * q))) (cmul g fac)
              if isLatRotF R then nLat := nLat + 1 else nOff := nOff + 1
          let ang := Float.acos (Float.ofInt m / (2 * Float.sqrt (Float.ofInt (p * q)))) * 180 / 3.141592653589793
          IO.println s!"p={p} q={q} Δ={Δ} angle(HX,HY)={ang}° lattice-placements={nLat} off-lattice-placements={nOff}"
