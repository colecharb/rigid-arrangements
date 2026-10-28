open OL in
def main (args : List String) : IO Unit := do
  let ns := (args.map String.toNat!)
  let bodies := latticeBodies 12
  for n in ns do
    let FA := enumA bodies n {}
    let FC := enumC bodies n {}
    IO.println s!"===== n={n}: Type A cores: {FA.cores.arrs.size}; Type C cores: {FC.cores.arrs.size}"
    for A in FA.cores.arrs ++ FC.cores.arrs do
      IO.println s!"--- {A.info}"
      IO.println s!"degrees: {A.nbrs.map (·.size)}; contacts {A.contacts.size} vs 2n-3 = {2*n-3}; exact rank {A.rigRank}"
      IO.println (describe A)
      IO.println s!"squared distances (radius-1 units): {distSpectrum A}"
