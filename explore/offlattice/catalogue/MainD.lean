open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "12").toNat!
  let lo := (args.getD 1 "7").toNat!
  let M := (args.getD 2 "720").toNat!
  let bodies := latticeBodies 12
  for n in [lo:N+1] do
    let (hits, nComb, nLat) := enumD2 bodies n M
    IO.println s!"D2 n={n}: combos={nComb} offlattice-nonoverlapping hits={hits.size} lattice hits={nLat}"
    for h in hits do
      IO.println s!"  {h.info}"
      IO.println s!"    pts={h.pts.map fun p => (p.x, p.y)}"
