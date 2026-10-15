open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "12").toNat!
  let lo := (args.getD 1 "6").toNat!
  let M := (args.getD 2 "2000").toNat!
  let bodies := latticeBodies 12
  for n in [lo:N+1] do
    let (hits, nComb, nTang, nDeg, nLat) := enumB bodies n M
    IO.println s!"B n={n}: combos={nComb} offlattice-nonoverlapping hits={hits.size} lattice hits={nLat} tangential={nTang} degenerate-families={nDeg}"
    for h in hits do
      IO.println s!"  {h.info}"
      IO.println s!"    pts={h.pts.map fun p => (p.x, p.y)}"
