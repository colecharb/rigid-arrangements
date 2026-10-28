namespace OL

def showArr (A : ExArr) : String := Id.run do
  let nb := A.nbrs
  let degs := nb.map (·.size)
  let mut s := s!"  n={A.n} contacts={A.contacts.size} (2n-3={2*A.n-3}) degs={degs} lvl={A.k} rad={repr A.T.rad}\n  {A.info}\n"
  for i in [0:A.n] do
    s := s ++ s!"    {i}: ({A.pf[i]!.x}, {A.pf[i]!.y})\n"
  return s

end OL

open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "12").toNat!
  let lo := (args.getD 1 "7").toNat!
  let bodies := latticeBodies 12
  IO.println s!"lattice bodies sizes 3..12: {(bodies.map (·.size)).toList.drop 3}"
  for n in [lo:N+1] do
    let F := enumA bodies n {}
    IO.println s!"n={n}: candidates={F.nCand} exact={F.nExact} offlattice-assemblies={F.all.arrs.size} cores={F.cores.arrs.size}"
    for A in F.cores.arrs do
      IO.println (showArr A)
