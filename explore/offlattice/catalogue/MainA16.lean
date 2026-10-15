open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "16").toNat!
  let bodies := latticeBodies 14
  for n in [15:N+1] do
    let F := enumA bodies n {}
    IO.println s!"n={n}: Type A off-lattice assemblies={F.all.arrs.size} cores={F.cores.arrs.size}"
    for A in F.cores.arrs do
      IO.println s!"   core: {A.info} contacts={A.contacts.size} irreducible-by-count={A.contacts.size == 2*n-3}"
