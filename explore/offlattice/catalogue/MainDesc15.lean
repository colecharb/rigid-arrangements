open OL in
def main : IO Unit := do
  let bodies := latticeBodies 14
  let F := enumA bodies 15 {}
  for A in F.cores.arrs do
    IO.println s!"--- {A.info}"
    IO.println s!"degrees: {A.nbrs.map (·.size)}; contacts {A.contacts.size} vs 2n-3 = 27; exact rank {A.rigRank}; onLattice={A.onLattice}"
    IO.println (describe A)
    IO.println s!"anatomy: {A.anatomy.signature}"
