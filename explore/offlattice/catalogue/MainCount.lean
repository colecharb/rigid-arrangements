open OL in
def main : IO Unit := do
  let b := latticeBodies 14
  IO.println s!"rigid lattice sets in the Henneberg closure of a triangle, sizes 3..14: {(b.map (·.size)).toList.drop 3}"
