open OL in
def main : IO Unit := do
  let b := latticeBodies 12
  for (s, i) in [(5,0),(6,0),(6,1),(6,2),(9,14),(9,1),(9,9)] do
    IO.println s!"body {s}#{i}: sites (a,b) ↦ 2a + b(1+i√3): {b[s]![i]!}"
