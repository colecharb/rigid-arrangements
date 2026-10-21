open OL in
def main : IO Unit := do
  let b := latticeBodies 12
  for (s, i) in [(8,6),(11,67),(11,29)] do
    IO.println s!"body {s}#{i}: {b[s]![i]!}"
