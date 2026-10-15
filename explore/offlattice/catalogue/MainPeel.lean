namespace OL
def ExArr.peel (A : ExArr) : ExArr := Id.run do
  let mut B := A
  let mut go := true
  while go do
    match B.removables[0]? with
    | none => go := false
    | some c =>
      let keep := (List.range B.n).filter (· != c) |>.toArray
      let pts := keep.map (B.pts[·]!)
      let C := mkArr B.T pts B.info
      B := C.validate.getD C
  return B
end OL

open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "14").toNat!
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  for m in [11:N+1] do
    let FA := enumA bodies m {}
    let FC := enumC bodies m {}
    seeds := seeds.set! m (FA.cores.arrs ++ FC.cores.arrs)
  let lv := closure seeds N 11
  -- catalogue of cores (all levels)
  let mut cores : Array (String × ExArr) := #[]
  for n in [11:N+1] do
    for (A, i) in (lv[n]!.arrs.filter (·.isCore)).zipIdx do
      cores := cores.push (s!"core{n}.{i}[{A.info}]", A)
  for (nm, A) in cores do
    IO.println s!"{nm}: n={A.n} contacts={A.contacts.size} irreducible(count&rank)={A.contacts.size == 2*A.n-3}"
  for n in [11:N+1] do
    let mut hist : Std.HashMap String Nat := {}
    for A in lv[n]!.arrs do
      let K := A.peel
      let mut name := "UNMATCHED"
      for (nm, C) in cores do
        if name == "UNMATCHED" && C.n == K.n && congruent K C then name := nm
      hist := hist.insert name (hist.getD name 0 + 1)
    IO.println s!"n={n}: total {lv[n]!.arrs.size}"
    for (nm, c) in hist.toArray do
      IO.println s!"   {c} peel to {nm}"
