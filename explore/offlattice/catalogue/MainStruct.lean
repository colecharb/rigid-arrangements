open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "13").toNat!
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  for m in [11:N+1] do
    let FA := enumA bodies m {}
    seeds := seeds.set! m FA.cores.arrs
  let lv := closure seeds N 11
  for n in [11:N+1] do
    IO.println s!"===== n={n}: {lv[n]!.arrs.size} off-lattice arrangements"
    let mut hist : Std.HashMap String Nat := {}
    for A in lv[n]!.arrs do
      let an := A.anatomy
      let sig := an.signature
      hist := hist.insert sig (hist.getD sig 0 + 1)
      if args.contains "v" then
        IO.println s!"  {sig} core={A.isCore} | {A.info}"
    for (sig, c) in hist.toArray.qsort (fun a b => a.2 > b.2) do
      IO.println s!"  {c} × {sig}"
