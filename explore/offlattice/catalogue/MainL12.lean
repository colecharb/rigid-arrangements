open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "12").toNat!
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  for m in [11:N+1] do
    seeds := seeds.set! m (enumA bodies m {}).cores.arrs
  let lv := closure seeds N 11
  for n in [12:N+1] do
    IO.println s!"===== n={n}"
    for (A, idx) in lv[n]!.arrs.zipIdx do
      let k := A.k
      let an := A.anatomy
      let extra := (Array.range (A.n - 11)).map fun t =>
        let z := Cx.scale 2 A.pts[11 + t]!
        s!"c{11+t} = ({tStr A.T k z.re}) + i({tStr A.T k z.im}) ≈ ({2*A.pf[11+t]!.x}, {2*A.pf[11+t]!.y})"
      IO.println s!"#{idx}: {A.info}\n   contacts={A.contacts.size} core={A.isCore} removable={A.removables} {an.signature}\n   {extra.toList}"
