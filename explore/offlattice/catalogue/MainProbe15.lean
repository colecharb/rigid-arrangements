open OL in
def main : IO Unit := do
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate 16 #[]
  for m in [11:15] do
    let FA := enumA bodies m {}
    let FC := enumC bodies m {}
    seeds := seeds.set! m (FA.cores.arrs ++ FC.cores.arrs)
  let lv := closure seeds 15 11
  let S := lv[15]!
  IO.println s!"n=15: extensions of the n=14 closure only (no new n=15 seeds): {S.arrs.size}"
  let mut levels : Array Nat := Array.replicate 10 0
  let mut hist : Std.HashMap String Nat := {}
  for A in S.arrs do
    levels := levels.modify A.k (· + 1)
    let an := A.anatomy
    let key := s!"frames={an.nFrames} free={an.free.size}"
    hist := hist.insert key (hist.getD key 0 + 1)
  IO.println s!"tower levels: {levels}"
  for (k, c) in hist.toArray do IO.println s!"  {c} × {k}"
  for A in S.arrs do
    if A.k > 2 then
      IO.println s!"  new radical: {A.info} rad={repr A.T.rad} anatomy={A.anatomy.signature}"
