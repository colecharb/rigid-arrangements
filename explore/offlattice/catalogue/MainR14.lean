open OL in
def main : IO Unit := do
  let bodies := latticeBodies 12
  let F := enumA bodies 14 { wantLat := true }
  let lat14 := (latticeBodies 14)[14]!
  let keys : Std.HashSet (Array Int) := lat14.foldl (fun acc S => acc.insert (ExArr.key (mkArr Tower.base (S.map fun v => Cx.ofLat v.1 v.2)))) {}
  let mut seen : Std.HashSet (Array Int) := {}
  for A in F.latCores do
    let k := A.key
    if !keys.contains k && !seen.contains k then
      seen := seen.insert k
      IO.println s!"lattice core not in closure: {A.info} contacts={A.contacts.size}\n  {A.pf.map fun p => (p.x, p.y)}"
