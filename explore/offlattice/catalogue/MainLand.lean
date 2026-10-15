namespace OL

def keyF (P : Array CF) : Array Int := Id.run do
  let mut ds : Array Float := #[]
  for i in [0:P.size] do
    for j in [i+1:P.size] do
      ds := ds.push (cfd2 P[i]! P[j]!)
  let ds2 := ds.qsort (· < ·)
  return ds2.map fun d => (Float.round (d * 1e5)).toInt64.toInt

def contactsF (P : Array CF) (tolc : Float := 1e-8) : Option (Array (Nat × Nat)) := Id.run do
  let mut cs := #[]
  for i in [0:P.size] do
    for j in [i+1:P.size] do
      let d := cfd2 P[i]! P[j]!
      if d < 1 - tolc then return none
      if d < 1 + tolc then cs := cs.push (i, j)
  return some cs

structure LStats where
  traces : Nat := 0
  blocked : Nat := 0
  fails : Nat := 0
  endLattice : Nat := 0
  endOffKnown : Nat := 0
  endNonRigid : Nat := 0
  endOverlap : Nat := 0
  newOff : Array (Array CF × String) := #[]
  deriving Inhabited

end OL

open OL in
def main (args : List String) : IO Unit := do
  let n := (args.getD 0 "11").toNat!
  let depth := (args.getD 1 "2").toNat!
  let bodies := latticeBodies n
  -- off-lattice catalogue at n from the exact closure (types A, C, E seeds)
  let mut seeds : Array (Array ExArr) := Array.replicate (n+1) #[]
  if n ≥ 11 then
    for m in [11:n+1] do
      let FA := enumA (latticeBodies 12) m {}
      let FC := enumC (latticeBodies 12) m {}
      seeds := seeds.set! m (FA.cores.arrs ++ FC.cores.arrs)
  let lv := if n ≥ 11 then closure seeds n 11 else #[]
  let blind := args.contains "blind"
  let catalog : Array ExArr := if n ≥ 11 then lv[n]!.arrs else #[]
  let offs : Array ExArr := if blind then #[] else catalog
  let mut latKeys : Std.HashSet (Array Int) := {}
  for S in bodies[n]! do latKeys := latKeys.insert (keyF (S.map ofLatF))
  let mut known : Std.HashSet (Array Int) := {}
  for A in offs do known := known.insert (keyF A.pf)
  IO.println s!"n={n}: lattice rigid sets={bodies[n]!.size}, known off-lattice={offs.size}"
  -- queue of starting configurations
  let mut queue : Array (Array CF × Array (Nat × Nat) × String) := #[]
  for (S, idx) in bodies[n]!.zipIdx do
    let P := S.map ofLatF
    queue := queue.push (P, (contactsF P).getD #[], s!"L{n}#{idx}")
  for (A, idx) in offs.zipIdx do
    queue := queue.push (A.pf, A.contacts, s!"O{n}#{idx}")
  -- lattice cores outside the Henneberg closure of a triangle (R14 at n = 14)
  if n ≥ 14 then
    let F := enumA (latticeBodies 12) n { wantLat := true }
    let mut seenL : Std.HashSet (Array Int) := {}
    for A in F.latCores do
      let k := keyF A.pf
      if !latKeys.contains k && !seenL.contains k then
        seenL := seenL.insert k
        latKeys := latKeys.insert k
        queue := queue.push (A.pf, A.contacts, s!"Lextra:{A.info}")
        IO.println s!"added lattice start outside closure: {A.info}"
  let mut st : LStats := {}
  let mut qi := 0
  while qi < queue.size do
    let (P, E, name) := queue[qi]!
    qi := qi + 1
    let x0 := flat P
    -- removal sets: single contacts; if still rigid, pairs; then triples (depth)
    let mut todo : Array (Array Nat) := (Array.range E.size).map (#[·])
    let mut ti := 0
    while ti < todo.size do
      let rem := todo[ti]!
      ti := ti + 1
      let E' := (E.zipIdx.filter fun (_, k) => !rem.contains k).map (·.1)
      if E'.isEmpty then continue
      let (a, b) := E'[0]!
      let (r, _) := rrefNull (jacRows x0 E' a b) x0.size
      if r == x0.size then
        -- still rigid: remove more
        if rem.size < depth then
          for k in [rem.back! + 1:E.size] do todo := todo.push (rem.push k)
        continue
      if r + 1 != x0.size then continue  -- more than one degree of freedom
      for dir in [1.0, -1.0] do
        st := { st with traces := st.traces + 1 }
        match trace x0 E' dir with
        | .blocked => st := { st with blocked := st.blocked + 1 }
        | .fail _ => st := { st with fails := st.fails + 1 }
        | .endpoint x0e =>
          -- polish on all near-contacts
          let Q0 := unflat x0e
          let mut Enear : Array (Nat × Nat) := #[]
          for i in [0:n] do
            for j in [i+1:n] do
              if (cfd2 Q0[i]! Q0[j]! - 1).abs < 1e-5 then Enear := Enear.push (i, j)
          let (pa, pb) := Enear[0]!
          let x := (newtonProj x0e Enear pa pb none 30).getD x0e
          let Q := unflat x
          match contactsF Q 1e-7 with
          | none => st := { st with endOverlap := st.endOverlap + 1 }
          | some cs =>
            let an := analyzeF Q
            let rk := rigRankPF Q cs
            if rk != 2 * n - 3 then
              st := { st with endNonRigid := st.endNonRigid + 1 }
              if args.contains "v" then
                IO.println s!"  nonrigid endpoint from {name} rem={rem}: contacts={cs.size} (E'={E'.size}) rank={rk} lattice={an.lattice} pts={Q.map fun p => (p.x, p.y)}"
            else if an.lattice || latKeys.contains (keyF Q) then
              st := { st with endLattice := st.endLattice + 1 }
            else
              let k := keyF Q
              if known.contains k then
                st := { st with endOffKnown := st.endOffKnown + 1 }
              else
                known := known.insert k
                st := { st with newOff := st.newOff.push (Q, s!"from {name} removing {rem}, contacts={cs.size}, core={an.core}") }
                queue := queue.push (Q, cs, s!"NEW{st.newOff.size}")
  IO.println s!"traces={st.traces} blocked={st.blocked} fails={st.fails} endpoints: lattice={st.endLattice} known-off={st.endOffKnown} nonrigid={st.endNonRigid} overlap={st.endOverlap} NEW-off={st.newOff.size}"
  if blind then
    let ck : Std.HashSet (Array Int) := catalog.foldl (fun acc A => acc.insert (keyF A.pf)) {}
    let found := st.newOff.filter fun (Q, _) => ck.contains (keyF Q)
    IO.println s!"BLIND: discovered {st.newOff.size} off-lattice arrangements; {found.size} of the {catalog.size} catalogue entries rediscovered; {st.newOff.size - found.size} not in catalogue"
  for (Q, info) in st.newOff do
    IO.println s!"  NEW: {info}"
    IO.println s!"    {Q.map fun p => (p.x, p.y)}"
