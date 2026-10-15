namespace OL

def showArr (A : ExArr) : String := Id.run do
  let nb := A.nbrs
  let degs := nb.map (·.size)
  let mut s := s!"  n={A.n} contacts={A.contacts.size} (2n-3={2*A.n-3}) degs={degs} lvl={A.k} rad={repr A.T.rad}\n  {A.info}\n"
  for i in [0:A.n] do
    s := s ++ s!"    {i}: ({A.pf[i]!.x}, {A.pf[i]!.y})\n"
  return s

def ExArr.erase (A : ExArr) (c : Nat) : ExArr :=
  let keep := (List.range A.n).filter (· != c) |>.toArray
  let pts := keep.map (A.pts[·]!)
  let B := mkArr A.T pts A.info
  B.validate.getD B

def ExArr.infRigidDeletions (A : ExArr) : Array Nat := Id.run do
  let mut out := #[]
  for c in [0:A.n] do
    let B := A.erase c
    if B.rigRankF == 2 * B.n - 3 then out := out.push c
  return out

def keyF5 (P : Array CF) : Array Int := Id.run do
  let mut ds : Array Float := #[]
  for i in [0:P.size] do
    for j in [i+1:P.size] do
      ds := ds.push (cfd2 P[i]! P[j]!)
  let ds2 := ds.qsort (· < ·)
  return ds2.map fun d => (Float.round (d * 1e5)).toInt64.toInt

end OL

open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "13").toNat!
  let useC := (args.getD 1 "1") == "1"
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  let mut allA : Array (Array ExArr) := Array.replicate (N+1) #[]
  for n in [11:N+1] do
    let FA := enumA bodies n {}
    let FE := enumE bodies n {}
    let FC := if useC then enumC bodies n {} else {}
    IO.println s!"n={n}: A assemblies={FA.all.arrs.size} cores={FA.cores.arrs.size}; C assemblies={FC.all.arrs.size} cores={FC.cores.arrs.size}; E assemblies={FE.all.arrs.size} cores={FE.cores.arrs.size}"
    seeds := seeds.set! n (FA.cores.arrs ++ FC.cores.arrs ++ FE.cores.arrs)
    allA := allA.set! n (FA.all.arrs ++ FC.all.arrs ++ FE.all.arrs)
  -- closure, with composite seeds added level by level
  let mut lv : Array Store := Array.replicate (N + 1) {}
  for n in [11:N+1] do
    let mut S : Store := {}
    if n > 11 then
      for A in lv[n-1]!.arrs do
        for B in A.extensions do
          let (S', _, _) := S.insert B
          S := S'
    let nExt := S.arrs.size
    -- composite hinge+bar: off-lattice arrangement of size n1 with lattice body of size n+1-n1
    let mut FCo : Found := {}
    for n1 in [11:n] do
      let s2 := n + 1 - n1
      if s2 ≥ 3 && s2 < bodies.size then
        FCo := enumAComposite lv[n1]!.arrs bodies[s2]! FCo
    IO.println s!"n={n}: composite hinge+bar assemblies={FCo.all.arrs.size} cores={FCo.cores.arrs.size}"
    let mut newSeeds := 0
    for A in seeds[n]! ++ FCo.cores.arrs do
      let (S', _, isNew) := S.insert A
      S := S'
      if isNew then
        newSeeds := newSeeds + 1
    lv := lv.set! n S
    let cores := S.arrs.filter (·.isCore)
    IO.println s!"closure n={n}: extensions={nExt}, new from seeds={newSeeds}, total off-lattice={S.arrs.size}, cores={cores.size}"
    let mut missing := 0
    for A in allA[n]! ++ FCo.all.arrs do
      let (_, _, isNew) := S.insert A
      if isNew then
        missing := missing + 1
        IO.println s!"  MISSING assembly:\n{showArr A}"
    IO.println s!"  assemblies not in closure: {missing}"
    let mut levels : Array Nat := Array.replicate 10 0
    let mut infR := 0
    let mut taut := 0
    for A in S.arrs do
      levels := levels.modify A.k (· + 1)
      if A.rigRankF == 2 * A.n - 3 then infR := infR + 1
      if A.tautCount > 0 then taut := taut + 1
    IO.println s!"  tower levels: {levels}; inf. rigid (float rank): {infR}; with taut circle: {taut}"
    -- composite three-bar: off-lattice arrangement of size n1 + lattice body of size n - n1
    let keys : Std.HashSet (Array Int) := S.arrs.foldl (fun acc A => acc.insert (keyF5 A.pf)) {}
    for n1 in [11:n] do
      let s2 := n - n1
      if s2 ≥ 3 && s2 < bodies.size then
        for A in lv[n1]!.arrs do
          let (hits, nComb) := enumBComp A.pf bodies[s2]!
          let mut inCl := 0
          let mut notIn := 0
          for h in hits do
            if keys.contains (keyF5 h.pts) then inCl := inCl + 1 else
              notIn := notIn + 1
              IO.println s!"  composite-B hit NOT in closure: {h.info}\n    {h.pts.map fun p => (p.x, p.y)}"
          IO.println s!"  composite-B on [{A.info}] with {s2}-bodies: combos={nComb} nonoverlapping hits={hits.size} in closure={inCl} not={notIn}"
    let mut hist : Std.HashMap String Nat := {}
    for A in S.arrs do
      let sig := A.anatomy.signature
      hist := hist.insert sig (hist.getD sig 0 + 1)
    for (sig, c) in hist.toArray.qsort (fun a b => a.2 > b.2) do
      IO.println s!"  anatomy {c} × {sig}"
    for A in cores do
      let dels := A.infRigidDeletions
      IO.println s!"  CORE: inf-rigid deletions={dels}; exact rank {A.rigRank}/{2*A.n-3}"
      IO.println (showArr A)
