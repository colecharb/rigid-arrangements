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

/-- deletions that leave an infinitesimally rigid set (float rank) -/
def ExArr.infRigidDeletions (A : ExArr) : Array Nat := Id.run do
  let mut out := #[]
  for c in [0:A.n] do
    let B := A.erase c
    if B.rigRankF == 2 * B.n - 3 then out := out.push c
  return out

end OL

open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "13").toNat!
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  let mut allA : Array (Array ExArr) := Array.replicate (N+1) #[]
  for n in [11:N+1] do
    let F := enumA bodies n {}
    seeds := seeds.set! n F.cores.arrs
    allA := allA.set! n F.all.arrs
    IO.println s!"TypeA n={n}: assemblies={F.all.arrs.size} cores={F.cores.arrs.size}"
  let lv := closure seeds N 11
  for n in [11:N+1] do
    let S := lv[n]!
    let cores := S.arrs.filter (·.isCore)
    IO.println s!"closure n={n}: total off-lattice = {S.arrs.size}, cores = {cores.size}"
    -- check type A assemblies are contained
    let mut missing := 0
    for A in allA[n]! do
      let (_, _, isNew) := S.insert A
      if isNew then missing := missing + 1
    IO.println s!"  type-A assemblies not in closure: {missing}"
    let mut levels : Array Nat := Array.replicate 8 0
    let mut infR := 0
    for A in S.arrs do
      levels := levels.modify A.k (· + 1)
      if A.rigRankF == 2 * A.n - 3 then infR := infR + 1
    IO.println s!"  tower levels histogram: {levels}; infinitesimally rigid (float): {infR}"
    for A in cores do
      let dels := A.infRigidDeletions
      IO.println s!"  CORE: removable-free; inf-rigid deletions: {dels}; exact rank {A.rigRank} / {2*A.n-3}"
      IO.println (showArr A)
