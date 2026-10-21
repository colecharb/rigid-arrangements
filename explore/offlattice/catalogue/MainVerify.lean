open OL in
def main (args : List String) : IO Unit := do
  let N := (args.getD 0 "13").toNat!
  let bodies := latticeBodies 12
  let mut seeds : Array (Array ExArr) := Array.replicate (N+1) #[]
  for m in [11:N+1] do
    let FA := enumA bodies m {}
    let FC := enumC bodies m {}
    let FE := enumE bodies m {}
    seeds := seeds.set! m (FA.cores.arrs ++ FC.cores.arrs ++ FE.cores.arrs)
  let lv := closure seeds N 11
  for n in [11:N+1] do
    let arrs := lv[n]!.arrs
    let mut okVal := 0
    let mut okRank := 0
    let mut offLat := 0
    for A in arrs do
      match A.validate (exact := true) with
      | some B => if B.contacts == A.contacts then okVal := okVal + 1
      | none => pure ()
      if A.rigRank == 2 * n - 3 then okRank := okRank + 1
      if !A.onLattice then offLat := offLat + 1
    let mut pairs := 0
    let mut certified := 0
    for i in [0:arrs.size] do
      for j in [i+1:arrs.size] do
        pairs := pairs + 1
        if distinctExact arrs[i]! arrs[j]! then certified := certified + 1
    IO.println s!"n={n}: {arrs.size} arrangements; fully-exact contact recheck ok={okVal}; exact inf-rigid (rank 2n-3)={okRank}; exact off-lattice={offLat}; pairwise distinct certified {certified}/{pairs}"
