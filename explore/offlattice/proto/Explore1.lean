import RigidArrangements
open RigidArrangements

/-- fast computable versions -/
def vecsN (N : Int) : List (Int × Int) := Id.run do
  let mut out := []
  for i in [0:(2*N.toNat+1)] do
    for j in [0:(2*N.toNat+1)] do
      let a : Int := i - N; let b : Int := j - N
      if eNorm (a, b) == N then out := (a, b) :: out
  return out

def units : List (Int × Int) := [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
def normTri (N₁ N₂ : Int) : Bool := (vecsN N₁).any fun a => units.any fun e => eNorm (a + e) == N₂
def fc (u v : Int × Int) : Bool := latticeSymmetries.any fun M => eNorm (u - latticeMatApply M v) == 1
def isSq (n : Int) : Bool := n ≥ 0 && (let r := n.toNat.sqrt; r * r == n.toNat)

def normsUpTo (B : Int) : List Int := (List.range (B.toNat + 1)).filterMap fun n =>
  if n > 0 && (vecsN n).length > 0 then some (n : Int) else none

-- T1 table: pairs N1 ≤ N2 with D > 0, and whether a lattice hinge triangle exists
#eval Id.run do
  let ns := normsUpTo 31
  let mut lines : List String := []
  for N₁ in ns do
    for N₂ in ns do
      if N₁ ≤ N₂ then
        let D := 4 * N₁ * N₂ - (N₁ + N₂ - 1) ^ 2
        if D ≥ 0 then
          let t := normTri N₁ N₂
          let crit := D % 3 == 0 && isSq (D / 3)
          lines := s!"N1={N₁} N2={N₂} D={D} latticeTriangle={t} D=3k^2:{crit}" :: lines
  return lines.reverse

-- orbits: number of symmetry orbits of vectors of each norm
#eval Id.run do
  let ns := normsUpTo 200
  let mut out : List (Int × Nat) := []
  for N in ns do
    let vs := vecsN N
    -- orbit reps
    let mut reps : List (Int × Int) := []
    for v in vs do
      if !(reps.any fun r => latticeSymmetries.any fun M => latticeMatApply M r == v) then
        reps := v :: reps
    if reps.length > 1 then out := (N, reps.length) :: out
  return out.reverse

-- T1 vs T2 discrepancy: smallest (N1, N2) with u,v such that normTri but not fc
#eval Id.run do
  let ns := normsUpTo 100
  let mut out : List String := []
  for N₁ in ns do
    for N₂ in ns do
      if N₁ ≤ N₂ && normTri N₁ N₂ then
        for u in vecsN N₁ do
          for v in vecsN N₂ do
            if !(fc u v) then
              if out.length < 12 then out := s!"N1={N₁} N2={N₂} u={u} v={v}" :: out
  return out.reverse
