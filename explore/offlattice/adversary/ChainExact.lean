/-! Exact (integer) verification of the taut-chain example E30.
Coordinates are lattice coordinates scaled by 7: site (a, b) ↦ (7a, 7b); the six chain circles
sit at (3j, 5j), j = 1..6, i.e. at (j/7)·(3,5) in lattice coordinates.
Real position of scaled coords (u, v): (2u + v, √3 v)/7. Squared distance = (4/49)·eNorm(Δ).
So: contact ⟺ eNorm(Δ) = 49; non-overlap ⟺ eNorm(Δ) ≥ 49. -/

abbrev Pt := Int × Int
def eN (p : Pt) : Int := p.1*p.1 + p.1*p.2 + p.2*p.2
def sub (p q : Pt) : Pt := (p.1 - q.1, p.2 - q.2)

/-- body sites in a Henneberg order (triangle first, then each new site touches ≥ 2 earlier). -/
def body : List Pt :=
  -- BFS polyiamond path from P=(0,0) to Q=(3,5), listed from the P end
  [(0,0), (-1,0), (-1,1), (-2,1), (-2,2), (-1,2), (-2,3), (-1,3), (-2,4), (-1,4), (0,3), (0,4),
   (-1,5), (0,5), (-1,6), (0,6), (1,5), (1,6), (0,7), (1,7), (2,6), (2,7), (3,6), (3,5)]

def chain : List Pt := (List.range 6).map fun (j : Nat) => (3 * (Int.ofNat j + 1), 5 * (Int.ofNat j + 1))

def allPts : List Pt := (body.map fun p => (7*p.1, 7*p.2)) ++ chain

def idx : List (Nat × Pt) := (List.range allPts.length).zip allPts

def contacts : List (Nat × Nat) :=
  idx.foldl (fun acc (i, p) => acc ++ ((idx.filter fun (j, q) => i < j && eN (sub p q) == 49).map
    fun (j, _) => (i, j))) []

def nonoverlap : Bool := idx.all fun (i, p) => idx.all fun (j, q) => i == j || eN (sub p q) ≥ 49

def nbrs (i : Nat) : List Nat :=
  contacts.filterMap fun (a, b) => if a == i then some b else if b == i then some a else none

/-- Henneberg certificate for the body: first three sites mutually touch; each later site
touches ≥ 2 earlier sites (in lattice units: eNorm = 1). -/
def hennebergOK : Bool := Id.run do
  let b := body.toArray
  let t := fun (p q : Pt) => eN (sub p q) == 1
  if !(t b[0]! b[1]! && t b[1]! b[2]! && t b[0]! b[2]!) then return false
  for k in [3:b.size] do
    let mut c := 0
    for l in [0:k] do
      if t b[k]! b[l]! then c := c + 1
    if c < 2 then return false
  return true

#eval s!"n = {allPts.length}, body = {body.length}, chain = {chain.length}"
#eval s!"distinct = {allPts.eraseDups.length == allPts.length}"
#eval s!"non-overlap (all eNorm ≥ 49, scaled) = {nonoverlap}"
#eval s!"contacts = {contacts.length}, 2n-3 = {2*allPts.length - 3}"
#eval s!"body Henneberg certificate = {hennebergOK}"
-- chain circles: indices 24..29; neighbours
#eval (List.range 6).map fun j => (24 + j, nbrs (24 + j))
-- chain endpoints: P = index 0, Q = index 23
#eval s!"P nbrs = {nbrs 0}, Q nbrs = {nbrs 23}"
-- straightness: P, c1..c6, Q consecutive at eNorm 49 and |PQ|² = 49·49 (|PQ| = 14 = 7 contacts)
#eval s!"eNorm(Q-P) scaled = {eN (sub (21,35) (0,0))} = 49*49 = {49*49}"
-- chain points are not lattice points (coordinates not divisible by 7)
#eval chain.all fun p => p.1 % 7 != 0 || p.2 % 7 != 0
-- each chain circle: exactly two contacts, at distance 4 (eNorm 4·49 = 196 scaled)
#eval (List.range 6).all fun j =>
  let ns := nbrs (24 + j)
  ns.length == 2 && eN (sub allPts[ns[0]!]! allPts[ns[1]!]!) == 196
-- degrees of all circles and removable circles (degree 2 with neighbours < 4 apart, eNorm < 196)
#eval (List.range allPts.length).map fun i => (nbrs i).length
#eval (List.range allPts.length).filter fun i =>
  let ns := nbrs i
  ns.length == 2 && eN (sub allPts[ns[0]!]! allPts[ns[1]!]!) < 196
-- circles in no triangle
#eval (List.range allPts.length).filter fun i =>
  let ns := nbrs i
  ns.all fun a => ns.all fun b => !(contacts.contains (a, b))
-- real coordinates of the chain circles: x = (2u+v)/7, y = √3·v/7
#eval chain.map fun p => (s!"({2*p.1 + p.2}/7, {p.2}√3/7)")

/-- greedy Henneberg order: start from a triangle, add any site touching ≥ 2 added sites. -/
def greedy (s : List Pt) : Option (List Pt) := Id.run do
  let t := fun (p q : Pt) => eN (sub p q) == 1
  let a := s.toArray
  -- find a triangle
  for i in [0:a.size] do
    for j in [i+1:a.size] do
      for k in [j+1:a.size] do
        if t a[i]! a[j]! && t a[j]! a[k]! && t a[i]! a[k]! then
          let mut order := #[a[i]!, a[j]!, a[k]!]
          let mut progress := true
          while progress do
            progress := false
            for p in a do
              if !(order.contains p) && (order.filter (t p)).size ≥ 2 then
                order := order.push p; progress := true
          if order.size == a.size then return some order.toList
  return none
#eval greedy body
