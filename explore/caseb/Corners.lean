namespace CaseB

/-!
# Minimum-corner polyiamond bodies

`Body.lean` searches over *sites*: connected allowed sets, accepted when the exact integer rank
of the rigidity matrix is `2m − 3`.  That search is the one that gives the honest lower bound,
but its tree is huge, because a connected set of 21 sites out of a 52-site window is a big
object.

This file searches the same problem from the other side, over **cells**.  By Theorem 1 of
`docs/offlattice.md` a body is the corner set of an edge-connected polyiamond, so a *cell family*
determines a body; and H30's own 26-site body is exactly such a family (24 cells, so its cell
adjacency graph is a tree: `V = k + 2`).  The window holds only 64 cells, so a family is a
`UInt64` mask and the search is over edge-connected cell families, minimising the size of the
**corner set** — which is the quantity we care about, and which is *not* minimised by minimising
the number of cells (a family whose cell adjacency graph has `c` independent cycles has
`V = k + 2 − c` corners, so more cells can mean fewer corners).

The bound is the one from `Body.lean`, applied to the corner set: the corner set of an
edge-connected polyiamond is site-connected, so any extension of the family has a corner set that
is a connected site set containing the current corners and every anchor, and `lowerBound` is a
valid lower bound on its size.  Note it is *not* true that each added cell adds a corner (a cell
all three of whose corners are already present adds none), which is why the bound goes through
the site metric rather than counting cells.

What this search establishes is the minimum over **polyiamond** bodies inside the window.  A
body that is infinitesimally rigid without being a polyiamond corner set — one with bars, say —
is covered only by the site search in `Body.lean`.
-/

structure CP where
  R : Region
  cells : Array (Nat × Nat × Nat)
  corn : Array BS                 -- corner mask (over site indices) of each cell
  cnb : Array BS                  -- edge-adjacency mask of each cell
  deriving Inhabited

def mkCP (R : Region) : CP := Id.run do
  let C := mkCells R
  let m := C.tri.size
  let mut corn : Array BS := #[]
  for c in [0:m] do corn := corn.push (cellCorners C c)
  let mut cnb : Array BS := Array.replicate m 0
  for a in [0:m] do
    for b in C.nb[a]! do cnb := cnb.set! a (cnb[a]! ||| bit b)
  return ⟨R, C.tri, corn, cnb⟩

def CP.cornersOf (P : CP) (T : BS) : BS := Id.run do
  let mut s : BS := 0
  for c in [0:P.cells.size] do
    if BS.has T c then s := s ||| P.corn[c]!
  return s

structure CBState where
  best : Nat
  bestSites : BS
  bestCells : BS
  nodes : Nat
  complete : Bool
  deriving Inhabited

/-- branch and bound over edge-connected cell families.  `T` is the family so far, `ex` the cells
excluded on this branch (which includes every cell of index below the seed, so each family is
reached exactly once, through its smallest cell). -/
partial def cbb (P : CP) (nodeCap : Nat) (T ex : BS) (st : CBState) : CBState :=
  if st.nodes ≥ nodeCap then { st with complete := false } else
  let st := { st with nodes := st.nodes + 1 }
  let S := P.cornersOf T
  let sz := BS.card S
  if lowerBound P.R S 0 sz ≥ st.best then st else
  let st :=
    if P.R.terms.all (BS.has S) && sz < st.best && infRigid (subPts P.R S) then
      { st with best := sz, bestSites := S, bestCells := T } else st
  Id.run do
    let m := P.cells.size
    let mut front : BS := 0
    for c in [0:m] do
      if BS.has T c then front := front ||| P.cnb[c]!
    let cand := front &&& (~~~T) &&& (~~~ex)
    let mut v := m
    for c in [0:m] do
      if v == m && BS.has cand c then v := c
    if v == m then return st
    let st := cbb P nodeCap (T ||| bit v) ex st
    return cbb P nodeCap T (ex ||| bit v) st

/-- the minimum corner count over every edge-connected cell family in the window whose corner
set contains all the anchors, searched with an initial upper bound of `cap`. -/
def minCorner (P : CP) (cap nodeCap : Nat) : CBState := Id.run do
  let m := P.cells.size
  let mut st : CBState := ⟨cap + 1, 0, 0, 0, true⟩
  let mut ex : BS := 0
  for s in [0:m] do
    st := cbb P nodeCap (bit s) ex st
    ex := ex ||| bit s
    if !st.complete then return st
  return st

end CaseB
