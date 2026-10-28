/-! Candidate polyiamond whose corner set spans an edge-isolated triangle t = U(0,0). -/
abbrev Pt := Int × Int
def U (a b : Int) : List Pt := [(a,b),(a+1,b),(a,b+1)]
def D (a b : Int) : List Pt := [(a+1,b),(a,b+1),(a+1,b+1)]
/-- rotation by 120° about the centre of U(0,0) -/
def rot (p : Pt) : Pt := (1 - p.1 - p.2, p.1)
def arc1 : List (List Pt) :=
  [D 1 (-1), U 2 (-1), D 2 (-1), U 2 0, D 2 0, U 2 1, D 1 1, U 1 2, D 0 2, U 0 2, D (-1) 2, U (-1) 2, D (-1) 1]
def cells0 : List (List Pt) :=
  arc1 ++ arc1.map (·.map rot) ++ arc1.map (·.map (rot ∘ rot))
def S : List Pt := (cells0.flatten).eraseDups
def mem (p : Pt) : Bool := S.contains p
/-- all lattice triangles spanned by S, as (anchor, isUp) -/
def tris : List (Pt × Bool) := Id.run do
  let mut out := []
  for p in S do
    if mem (p.1+1,p.2) && mem (p.1,p.2+1) then out := out ++ [(p, true)]
    if mem (p.1-1,p.2+1) && mem (p.1,p.2+1) then out := out ++ [((p.1-1,p.2), false)]
  return out
def verts (t : Pt × Bool) : List Pt := if t.2 then U t.1.1 t.1.2 else D t.1.1 t.1.2
def edgeAdj (s t : Pt × Bool) : Bool := ((verts s).filter (fun v => (verts t).contains v)).length == 2
partial def comp (todo seen : List (Pt × Bool)) : List (Pt × Bool) :=
  match todo with
  | [] => seen
  | x :: xs =>
    let nb := tris.filter (fun y => edgeAdj x y && !seen.contains y)
    comp (xs ++ nb) (seen ++ nb)
def components : List (List (Pt × Bool)) := Id.run do
  let mut out : List (List (Pt × Bool)) := []
  for t in tris do
    if !(out.any (·.contains t)) then out := out ++ [comp [t] [t]]
  return out
def deg (p : Pt) : Nat :=
  ([(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)] : List Pt).countP (fun d => mem (p.1+d.1, p.2+d.2))
#eval (S.length, tris.length, components.map (·.length),
  components.map (fun c => S.all (fun p => c.any (fun t => (verts t).contains p))),
  (cells0.length), (S.map deg).foldl (·+·) 0 / 2)
#eval components.filter (·.length == 1)

/-! Judge: the two-arc ("C") variant: drop the third arc. -/
def cellsC : List (List Pt) := arc1 ++ arc1.map (·.map rot)
def SC : List Pt := (cellsC.flatten).eraseDups
def memC (p : Pt) : Bool := SC.contains p
def trisC : List (Pt × Bool) := Id.run do
  let mut out := []
  for p in SC do
    if memC (p.1+1,p.2) && memC (p.1,p.2+1) then out := out ++ [(p, true)]
    if memC (p.1-1,p.2+1) && memC (p.1,p.2+1) then out := out ++ [((p.1-1,p.2), false)]
  return out
partial def compC (todo seen : List (Pt × Bool)) : List (Pt × Bool) :=
  match todo with
  | [] => seen
  | x :: xs =>
    let nb := trisC.filter (fun y => edgeAdj x y && !seen.contains y)
    compC (xs ++ nb) (seen ++ nb)
def componentsC : List (List (Pt × Bool)) := Id.run do
  let mut out : List (List (Pt × Bool)) := []
  for t in trisC do
    if !(out.any (·.contains t)) then out := out ++ [compC [t] [t]]
  return out
/-- the cells of the polyiamond, as (anchor, isUp), deduplicated -/
def sortPts (c : List Pt) : List Pt := (c.toArray.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2))).toList
def polyCells : List (List Pt) := (cellsC.map sortPts).eraseDups
def adjV (s t : List Pt) : Bool := (s.filter (fun v => t.contains v)).length == 2
partial def compP (todo seen : List (List Pt)) : List (List Pt) :=
  match todo with
  | [] => seen
  | x :: xs =>
    let nb := polyCells.filter (fun y => adjV x y && !seen.contains y)
    compP (xs ++ nb) (seen ++ nb)
def degC (p : Pt) : Nat :=
  ([(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)] : List Pt).countP (fun d => memC (p.1+d.1, p.2+d.2))
-- (#corners, #spanned triangles, component sizes, which components cover all corners,
--  #cells, polyiamond edge-connected?, #contacts, U(0,0) corners present?, apexes absent?)
#eval (SC.length, trisC.length, componentsC.map (·.length),
  componentsC.map (fun c => SC.all (fun p => c.any (fun t => (verts t).contains p))),
  polyCells.length, (compP [polyCells[0]!] [polyCells[0]!]).length == polyCells.length,
  (SC.map degC).foldl (·+·) 0 / 2,
  [((0:Int),(0:Int)),(1,0),(0,1)].all memC, [((1:Int),(1:Int)),(-1,1),(1,-1)].all (!memC ·),
  polyCells.all (fun t => t.all memC), polyCells.all (fun c => c.length == 3))
#eval componentsC.filter (·.length == 1)
#eval SC
