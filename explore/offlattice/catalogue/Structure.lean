namespace OL

/-- union-find helpers -/
partial def ufFind (p : Array Nat) (x : Nat) : Nat := if p[x]! == x then x else ufFind p p[x]!

structure Anatomy where
  bodies : Array (Array Nat)      -- triangle components (vertex sets), size ≥ 3
  free : Array Nat                -- circles in no triangle
  bars : Array (Nat × Nat)        -- contacts not inside one body
  frameOfBody : Array Nat         -- frame class id of each body
  frameOfBar : Array Nat
  nFrames : Nat
  hinges : Array Nat              -- circles in ≥ 2 bodies
  deriving Inhabited

/-- exact sixth power of a contact direction (a unit complex number) -/
def dir6 (A : ExArr) (i j : Nat) : Cx :=
  let k := A.k
  let rad := A.T.rad
  let d := Cx.sub k A.pts[j]! A.pts[i]!
  let d2 := Cx.mul rad k d d
  let d3 := Cx.mul rad k d2 d
  Cx.mul rad k d3 d3

def cxEq (A : ExArr) (z w : Cx) : Bool :=
  let k := A.k
  tIsZero A.T.rad k (tSub k z.re w.re) && tIsZero A.T.rad k (tSub k z.im w.im)

def ExArr.anatomy (A : ExArr) : Anatomy := Id.run do
  let n := A.n
  let mut adj : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for (i, j) in A.contacts do
    adj := adj.modify i (·.set! j true)
    adj := adj.modify j (·.set! i true)
  let mut tris : Array (Nat × Nat × Nat) := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      if adj[i]![j]! then
        for k in [j+1:n] do
          if adj[i]![k]! && adj[j]![k]! then tris := tris.push (i, j, k)
  let mut par := Array.range tris.size
  for a in [0:tris.size] do
    for b in [a+1:tris.size] do
      let (i, j, k) := tris[a]!
      let (x, y, z) := tris[b]!
      let sa := #[i, j, k]
      let common := (#[x, y, z].filter sa.contains).size
      if common == 2 then
        let ra := ufFind par a
        let rb := ufFind par b
        if ra != rb then par := par.set! ra rb
  let mut compOf : Std.HashMap Nat (Array Nat) := {}
  for a in [0:tris.size] do
    let r := ufFind par a
    let (i, j, k) := tris[a]!
    let cur := compOf.getD r #[]
    let cur := [i, j, k].foldl (fun acc v => if acc.contains v then acc else acc.push v) cur
    compOf := compOf.insert r cur
  let bodies := compOf.toArray.map (·.2.qsort (· < ·))
  let inBody (v : Nat) : Bool := bodies.any (·.contains v)
  let free := (Array.range n).filter (!inBody ·)
  let bars := A.contacts.filter fun (i, j) => !(bodies.any fun B => B.contains i && B.contains j)
  -- frames
  let mut reps : Array Cx := #[]
  let mut fb : Array Nat := #[]
  for B in bodies do
    -- a contact inside B
    let some (i, j) := A.contacts.find? (fun (i, j) => B.contains i && B.contains j) | fb := fb.push 999
    let d := dir6 A i j
    match reps.findIdx? (cxEq A d) with
    | some r => fb := fb.push r
    | none =>
      fb := fb.push reps.size
      reps := reps.push d
  let mut fr : Array Nat := #[]
  for (i, j) in bars do
    let d := dir6 A i j
    match reps.findIdx? (cxEq A d) with
    | some r => fr := fr.push r
    | none =>
      fr := fr.push reps.size
      reps := reps.push d
  let hinges := (Array.range n).filter fun v => (bodies.filter (·.contains v)).size ≥ 2
  return { bodies, free, bars, frameOfBody := fb, frameOfBar := fr, nFrames := reps.size, hinges }

def Anatomy.signature (an : Anatomy) : String :=
  let bs := (an.bodies.map (·.size)).qsort (· > ·)
  s!"bodies={bs.toList} free={an.free.size} bars={an.bars.size} hinges={an.hinges.size} frames={an.nFrames} (bodyFrames={an.frameOfBody.toList}, barFrames={an.frameOfBar.toList})"

end OL
