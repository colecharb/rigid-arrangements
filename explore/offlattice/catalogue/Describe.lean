namespace OL

def ratStr (q : Rat) : String :=
  if q.den == 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

/-- monomial expansion of a tower element: list of (coefficient, set of radicand indices) -/
def tMonos : Nat → TN → Array (Rat × Array Nat)
  | _, .q a => if a == 0 then #[] else #[(a, #[])]
  | 0, .e _ _ => #[]
  | k+1, .e a b =>
    tMonos k a ++ (tMonos k b).map fun (c, s) => (c, s.push k)

def radName (T : Tower) (j : Nat) : String :=
  match T.rad[j]! with
  | .q a => s!"√{ratStr a}"
  | _ => s!"√r{j}"

def tStr (T : Tower) (k : Nat) (x : TN) : String :=
  let ms := tMonos k x
  if ms.isEmpty then "0" else
  ms.foldl (fun acc (c, s) =>
    let rs := String.join (s.toList.map fun j => radName T j)
    let term := if s.isEmpty then ratStr c else if c == 1 then rs else if c == -1 then "-" ++ rs else s!"{ratStr c}{rs}"
    if acc == "" then term else if term.startsWith "-" then acc ++ " - " ++ term.drop 1 else acc ++ " + " ++ term) ""

/-- print the arrangement in radius-1 units (all coordinates doubled), exact and float -/
def describe (A : ExArr) : String := Id.run do
  let k := A.k
  let mut s := s!"tower radicands: {A.T.rad.toList.map fun r => tStr A.T k r}\n"
  for i in [0:A.n] do
    let z := Cx.scale 2 A.pts[i]!
    s := s ++ s!"  c{i} = ({tStr A.T k z.re}) + i({tStr A.T k z.im})   ≈ ({2*A.pf[i]!.x}, {2*A.pf[i]!.y})\n"
  s := s ++ s!"  contacts ({A.contacts.size}): {A.contacts.toList}\n"
  return s

/-- multiset of exact squared distances (radius-1 units: ×4), as strings with multiplicity -/
def distSpectrum (A : ExArr) : String := Id.run do
  let k := A.k
  let mut ds : Array (Float × String) := #[]
  for i in [0:A.n] do
    for j in [i+1:A.n] do
      let d := Cx.sub k A.pts[i]! A.pts[j]!
      let d2 := tScale 4 (Cx.norm2 A.T.rad k d)
      ds := ds.push (4 * cfd2 A.pf[i]! A.pf[j]!, tStr A.T k d2)
  let ds2 := ds.qsort (fun a b => a.1 < b.1)
  let mut out : Array (String × Nat) := #[]
  for (_, st) in ds2 do
    if !out.isEmpty && out.back!.1 == st then out := out.modify (out.size - 1) (fun (a, c) => (a, c + 1))
    else out := out.push (st, 1)
  return String.intercalate ", " (out.toList.map fun (st, c) => if c == 1 then st else s!"{st} (×{c})")

end OL
