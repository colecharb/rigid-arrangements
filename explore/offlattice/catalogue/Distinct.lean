namespace OL

/-- exact certificate that `A` and `B` are not congruent: a squared distance whose exact
multiplicity differs. Returns `true` if certified distinct. -/
def distinctExact (A B : ExArr) : Bool := Id.run do
  if A.n != B.n then return true
  let kA := A.k
  let kB := B.k
  let K := kA + kB
  let rad := A.T.rad ++ B.T.rad
  let mut dA : Array (TN × Float) := #[]
  let mut dB : Array (TN × Float) := #[]
  for i in [0:A.n] do
    for j in [i+1:A.n] do
      let d := Cx.sub K (Cx.lift kB A.pts[i]!) (Cx.lift kB A.pts[j]!)
      dA := dA.push (Cx.norm2 rad K d, cfd2 A.pf[i]! A.pf[j]!)
      let e := Cx.sub K B.pts[i]! B.pts[j]!
      dB := dB.push (Cx.norm2 rad K e, cfd2 B.pf[i]! B.pf[j]!)
  -- try candidate values (float-guided), confirm counts exactly
  for (v, vf) in dA ++ dB do
    let ca := (dA.filter fun (_, f) => (f - vf).abs < 1e-6).size
    let cb := (dB.filter fun (_, f) => (f - vf).abs < 1e-6).size
    if ca != cb then
      let ea := (dA.filter fun (w, _) => tIsZero rad K (tSub K w v)).size
      let eb := (dB.filter fun (w, _) => tIsZero rad K (tSub K w v)).size
      if ea != eb then return true
  return false

end OL
