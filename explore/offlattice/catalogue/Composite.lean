namespace OL

/-- hinge + bar between an exact arrangement `A` (hinge `h1`, bar end `x`) and a lattice body
`B2` (hinge `ih2`, bar end `iy`), solution `ε`. -/
def hingeBarComposite (A : ExArr) (h1 x : Nat) (B2 : Array Pt) (ih2 iy : Nat) (ε : Int) :
    Option ExArr := Id.run do
  let uf : CF := ⟨A.pf[x]!.x - A.pf[h1]!.x, A.pf[x]!.y - A.pf[h1]!.y⟩
  let p := uf.x * uf.x + uf.y * uf.y
  let v := psub B2[iy]! B2[ih2]!
  let vf := ofLatF v
  let q := Float.ofInt (eN v)
  let m := p + q - 1
  let Δf := 4 * p * q - m * m
  if Δf < -1e-9 then return none
  let fac : CF := ⟨m, -(Float.ofInt ε) * Float.sqrt (max 0 Δf)⟩
  let R := csc (1 / (2 * p * q)) (cmul (cmul uf (cconj vf)) fac)
  let h1f := A.pf[h1]!
  for iw in [0:B2.size] do
    if iw != ih2 then
      let P := cadd h1f (cmul R (ofLatF (psub B2[iw]! B2[ih2]!)))
      for z in A.pf do
        if cfd2 P z < 1 - 1e-6 then return none
  -- exact
  let k := A.k
  let rad0 := A.T.rad
  let u := Cx.sub k A.pts[x]! A.pts[h1]!
  let pX := Cx.norm2 rad0 k u
  let qX : TN := .q (eN v)
  let mX := tSub k (tAdd k pX qX) (.q 1)
  let ΔX := tSub k (tScale 4 (tMul rad0 k pX qX)) (tMul rad0 k mX mX)
  if tSign rad0 k ΔX < 0 then return none
  if tSign rad0 k ΔX == 0 && ε == -1 then return none
  let (T, sD, _) := A.T.sqrtOrPush ΔX
  let K := T.lvl
  let dk := K - k
  let rad := T.rad
  let L (w : Pt) : Cx := Cx.lift (K - 1) (Cx.ofLat w.1 w.2)
  let g := Cx.mul rad K (Cx.lift dk u) (Cx.conj (L v))
  let fac : Cx := ⟨tLift dk mX, tScale (-(ε : Rat)) sD⟩
  let den := tInv rad K (tScale 2 (tMul rad K (tLift dk pX) (tLift dk qX)))
  let Rx := Cx.mulR rad K den (Cx.mul rad K g fac)
  let h1x := Cx.lift dk A.pts[h1]!
  let mut pts := A.pts.map (Cx.lift dk)
  for iw in [0:B2.size] do
    if iw != ih2 then
      pts := pts.push (Cx.add K h1x (Cx.mul rad K Rx (L (psub B2[iw]! B2[ih2]!))))
  return some (mkArr T pts s!"Acomp [{A.info}] + body {B2} hinge=({h1},{ih2}) bar=({x},{iy}) eps={ε}")

def enumAComposite (offs : Array ExArr) (bodies : Array (Array Pt)) (F0 : Found) : Found := Id.run do
  let mut F := F0
  for A in offs do
    for B in bodies do
      for mir in [false, true] do
        let B2 : Array Pt := if mir then B.map mirr else B
        for h1 in [0:A.n] do
          for x in [0:A.n] do
            if x != h1 then
              for ih2 in [0:B2.size] do
                for iy in [0:B2.size] do
                  if iy != ih2 then
                    for ε in [1, -1] do
                      F := { F with nCand := F.nCand + 1 }
                      match hingeBarComposite A h1 x B2 ih2 iy ε with
                      | some C => F := F.add C
                      | none => pure ()
  return F

end OL
