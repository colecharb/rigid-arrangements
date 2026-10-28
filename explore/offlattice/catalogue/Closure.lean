namespace OL

/-- add a point `c` (level `k` of `A.T`) to `A`, possibly over an extended tower. -/
def ExArr.addPt (A : ExArr) (T : Tower) (c : Cx) (info : String) : ExArr :=
  let dk := T.lvl - A.T.lvl
  let pts := (A.pts.map (Cx.lift dk)).push c
  { T, pts, pf := pts.map (·.toF T T.lvl), info }

/-- all one-circle extensions of `A` by a circle touching at least two circles (exact). -/
def ExArr.extensions (A : ExArr) : Array ExArr := Id.run do
  let n := A.n
  let k := A.k
  let rad := A.T.rad
  let mut out := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      let df := cfd2 A.pf[i]! A.pf[j]!
      if df ≤ 4 + tol then
        if cmpD2 A i j 4 ≤ 0 then
          -- float apexes first
          let mf : CF := ⟨(A.pf[i]!.x + A.pf[j]!.x) / 2, (A.pf[i]!.y + A.pf[j]!.y) / 2⟩
          let wf : CF := ⟨A.pf[j]!.x - A.pf[i]!.x, A.pf[j]!.y - A.pf[i]!.y⟩
          let hf := Float.sqrt (max 0 ((4 - df) / (4 * df)))
          for sgn in [1.0, -1.0] do
            let cf : CF := ⟨mf.x - sgn * hf * wf.y, mf.y + sgn * hf * wf.x⟩
            let mut ok := true
            for l in [0:n] do
              if ok && cfd2 cf A.pf[l]! < 1 - tol then ok := false
            if ok then
              -- exact apex
              let w := Cx.sub k A.pts[j]! A.pts[i]!
              let d2 := Cx.norm2 rad k w
              let s := tMul rad k (tSub k (.q 4) d2) (tInv rad k (tScale 4 d2))
              let (T, h, _) := A.T.sqrtOrPush s
              let K := T.lvl
              let dk := K - k
              let mid := Cx.scale (1/2) (Cx.add k A.pts[i]! A.pts[j]!)
              let iw : Cx := ⟨tNeg w.im, w.re⟩
              let off := Cx.mulR T.rad K h (Cx.lift dk iw)
              let c := if sgn > 0 then Cx.add K (Cx.lift dk mid) off else Cx.sub K (Cx.lift dk mid) off
              let B := A.addPt T c s!"{A.info} + apex({i},{j}){if sgn > 0 then "+" else "-"}"
              match B.validate with
              | some B' => out := out.push B'
              | none => pure ()
  return out

/-- closure levels: `lv[n] = Ext(lv[n-1]) ∪ seeds[n]` -/
def closure (seeds : Array (Array ExArr)) (N : Nat) (lo : Nat) : Array Store := Id.run do
  let mut lv : Array Store := Array.replicate (N + 1) {}
  for n in [lo:N+1] do
    let mut S : Store := {}
    if n > lo then
      for A in lv[n-1]!.arrs do
        for B in A.extensions do
          let (S', _, _) := S.insert B
          S := S'
    for A in seeds[n]! do
      let (S', _, _) := S.insert A
      S := S'
    lv := lv.set! n S
  return lv

end OL
