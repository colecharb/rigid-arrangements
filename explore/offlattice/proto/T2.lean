import RigidArrangements
open RigidArrangements
#check @AffineIsometryEquiv.vaddConst
#check @LinearIsometryEquiv.toAffineIsometryEquiv
#check @AffineIsometryEquiv.trans_apply
#check @Circle.coe_ne_zero
#check @Finset.mem_Icc
#check @latticeSymmetries
#eval latticeSymmetries
#check @Complex.conj_conj
example : (Finset.Icc (-3 : ℤ) 3).card = 7 := by decide
