import SimpleC.SL.SeparationLogic

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.IntLib

example (x : Int) (h : 0 <= x) : x = Zabs x := by
  _int_nia_compat

example (x : Int) (h : x < 0) : -x = Zabs x := by
  _int_nia_compat

example (x y : Int) : (0 + y) + (x - 1) * y = x * y := by
  _int_nia_compat

example (x y i j ans : Int) (hi : i + 1 > x) (hix : i <= x)
    (hj : j + 1 > y) (hjy : j <= y)
    (hans : ans = (i - 1) * y + j) : ans = x * y := by
  _int_nia_compat
