import SimpleC.SL.SeparationLogic

open SimpleC.SL.SeparationLogic

-- A one-element interval is missing its final in-bounds index, zero.
-- This contract would not typecheck with the former out-of-bounds index `hi`.
example (p : Int) : naive_C_Rules.derivable1
    (naive_C_Rules.UIntArray.undef_missing_i p 0 0 1)
    (naive_C_Rules.UIntArray.undef_seg p 0 0) := by
  simpa using naive_C_Rules.UIntArray.undef_missing_i_to_undef_seg_tail p 0 1 (by decide)

example (p lo hi : Int) (h : lo < hi) : naive_C_Rules64.derivable1
    (naive_C_Rules64.IntArray.undef_missing_i p (hi - 1) lo hi)
    (naive_C_Rules64.IntArray.undef_seg p lo (hi - 1)) :=
  naive_C_Rules64.IntArray.undef_missing_i_to_undef_seg_tail p lo hi h
