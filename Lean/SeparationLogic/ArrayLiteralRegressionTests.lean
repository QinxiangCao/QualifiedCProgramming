import SimpleC.SL.SeparationLogic

open SimpleC.SL.SeparationLogic

-- Generated array literals must infer their scalar element type through facades.
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.IntArray.full p 2 [1, -1]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.CharArray2.mixed_full p 1 2 [[some 1, none]]
noncomputable example (p : Int) : naive_C_Rules64.expr :=
  naive_C_Rules64.IntArray2.full p 1 2 [[1, -1]]
noncomputable example (p : Int) : Snaive_C_Rules64.expr :=
  Snaive_C_Rules64.Int64PtrArray2.full p 1 [[1, -1]]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.BoolArray.full p 2 [0, 1]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.BoolArray2.full p 1 2 [[0, 1]]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.BoolArray3.full p 1 1 2 [[[0, 1]]]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.BoolPtrArray2.full p 1 [[0, 1]]
