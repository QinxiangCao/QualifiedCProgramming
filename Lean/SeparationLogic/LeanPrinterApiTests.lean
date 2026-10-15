import SimpleC.SL.LeanPrinterPrelude

open AUXLib SimpleC.SL.SeparationLogic
open scoped CoqZ

-- Function-valued annotation operations use Lean's native declarations.
example : Forall2 Eq ([1, 2] : List Int) [1, 2] :=
  .cons rfl (.cons rfl .nil)
example : Forall (LE.le (α := Int) 0) [0, 1] := .cons (by decide) (.cons (by decide) .nil)
example : Forall (GE.ge (α := Int) 2) [0, 1] := .cons (by decide) (.cons (by decide) .nil)
example : List.map (fun x : Int => x + 1) [1, 2] = [2, 3] := rfl
example : List.map (Int.add 48) [0, 1] = [48, 49] := rfl
example : hd (0 : Int) [] = 0 := rfl
example : hd (0 : Int) [1, 2] = 1 := rfl
example : repeat_Z (1 : Int) (-1) = [] := rfl
example : repeat_Z (1 : Int) 3 = [1, 1, 1] := rfl
example : ListLib.sum [1, 2] = 3 := rfl
example : (2 : Int) ^ (-1 : Int) = 0 := rfl
example : (2 : Int) ^ (0 : Int) = 1 := rfl
example : (2 : Int) ^ (3 : Int) = 8 := rfl
example : (2 : Int) ^ (3 : Nat) = 8 := rfl

private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2

-- Bare and negative literals must elaborate through the facade's element type.
noncomputable example (p : Int) : naive_C_Rules.expr :=
  intArray.seg p 0 1 (replace_Znth 0 1 [-1])
noncomputable example (p : Int) : naive_C_Rules.expr :=
  intArray2.full p 1 2 [[1, -1]]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  int64PtrArray2.full p 1 [[1, -1]]
noncomputable example (p : Int) : naive_C_Rules.expr :=
  naive_C_Rules.CharArray2.mixed_full p 1 2 [[some 1, none]]
noncomputable example (p : Int) : naive_C_Rules64.expr :=
  naive_C_Rules64.IntArray2.full p 1 2 [[1, -1]]
noncomputable example (p : Int) : Snaive_C_Rules64.expr :=
  Snaive_C_Rules64.Int64PtrArray2.full p 1 [[1, -1]]
