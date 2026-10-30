import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P004_1890A_doremys_paint_3_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def solver_safety_wit_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  ((( &( "cy" ) )) # Int |->_)
  ** ((( &( "cx" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "y" ) )) # Int |-> ((-1)))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "x" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  ((( &( "cx" ) )) # Int |->_)
  ** ((( &( "y" ) )) # Int |-> ((-1)))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "x" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  ((( &( "y" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "x" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  ((( &( "y" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "x" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  ((( &( "x" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "cy" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "cx" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "y" ) )) # Int |-> ((-1)))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "x" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cx + 1)) ”
) \/
(
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cx + 1)) ”
)

noncomputable def solver_safety_wit_7_split_goal_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cx + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_7_split_goal_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((INT_MIN) <= (cx + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cy + 1)) ”
) \/
(
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cy + 1)) ”
)

noncomputable def solver_safety_wit_10_split_goal_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_10_split_goal_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((INT_MIN) <= (cy + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cy + 1)) ”
) \/
(
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cy + 1)) ”
)

noncomputable def solver_safety_wit_11_split_goal_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_11_split_goal_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((INT_MIN) <= (cy + 1)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> ((cx + 1)))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> ((cy + 1)))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cy" ) )) # Int |-> ((cy + 1)))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH8 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy ≠ (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cx - cy) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cx - cy)) ”
) \/
(
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy ≠ (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cx - cy) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cx - cy)) ”
)

noncomputable def solver_safety_wit_17_split_goal_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy ≠ (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cx - cy) <= INT_MAX) ”

noncomputable def solver_safety_wit_17_split_goal_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy ≠ (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((INT_MIN) <= (cx - cy)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy ≠ (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_19 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) <= 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy - cx) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cy - cx)) ”
) \/
(
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) <= 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy - cx) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cy - cx)) ”
)

noncomputable def solver_safety_wit_19_split_goal_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) <= 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((cy - cx) <= INT_MAX) ”

noncomputable def solver_safety_wit_19_split_goal_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) <= 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((INT_MIN) <= (cy - cx)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) <= 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cy" ) )) # Int |-> (cy))
  ** ((( &( "cx" ) )) # Int |-> (cx))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input (0 : Int))) ∧ ((Znth idx_2 input (0 : Int)) <= 100000)))) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input (0 : Int) (Znth (0 : Int) input (0 : Int)) (-1) (0 : Int) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input (0 : Int))) ∧ ((Znth idx_2 input (0 : Int)) <= 100000)))) ,
  TT && emp 
|--
  “ (PaintScanState input (0 : Int) (Znth (0 : Int) input (0 : Int)) (-1) (0 : Int) (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input (0 : Int))) ∧ ((Znth idx_2 input (0 : Int)) <= 100000)))) ,
  (PaintScanState input (0 : Int) (Znth (0 : Int) input (0 : Int)) (-1) (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input (0 : Int))) ∧ ((Znth idx_2 input (0 : Int)) <= 100000)))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input (i + 1) x y (cx + 1) cy) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (PaintScanState input (i + 1) x y (cx + 1) cy) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (PaintScanState input (i + 1) x y (cx + 1) cy)

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input (i + 1) x (Znth i input (0 : Int)) cx (cy + 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (PaintScanState input (i + 1) x (Znth i input (0 : Int)) cx (cy + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (PaintScanState input (i + 1) x (Znth i input (0 : Int)) cx (cy + 1))

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input (i + 1) x (Znth i input (0 : Int)) cx (cy + 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (PaintScanState input (i + 1) x y cx (cy + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (PaintScanState input (i + 1) x y cx (cy + 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy = (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (Spec input 1) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy = (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (Spec input 1) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (cy = (0 : Int))) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy)) ,
  (Spec input 1)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cy - cx) > 1)) (PreH2 : ((cx - cy) <= 1)) (PreH3 : (cy ≠ (0 : Int))) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (Spec input (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cy - cx) > 1)) (PreH2 : ((cx - cy) <= 1)) (PreH3 : (cy ≠ (0 : Int))) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (Spec input (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cy - cx) > 1)) (PreH2 : ((cx - cy) <= 1)) (PreH3 : (cy ≠ (0 : Int))) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (Spec input (0 : Int))

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cy - cx) <= 1)) (PreH2 : ((cx - cy) <= 1)) (PreH3 : (cy ≠ (0 : Int))) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (Spec input 1) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cy - cx) <= 1)) (PreH2 : ((cx - cy) <= 1)) (PreH3 : (cy ≠ (0 : Int))) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (Spec input 1) ”
  &&  emp
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cy - cx) <= 1)) (PreH2 : ((cx - cy) <= 1)) (PreH3 : (cy ≠ (0 : Int))) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (Spec input 1)

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) > 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (Spec input (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) > 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (Spec input (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_4_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((cx - cy) > 1)) (PreH2 : (cy ≠ (0 : Int))) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (Spec input (0 : Int))

noncomputable def solver_return_wit_5 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (Spec input (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  TT && emp 
|--
  “ (Spec input (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_5_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (Spec input (0 : Int))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH8 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input i x y cx cy) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y ≠ (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (y ≠ (-1)) ” &&
  “ ((Znth i input (0 : Int)) ≠ x) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input i x y cx cy) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input (0 : Int)) ≠ x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ (y = (-1)) ” &&
  “ ((Znth i input (0 : Int)) ≠ x) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input i x y cx cy) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (x : Int) (y : Int) (cx : Int) (cy : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = y)) (PreH2 : (y ≠ (-1))) (PreH3 : ((Znth i input (0 : Int)) ≠ x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)
|--
  “ ((Znth i input (0 : Int)) = y) ” &&
  “ (y ≠ (-1)) ” &&
  “ ((Znth i input (0 : Int)) ≠ x) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> ((1 <= (Znth idx input (0 : Int))) ∧ ((Znth idx input (0 : Int)) <= 100000))) ” &&
  “ (PaintScanState input i x y cx cy) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 100)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4
  proof_of_solver_return_wit_5 : solver_return_wit_5

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_goal
