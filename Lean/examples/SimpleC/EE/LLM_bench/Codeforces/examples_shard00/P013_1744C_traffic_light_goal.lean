import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P013_1744C_traffic_light_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solver_safety_wit_1_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (n_pre = (Zlength (lights)))) (PreH2 : (1 <= (Zlength (lights)))) (PreH3 : ((Zlength (lights)) <= 200000)) (PreH4 : (c_pre = 114)) (PreH5 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH6 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (103 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 103) ”

noncomputable def solver_safety_wit_2_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (n_pre = (Zlength (lights)))) (PreH2 : (1 <= (Zlength (lights)))) (PreH3 : ((Zlength (lights)) <= 200000)) (PreH4 : (c_pre = 121)) (PreH5 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH6 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (103 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 103) ”

noncomputable def solver_safety_wit_3_green : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (n_pre = (Zlength (lights)))) (PreH2 : (1 <= (Zlength (lights)))) (PreH3 : ((Zlength (lights)) <= 200000)) (PreH4 : (c_pre = 103)) (PreH5 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH6 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (103 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 103) ”

noncomputable def solver_safety_wit_4_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_5_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_6_green : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_7_green : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "next_green" ) )) # Int |->_)
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_9_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "next_green" ) )) # Int |->_)
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "next_green" ) )) # Int |->_)
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_11_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "next_green" ) )) # Int |->_)
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_12_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_13_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_14_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (((2 * n_pre) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * n_pre) - 1)) ”

noncomputable def solver_safety_wit_15_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * n_pre)) ”

noncomputable def solver_safety_wit_16_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_17_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_18_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (((2 * n_pre) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * n_pre) - 1)) ”

noncomputable def solver_safety_wit_19_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * n_pre)) ”

noncomputable def solver_safety_wit_20_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_21_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "next_green" ) )) # Int |-> ((-1)))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Char |-> (c_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_22_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (n = (Zlength (lights)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 200000)) (PreH4 : (c = 114)) (PreH5 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH6 : (Pre c lights)) (PreH7 : ((-1) <= i)) (PreH8 : (i < (2 * n))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= n)) (PreH11 : ((-1) <= next_green)) (PreH12 : (next_green < (2 * n))) (PreH13 : (TrafficScanState c lights i ans next_green)) (PreH14 : ((0 : Int) <= (n_pre + 1))) (PreH15 : (c_pre ≠ 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 114)) (PreH20 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH21 : (Pre c_pre lights)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_23_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (n = (Zlength (lights)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 200000)) (PreH4 : (c = 121)) (PreH5 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH6 : (Pre c lights)) (PreH7 : ((-1) <= i)) (PreH8 : (i < (2 * n))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= n)) (PreH11 : ((-1) <= next_green)) (PreH12 : (next_green < (2 * n))) (PreH13 : (TrafficScanState c lights i ans next_green)) (PreH14 : ((0 : Int) <= (n_pre + 1))) (PreH15 : (c_pre ≠ 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 121)) (PreH20 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH21 : (Pre c_pre lights)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_24_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((0 : Int) <= (Z.rem i n))) (PreH2 : ((Z.rem i n) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 114)) (PreH12 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH13 : (Pre c lights)) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n))) (PreH20 : (TrafficScanState c lights i ans next_green)) (PreH21 : ((0 : Int) <= (n_pre + 1))) (PreH22 : (c_pre ≠ 103)) (PreH23 : (n_pre = (Zlength (lights)))) (PreH24 : (1 <= (Zlength (lights)))) (PreH25 : ((Zlength (lights)) <= 200000)) (PreH26 : (c_pre = 114)) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH28 : (Pre c_pre lights)) ,
  ((( &( "ch" ) )) # Char |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i ≠ (INT_MIN)) ∨ (n ≠ (-1))) ” &&
  “ (n ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_25_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((0 : Int) <= (Z.rem i n))) (PreH2 : ((Z.rem i n) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 121)) (PreH12 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH13 : (Pre c lights)) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n))) (PreH20 : (TrafficScanState c lights i ans next_green)) (PreH21 : ((0 : Int) <= (n_pre + 1))) (PreH22 : (c_pre ≠ 103)) (PreH23 : (n_pre = (Zlength (lights)))) (PreH24 : (1 <= (Zlength (lights)))) (PreH25 : ((Zlength (lights)) <= 200000)) (PreH26 : (c_pre = 121)) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH28 : (Pre c_pre lights)) ,
  ((( &( "ch" ) )) # Char |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i ≠ (INT_MIN)) ∨ (n ≠ (-1))) ” &&
  “ (n ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_26_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((0 : Int) <= (Z.rem i n))) (PreH2 : ((Z.rem i n) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 114)) (PreH12 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH13 : (Pre c lights)) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n))) (PreH20 : (TrafficScanState c lights i ans next_green)) (PreH21 : ((0 : Int) <= (n_pre + 1))) (PreH22 : (c_pre ≠ 103)) (PreH23 : (n_pre = (Zlength (lights)))) (PreH24 : (1 <= (Zlength (lights)))) (PreH25 : ((Zlength (lights)) <= 200000)) (PreH26 : (c_pre = 114)) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH28 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (103 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 103) ”

noncomputable def solver_safety_wit_27_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((0 : Int) <= (Z.rem i n))) (PreH2 : ((Z.rem i n) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 121)) (PreH12 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH13 : (Pre c lights)) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n))) (PreH20 : (TrafficScanState c lights i ans next_green)) (PreH21 : ((0 : Int) <= (n_pre + 1))) (PreH22 : (c_pre ≠ 103)) (PreH23 : (n_pre = (Zlength (lights)))) (PreH24 : (1 <= (Zlength (lights)))) (PreH25 : ((Zlength (lights)) <= 200000)) (PreH26 : (c_pre = 121)) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH28 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (103 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 103) ”

noncomputable def solver_safety_wit_28_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (i))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_29_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (i))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_30_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((next_green - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (next_green - i)) ”

noncomputable def solver_safety_wit_31_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((next_green - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (next_green - i)) ”

noncomputable def solver_safety_wit_32_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((next_green - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (next_green - i)) ”

noncomputable def solver_safety_wit_33_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "ch" ) )) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((next_green - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (next_green - i)) ”

noncomputable def solver_safety_wit_34_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> ((next_green - i)))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_35_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> ((next_green - i)))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_36_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_37_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_38_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (i))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_39_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (i))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_40_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (i))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_41_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (i))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_42_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_43_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_44_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_45_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_entail_wit_1_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ” &&
  “ ((-1) <= ((2 * n_pre) - 1)) ” &&
  “ (((2 * n_pre) - 1) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((-1) <= (-1)) ” &&
  “ ((-1) < (2 * n_pre)) ” &&
  “ (TrafficScanState c_pre lights ((2 * n_pre) - 1) (0 : Int) (-1)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights ((2 * n_pre) - 1) (0 : Int) (-1)) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights ((2 * n_pre) - 1) (0 : Int) (-1))

noncomputable def solver_entail_wit_1_red_split_goal_2 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))

noncomputable def solver_entail_wit_2_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ” &&
  “ ((-1) <= ((2 * n_pre) - 1)) ” &&
  “ (((2 * n_pre) - 1) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((-1) <= (-1)) ” &&
  “ ((-1) < (2 * n_pre)) ” &&
  “ (TrafficScanState c_pre lights ((2 * n_pre) - 1) (0 : Int) (-1)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights ((2 * n_pre) - 1) (0 : Int) (-1)) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights ((2 * n_pre) - 1) (0 : Int) (-1))

noncomputable def solver_entail_wit_2_yellow_split_goal_2 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre ≠ 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))

noncomputable def solver_entail_wit_3_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 114)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= (Z.rem i n)) ” &&
  “ ((Z.rem i n) < n) ” &&
  “ (next_green <= INT_MAX) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (next_green >= INT_MIN) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights i ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ ((Z.rem i n) < n) ” &&
  “ ((0 : Int) <= (Z.rem i n)) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  ((Z.rem i n) < n)

noncomputable def solver_entail_wit_3_red_split_goal_2 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  ((0 : Int) <= (Z.rem i n))

noncomputable def solver_entail_wit_4_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 121)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= (Z.rem i n)) ” &&
  “ ((Z.rem i n) < n) ” &&
  “ (next_green <= INT_MAX) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (next_green >= INT_MIN) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights i ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "c" ) )) # Char |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "next_green" ) )) # Int |-> (next_green))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ ((Z.rem i n) < n) ” &&
  “ ((0 : Int) <= (Z.rem i n)) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  ((Z.rem i n) < n)

noncomputable def solver_entail_wit_4_yellow_split_goal_2 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  ((0 : Int) <= (Z.rem i n))

noncomputable def solver_entail_wit_5_1_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= (next_green - i)) ” &&
  “ ((next_green - i) <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) (next_green - i) next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1) (next_green - i) next_green) ” &&
  “ ((next_green - i) <= n) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_1_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights (i - 1) (next_green - i) next_green)

noncomputable def solver_entail_wit_5_1_red_split_goal_2 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  ((next_green - i) <= n)

noncomputable def solver_entail_wit_5_2_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1) ans next_green) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_2_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights (i - 1) ans next_green)

noncomputable def solver_entail_wit_5_3_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans i) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1) ans i) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_3_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights (i - 1) ans i)

noncomputable def solver_entail_wit_5_4_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans i) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1) ans i) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_4_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights (i - 1) ans i)

noncomputable def solver_entail_wit_5_5_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1) ans next_green) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_5_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights (i - 1) ans next_green)

noncomputable def solver_entail_wit_5_6_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1) ans next_green) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_6_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 114)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (TrafficScanState 114 lights (i - 1) ans next_green)

noncomputable def solver_entail_wit_6_1_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= (next_green - i)) ” &&
  “ ((next_green - i) <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) (next_green - i) next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1) (next_green - i) next_green) ” &&
  “ ((next_green - i) <= n) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_1_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights (i - 1) (next_green - i) next_green)

noncomputable def solver_entail_wit_6_1_yellow_split_goal_2 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) > ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  ((next_green - i) <= n)

noncomputable def solver_entail_wit_6_2_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1) ans next_green) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_2_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights (i - 1) ans next_green)

noncomputable def solver_entail_wit_6_3_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans i) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1) ans i) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_3_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ c)) (PreH2 : (i < n)) (PreH3 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH4 : ((0 : Int) <= (Z.rem i n))) (PreH5 : ((Z.rem i n) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= (0 : Int))) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH16 : (Pre c lights)) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n))) (PreH19 : ((0 : Int) <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n))) (PreH23 : (TrafficScanState c lights i ans next_green)) (PreH24 : ((0 : Int) <= (n_pre + 1))) (PreH25 : (c_pre ≠ 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH31 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights (i - 1) ans i)

noncomputable def solver_entail_wit_6_4_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans i) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1) ans i) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_4_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights (i - 1) ans i)

noncomputable def solver_entail_wit_6_5_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1) ans next_green) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_5_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i >= n)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH3 : ((0 : Int) <= (Z.rem i n))) (PreH4 : ((Z.rem i n) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= (0 : Int))) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH15 : (Pre c lights)) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n))) (PreH22 : (TrafficScanState c lights i ans next_green)) (PreH23 : ((0 : Int) <= (n_pre + 1))) (PreH24 : (c_pre ≠ 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH30 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights (i - 1) ans next_green)

noncomputable def solver_entail_wit_6_6_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights (i - 1) ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1) ans next_green) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_6_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((next_green - i) <= ans)) (PreH2 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 103)) (PreH5 : ((0 : Int) <= (Z.rem i n))) (PreH6 : ((Z.rem i n) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH17 : (Pre c lights)) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n))) (PreH20 : ((0 : Int) <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n))) (PreH24 : (TrafficScanState c lights i ans next_green)) (PreH25 : ((0 : Int) <= (n_pre + 1))) (PreH26 : (c_pre ≠ 103)) (PreH27 : (n_pre = (Zlength (lights)))) (PreH28 : (1 <= (Zlength (lights)))) (PreH29 : ((Zlength (lights)) <= 200000)) (PreH30 : (c_pre = 121)) (PreH31 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH32 : (Pre c_pre lights)) ,
  (TrafficScanState 121 lights (i - 1) ans next_green)

noncomputable def solver_return_wit_1_red : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 114)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec c_pre lights ans) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 114)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (Spec 114 lights ans) ”
  &&  emp
)

noncomputable def solver_return_wit_1_red_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 114)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  (Spec 114 lights ans)

noncomputable def solver_return_wit_2_yellow : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 121)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec c_pre lights ans) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 121)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (Spec 121 lights ans) ”
  &&  emp
)

noncomputable def solver_return_wit_2_yellow_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH7 : (Pre c lights)) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n))) (PreH14 : (TrafficScanState c lights i ans next_green)) (PreH15 : ((0 : Int) <= (n_pre + 1))) (PreH16 : (c_pre ≠ 103)) (PreH17 : (n_pre = (Zlength (lights)))) (PreH18 : (1 <= (Zlength (lights)))) (PreH19 : ((Zlength (lights)) <= 200000)) (PreH20 : (c_pre = 121)) (PreH21 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH22 : (Pre c_pre lights)) ,
  (Spec 121 lights ans)

noncomputable def solver_return_wit_3_green : Prop :=
  (
forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ (Spec c_pre lights (0 : Int)) ”
  &&  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
) \/
(
forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  TT && emp 
|--
  “ (Spec 103 lights (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_3_green_split_goal_1 : Prop :=
  forall (c_pre : Int) (n_pre : Int) (lights : (List Int)) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH7 : (Pre c_pre lights)) ,
  (Spec 103 lights (0 : Int))

noncomputable def solver_partial_solve_wit_1_red : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((0 : Int) <= (Z.rem i n))) (PreH2 : ((Z.rem i n) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 114)) (PreH12 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH13 : (Pre c lights)) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n))) (PreH20 : (TrafficScanState c lights i ans next_green)) (PreH21 : ((0 : Int) <= (n_pre + 1))) (PreH22 : (c_pre ≠ 103)) (PreH23 : (n_pre = (Zlength (lights)))) (PreH24 : (1 <= (Zlength (lights)))) (PreH25 : ((Zlength (lights)) <= 200000)) (PreH26 : (c_pre = 114)) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH28 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= (Z.rem i n)) ” &&
  “ ((Z.rem i n) < n) ” &&
  “ (next_green <= INT_MAX) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (next_green >= INT_MIN) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 114) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights i ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 114) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (((s_pre + ((Z.rem i n) * sizeof(CHAR)))) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre (Z.rem i n) (0 : Int) (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)

noncomputable def solver_partial_solve_wit_2_yellow : Prop :=
  forall (c_pre : Int) (n_pre : Int) (s_pre : Int) (lights : (List Int)) (next_green : Int) (ans : Int) (i : Int) (c : Int) (n : Int) (PreH1 : ((0 : Int) <= (Z.rem i n))) (PreH2 : ((Z.rem i n) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 121)) (PreH12 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103)))) (PreH13 : (Pre c lights)) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n))) (PreH20 : (TrafficScanState c lights i ans next_green)) (PreH21 : ((0 : Int) <= (n_pre + 1))) (PreH22 : (c_pre ≠ 103)) (PreH23 : (n_pre = (Zlength (lights)))) (PreH24 : (1 <= (Zlength (lights)))) (PreH25 : ((Zlength (lights)) <= 200000)) (PreH26 : (c_pre = 121)) (PreH27 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103)))) (PreH28 : (Pre c_pre lights)) ,
  (charArray.full s_pre (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)
|--
  “ ((0 : Int) <= (Z.rem i n)) ” &&
  “ ((Z.rem i n) < n) ” &&
  “ (next_green <= INT_MAX) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (next_green >= INT_MIN) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (n = (Zlength (lights))) ” &&
  “ (1 <= n) ” &&
  “ (n <= 200000) ” &&
  “ (c = 121) ” &&
  “ forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n)) -> ((((Znth idx_2 lights (0 : Int)) = 114) ∨ ((Znth idx_2 lights (0 : Int)) = 121)) ∨ ((Znth idx_2 lights (0 : Int)) = 103))) ” &&
  “ (Pre c lights) ” &&
  “ ((-1) <= i) ” &&
  “ (i < (2 * n)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= n) ” &&
  “ ((-1) <= next_green) ” &&
  “ (next_green < (2 * n)) ” &&
  “ (TrafficScanState c lights i ans next_green) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (c_pre ≠ 103) ” &&
  “ (n_pre = (Zlength (lights))) ” &&
  “ (1 <= (Zlength (lights))) ” &&
  “ ((Zlength (lights)) <= 200000) ” &&
  “ (c_pre = 121) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (lights)))) -> ((((Znth idx lights (0 : Int)) = 114) ∨ ((Znth idx lights (0 : Int)) = 121)) ∨ ((Znth idx lights (0 : Int)) = 103))) ” &&
  “ (Pre c_pre lights) ”
  &&  (((s_pre + ((Z.rem i n) * sizeof(CHAR)))) # Char |-> ((Znth (Z.rem i n) (lights ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre (Z.rem i n) (0 : Int) (n_pre + 1) (lights ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg s_pre (n_pre + 1) 200005)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1_red : solver_safety_wit_1_red
  proof_of_solver_safety_wit_2_yellow : solver_safety_wit_2_yellow
  proof_of_solver_safety_wit_3_green : solver_safety_wit_3_green
  proof_of_solver_safety_wit_4_red : solver_safety_wit_4_red
  proof_of_solver_safety_wit_5_yellow : solver_safety_wit_5_yellow
  proof_of_solver_safety_wit_6_green : solver_safety_wit_6_green
  proof_of_solver_safety_wit_7_green : solver_safety_wit_7_green
  proof_of_solver_safety_wit_8_red : solver_safety_wit_8_red
  proof_of_solver_safety_wit_9_red : solver_safety_wit_9_red
  proof_of_solver_safety_wit_10_yellow : solver_safety_wit_10_yellow
  proof_of_solver_safety_wit_11_yellow : solver_safety_wit_11_yellow
  proof_of_solver_safety_wit_12_red : solver_safety_wit_12_red
  proof_of_solver_safety_wit_13_yellow : solver_safety_wit_13_yellow
  proof_of_solver_safety_wit_14_red : solver_safety_wit_14_red
  proof_of_solver_safety_wit_15_red : solver_safety_wit_15_red
  proof_of_solver_safety_wit_16_red : solver_safety_wit_16_red
  proof_of_solver_safety_wit_17_red : solver_safety_wit_17_red
  proof_of_solver_safety_wit_18_yellow : solver_safety_wit_18_yellow
  proof_of_solver_safety_wit_19_yellow : solver_safety_wit_19_yellow
  proof_of_solver_safety_wit_20_yellow : solver_safety_wit_20_yellow
  proof_of_solver_safety_wit_21_yellow : solver_safety_wit_21_yellow
  proof_of_solver_safety_wit_22_red : solver_safety_wit_22_red
  proof_of_solver_safety_wit_23_yellow : solver_safety_wit_23_yellow
  proof_of_solver_safety_wit_24_red : solver_safety_wit_24_red
  proof_of_solver_safety_wit_25_yellow : solver_safety_wit_25_yellow
  proof_of_solver_safety_wit_26_red : solver_safety_wit_26_red
  proof_of_solver_safety_wit_27_yellow : solver_safety_wit_27_yellow
  proof_of_solver_safety_wit_28_yellow : solver_safety_wit_28_yellow
  proof_of_solver_safety_wit_29_red : solver_safety_wit_29_red
  proof_of_solver_safety_wit_30_red : solver_safety_wit_30_red
  proof_of_solver_safety_wit_31_yellow : solver_safety_wit_31_yellow
  proof_of_solver_safety_wit_32_red : solver_safety_wit_32_red
  proof_of_solver_safety_wit_33_yellow : solver_safety_wit_33_yellow
  proof_of_solver_safety_wit_34_red : solver_safety_wit_34_red
  proof_of_solver_safety_wit_35_yellow : solver_safety_wit_35_yellow
  proof_of_solver_safety_wit_36_yellow : solver_safety_wit_36_yellow
  proof_of_solver_safety_wit_37_red : solver_safety_wit_37_red
  proof_of_solver_safety_wit_38_yellow : solver_safety_wit_38_yellow
  proof_of_solver_safety_wit_39_red : solver_safety_wit_39_red
  proof_of_solver_safety_wit_40_red : solver_safety_wit_40_red
  proof_of_solver_safety_wit_41_yellow : solver_safety_wit_41_yellow
  proof_of_solver_safety_wit_42_red : solver_safety_wit_42_red
  proof_of_solver_safety_wit_43_yellow : solver_safety_wit_43_yellow
  proof_of_solver_safety_wit_44_red : solver_safety_wit_44_red
  proof_of_solver_safety_wit_45_yellow : solver_safety_wit_45_yellow
  proof_of_solver_partial_solve_wit_1_red : solver_partial_solve_wit_1_red
  proof_of_solver_partial_solve_wit_2_yellow : solver_partial_solve_wit_2_yellow
  proof_of_solver_entail_wit_1_red : solver_entail_wit_1_red
  proof_of_solver_entail_wit_2_yellow : solver_entail_wit_2_yellow
  proof_of_solver_entail_wit_3_red : solver_entail_wit_3_red
  proof_of_solver_entail_wit_4_yellow : solver_entail_wit_4_yellow
  proof_of_solver_entail_wit_5_1_red : solver_entail_wit_5_1_red
  proof_of_solver_entail_wit_5_2_red : solver_entail_wit_5_2_red
  proof_of_solver_entail_wit_5_3_red : solver_entail_wit_5_3_red
  proof_of_solver_entail_wit_5_4_red : solver_entail_wit_5_4_red
  proof_of_solver_entail_wit_5_5_red : solver_entail_wit_5_5_red
  proof_of_solver_entail_wit_5_6_red : solver_entail_wit_5_6_red
  proof_of_solver_entail_wit_6_1_yellow : solver_entail_wit_6_1_yellow
  proof_of_solver_entail_wit_6_2_yellow : solver_entail_wit_6_2_yellow
  proof_of_solver_entail_wit_6_3_yellow : solver_entail_wit_6_3_yellow
  proof_of_solver_entail_wit_6_4_yellow : solver_entail_wit_6_4_yellow
  proof_of_solver_entail_wit_6_5_yellow : solver_entail_wit_6_5_yellow
  proof_of_solver_entail_wit_6_6_yellow : solver_entail_wit_6_6_yellow
  proof_of_solver_return_wit_1_red : solver_return_wit_1_red
  proof_of_solver_return_wit_2_yellow : solver_return_wit_2_yellow
  proof_of_solver_return_wit_3_green : solver_return_wit_3_green

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_goal
