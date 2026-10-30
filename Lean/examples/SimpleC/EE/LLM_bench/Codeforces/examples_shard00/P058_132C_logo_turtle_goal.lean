import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P058_132C_logo_turtle_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "W" ) )) # Int |->_)
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (((2 * retval) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * retval) + 1)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "W" ) )) # Int |->_)
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((2 * retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * retval)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "W" ) )) # Int |->_)
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "W" ) )) # Int |->_)
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "dp" ) )) # Ptr |->_)
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((changes_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (changes_pre + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "dp" ) )) # Ptr |->_)
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "dp" ) )) # Ptr |->_)
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "dp" ) )) # Ptr |->_)
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval = (Zlength (commands)))) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "ndp" ) )) # Ptr |->_)
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((changes_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (changes_pre + 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval = (Zlength (commands)))) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "ndp" ) )) # Ptr |->_)
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval = (Zlength (commands)))) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "ndp" ) )) # Ptr |->_)
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval = (Zlength (commands)))) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "ndp" ) )) # Ptr |->_)
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1))) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((((0 : Int) * 2) + (0 : Int)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((0 : Int) * 2) + (0 : Int))) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (((0 : Int) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) * 2)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (replace_Znth ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) (1) ((repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))))
  ** (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "ndp" ) )) # Ptr |-> (retval_3))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i < len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((changes_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (changes_pre + 1)) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i < len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i < len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i < len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval = ndp)) (PreH2 : (i < len)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= len)) (PreH14 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH15 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * W))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table)) ,
  ((( &( "dir" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= changes_pre)) (PreH14 : ((0 : Int) <= dir)) (PreH15 : (dir <= 2)) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH22 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table)) ,
  ((( &( "pos" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c * 2) + dir) * W) + pos) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c * 2) + dir) * W) + pos)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c * 2) + dir) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c * 2) + dir) * W)) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c * 2) + dir) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c * 2) + dir)) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c * 2)) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) ,
  ((( &( "flip" ) )) # Int |->_)
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= changes_pre)) (PreH14 : ((0 : Int) <= dir)) (PreH15 : (dir < 2)) (PreH16 : ((0 : Int) <= pos)) (PreH17 : (pos < W)) (PreH18 : ((0 : Int) <= flip)) (PreH19 : (flip <= 2)) (PreH20 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH21 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH27 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) <= changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH30 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (84 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 84) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (70 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 70) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (84 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 84) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (84 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 84) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (84 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 84) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) <= changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH30 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (84 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 84) ”

noncomputable def solver_safety_wit_44 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_45 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_46 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir = (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((pos + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + 1)) ”

noncomputable def solver_safety_wit_47 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + (-1))) ”

noncomputable def solver_safety_wit_48 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_49 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_50 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir = (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_51 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir = (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((pos + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + 1)) ”

noncomputable def solver_safety_wit_52 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + (-1))) ”

noncomputable def solver_safety_wit_53 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_54 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_55 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir = (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_56 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (Z.lxor dir 1))) (PreH2 : ((Z.lxor dir 1) < 2)) (PreH3 : (flip <= INT_MAX)) (PreH4 : (dir <= INT_MAX)) (PreH5 : (c <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (W <= INT_MAX)) (PreH9 : (len <= INT_MAX)) (PreH10 : (changes_pre <= INT_MAX)) (PreH11 : (pos <= INT_MAX)) (PreH12 : (flip >= INT_MIN)) (PreH13 : (dir >= INT_MIN)) (PreH14 : (c >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (O >= INT_MIN)) (PreH17 : (W >= INT_MIN)) (PreH18 : (len >= INT_MIN)) (PreH19 : (changes_pre >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_57 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (Z.lxor dir 1))) (PreH2 : ((Z.lxor dir 1) < 2)) (PreH3 : (flip <= INT_MAX)) (PreH4 : (dir <= INT_MAX)) (PreH5 : (c <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (W <= INT_MAX)) (PreH9 : (len <= INT_MAX)) (PreH10 : (changes_pre <= INT_MAX)) (PreH11 : (pos <= INT_MAX)) (PreH12 : (flip >= INT_MIN)) (PreH13 : (dir >= INT_MIN)) (PreH14 : (c >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (O >= INT_MIN)) (PreH17 : (W >= INT_MIN)) (PreH18 : (len >= INT_MIN)) (PreH19 : (changes_pre >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_58 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= dir)) (PreH2 : (dir < 2)) (PreH3 : (flip <= INT_MAX)) (PreH4 : (pos <= INT_MAX)) (PreH5 : (dir <= INT_MAX)) (PreH6 : (c <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (O <= INT_MAX)) (PreH9 : (W <= INT_MAX)) (PreH10 : (len <= INT_MAX)) (PreH11 : (changes_pre <= INT_MAX)) (PreH12 : ((pos + (-1)) <= INT_MAX)) (PreH13 : (flip >= INT_MIN)) (PreH14 : (pos >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : ((pos + (-1)) >= INT_MIN)) (PreH23 : (dir ≠ (0 : Int))) (PreH24 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH25 : ((c + flip) <= changes_pre)) (PreH26 : (flip <= 1)) (PreH27 : (changes_pre = n)) (PreH28 : (len = (Zlength (commands)))) (PreH29 : (W = ((2 * len) + 1))) (PreH30 : (O = len)) (PreH31 : (1 <= len)) (PreH32 : (len <= 100)) (PreH33 : (1 <= changes_pre)) (PreH34 : (changes_pre <= 50)) (PreH35 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH36 : ((0 : Int) <= i)) (PreH37 : (i < len)) (PreH38 : ((0 : Int) <= c)) (PreH39 : (c <= changes_pre)) (PreH40 : ((0 : Int) <= dir)) (PreH41 : (dir < 2)) (PreH42 : ((0 : Int) <= pos)) (PreH43 : (pos < W)) (PreH44 : ((0 : Int) <= flip)) (PreH45 : (flip <= 2)) (PreH46 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH47 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH48 : (dp ≠ (0 : Int))) (PreH49 : (ndp ≠ (0 : Int))) (PreH50 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH53 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH54 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_59 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= dir)) (PreH2 : (dir < 2)) (PreH3 : (flip <= INT_MAX)) (PreH4 : (pos <= INT_MAX)) (PreH5 : (dir <= INT_MAX)) (PreH6 : (c <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (O <= INT_MAX)) (PreH9 : (W <= INT_MAX)) (PreH10 : (len <= INT_MAX)) (PreH11 : (changes_pre <= INT_MAX)) (PreH12 : ((pos + 1) <= INT_MAX)) (PreH13 : (flip >= INT_MIN)) (PreH14 : (pos >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : ((pos + 1) >= INT_MIN)) (PreH23 : (dir = (0 : Int))) (PreH24 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH25 : ((c + flip) <= changes_pre)) (PreH26 : (flip <= 1)) (PreH27 : (changes_pre = n)) (PreH28 : (len = (Zlength (commands)))) (PreH29 : (W = ((2 * len) + 1))) (PreH30 : (O = len)) (PreH31 : (1 <= len)) (PreH32 : (len <= 100)) (PreH33 : (1 <= changes_pre)) (PreH34 : (changes_pre <= 50)) (PreH35 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH36 : ((0 : Int) <= i)) (PreH37 : (i < len)) (PreH38 : ((0 : Int) <= c)) (PreH39 : (c <= changes_pre)) (PreH40 : ((0 : Int) <= dir)) (PreH41 : (dir < 2)) (PreH42 : ((0 : Int) <= pos)) (PreH43 : (pos < W)) (PreH44 : ((0 : Int) <= flip)) (PreH45 : (flip <= 2)) (PreH46 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH47 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH48 : (dp ≠ (0 : Int))) (PreH49 : (ndp ≠ (0 : Int))) (PreH50 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH53 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH54 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_60 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= dir)) (PreH2 : (dir < 2)) (PreH3 : (flip <= INT_MAX)) (PreH4 : (pos <= INT_MAX)) (PreH5 : (dir <= INT_MAX)) (PreH6 : (c <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (O <= INT_MAX)) (PreH9 : (W <= INT_MAX)) (PreH10 : (len <= INT_MAX)) (PreH11 : (changes_pre <= INT_MAX)) (PreH12 : ((pos + (-1)) <= INT_MAX)) (PreH13 : (flip >= INT_MIN)) (PreH14 : (pos >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : ((pos + (-1)) >= INT_MIN)) (PreH23 : (dir ≠ (0 : Int))) (PreH24 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH25 : ((c + flip) <= changes_pre)) (PreH26 : (flip <= 1)) (PreH27 : (changes_pre = n)) (PreH28 : (len = (Zlength (commands)))) (PreH29 : (W = ((2 * len) + 1))) (PreH30 : (O = len)) (PreH31 : (1 <= len)) (PreH32 : (len <= 100)) (PreH33 : (1 <= changes_pre)) (PreH34 : (changes_pre <= 50)) (PreH35 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH36 : ((0 : Int) <= i)) (PreH37 : (i < len)) (PreH38 : ((0 : Int) <= c)) (PreH39 : (c <= changes_pre)) (PreH40 : ((0 : Int) <= dir)) (PreH41 : (dir < 2)) (PreH42 : ((0 : Int) <= pos)) (PreH43 : (pos < W)) (PreH44 : ((0 : Int) <= flip)) (PreH45 : (flip <= 2)) (PreH46 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH47 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH48 : (dp ≠ (0 : Int))) (PreH49 : (ndp ≠ (0 : Int))) (PreH50 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH53 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH54 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_61 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= dir)) (PreH2 : (dir < 2)) (PreH3 : (flip <= INT_MAX)) (PreH4 : (pos <= INT_MAX)) (PreH5 : (dir <= INT_MAX)) (PreH6 : (c <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (O <= INT_MAX)) (PreH9 : (W <= INT_MAX)) (PreH10 : (len <= INT_MAX)) (PreH11 : (changes_pre <= INT_MAX)) (PreH12 : ((pos + 1) <= INT_MAX)) (PreH13 : (flip >= INT_MIN)) (PreH14 : (pos >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : ((pos + 1) >= INT_MIN)) (PreH23 : (dir = (0 : Int))) (PreH24 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH25 : ((c + flip) <= changes_pre)) (PreH26 : (flip <= 1)) (PreH27 : (changes_pre = n)) (PreH28 : (len = (Zlength (commands)))) (PreH29 : (W = ((2 * len) + 1))) (PreH30 : (O = len)) (PreH31 : (1 <= len)) (PreH32 : (len <= 100)) (PreH33 : (1 <= changes_pre)) (PreH34 : (changes_pre <= 50)) (PreH35 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH36 : ((0 : Int) <= i)) (PreH37 : (i < len)) (PreH38 : ((0 : Int) <= c)) (PreH39 : (c <= changes_pre)) (PreH40 : ((0 : Int) <= dir)) (PreH41 : (dir < 2)) (PreH42 : ((0 : Int) <= pos)) (PreH43 : (pos < W)) (PreH44 : ((0 : Int) <= flip)) (PreH45 : (flip <= 2)) (PreH46 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH47 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH48 : (dp ≠ (0 : Int))) (PreH49 : (ndp ≠ (0 : Int))) (PreH50 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH53 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH54 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_62 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos < (0 : Int))) (PreH2 : ((0 : Int) <= (Z.lxor dir 1))) (PreH3 : ((Z.lxor dir 1) < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (dir <= INT_MAX)) (PreH6 : (c <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (O <= INT_MAX)) (PreH9 : (W <= INT_MAX)) (PreH10 : (len <= INT_MAX)) (PreH11 : (changes_pre <= INT_MAX)) (PreH12 : (pos <= INT_MAX)) (PreH13 : (flip >= INT_MIN)) (PreH14 : (dir >= INT_MIN)) (PreH15 : (c >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (O >= INT_MIN)) (PreH18 : (W >= INT_MIN)) (PreH19 : (len >= INT_MIN)) (PreH20 : (changes_pre >= INT_MIN)) (PreH21 : (pos >= INT_MIN)) (PreH22 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH23 : ((c + flip) <= changes_pre)) (PreH24 : (flip <= 1)) (PreH25 : (changes_pre = n)) (PreH26 : (len = (Zlength (commands)))) (PreH27 : (W = ((2 * len) + 1))) (PreH28 : (O = len)) (PreH29 : (1 <= len)) (PreH30 : (len <= 100)) (PreH31 : (1 <= changes_pre)) (PreH32 : (changes_pre <= 50)) (PreH33 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i < len)) (PreH36 : ((0 : Int) <= c)) (PreH37 : (c <= changes_pre)) (PreH38 : ((0 : Int) <= dir)) (PreH39 : (dir < 2)) (PreH40 : ((0 : Int) <= pos)) (PreH41 : (pos < W)) (PreH42 : ((0 : Int) <= flip)) (PreH43 : (flip <= 2)) (PreH44 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH45 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH46 : (dp ≠ (0 : Int))) (PreH47 : (ndp ≠ (0 : Int))) (PreH48 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH50 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH51 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH52 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_63 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos < (0 : Int))) (PreH2 : ((0 : Int) <= (Z.lxor dir 1))) (PreH3 : ((Z.lxor dir 1) < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (dir <= INT_MAX)) (PreH6 : (c <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (O <= INT_MAX)) (PreH9 : (W <= INT_MAX)) (PreH10 : (len <= INT_MAX)) (PreH11 : (changes_pre <= INT_MAX)) (PreH12 : (pos <= INT_MAX)) (PreH13 : (flip >= INT_MIN)) (PreH14 : (dir >= INT_MIN)) (PreH15 : (c >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (O >= INT_MIN)) (PreH18 : (W >= INT_MIN)) (PreH19 : (len >= INT_MIN)) (PreH20 : (changes_pre >= INT_MIN)) (PreH21 : (pos >= INT_MIN)) (PreH22 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH23 : ((c + flip) <= changes_pre)) (PreH24 : (flip <= 1)) (PreH25 : (changes_pre = n)) (PreH26 : (len = (Zlength (commands)))) (PreH27 : (W = ((2 * len) + 1))) (PreH28 : (O = len)) (PreH29 : (1 <= len)) (PreH30 : (len <= 100)) (PreH31 : (1 <= changes_pre)) (PreH32 : (changes_pre <= 50)) (PreH33 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH34 : ((0 : Int) <= i)) (PreH35 : (i < len)) (PreH36 : ((0 : Int) <= c)) (PreH37 : (c <= changes_pre)) (PreH38 : ((0 : Int) <= dir)) (PreH39 : (dir < 2)) (PreH40 : ((0 : Int) <= pos)) (PreH41 : (pos < W)) (PreH42 : ((0 : Int) <= flip)) (PreH43 : (flip <= 2)) (PreH44 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH45 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH46 : (dp ≠ (0 : Int))) (PreH47 : (ndp ≠ (0 : Int))) (PreH48 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH50 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH51 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH52 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_64 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + 1) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + 1) >= INT_MIN)) (PreH24 : (dir = (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_65 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + 1) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + 1) >= INT_MIN)) (PreH24 : (dir = (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_66 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) >= W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_67 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) >= W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_68 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (pos >= (0 : Int))) (PreH3 : ((0 : Int) <= (Z.lxor dir 1))) (PreH4 : ((Z.lxor dir 1) < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : (pos <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : (pos >= INT_MIN)) (PreH23 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH24 : ((c + flip) <= changes_pre)) (PreH25 : (flip <= 1)) (PreH26 : (changes_pre = n)) (PreH27 : (len = (Zlength (commands)))) (PreH28 : (W = ((2 * len) + 1))) (PreH29 : (O = len)) (PreH30 : (1 <= len)) (PreH31 : (len <= 100)) (PreH32 : (1 <= changes_pre)) (PreH33 : (changes_pre <= 50)) (PreH34 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH35 : ((0 : Int) <= i)) (PreH36 : (i < len)) (PreH37 : ((0 : Int) <= c)) (PreH38 : (c <= changes_pre)) (PreH39 : ((0 : Int) <= dir)) (PreH40 : (dir < 2)) (PreH41 : ((0 : Int) <= pos)) (PreH42 : (pos < W)) (PreH43 : ((0 : Int) <= flip)) (PreH44 : (flip <= 2)) (PreH45 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH46 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH47 : (dp ≠ (0 : Int))) (PreH48 : (ndp ≠ (0 : Int))) (PreH49 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH50 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH52 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH53 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_69 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (pos >= (0 : Int))) (PreH3 : ((0 : Int) <= (Z.lxor dir 1))) (PreH4 : ((Z.lxor dir 1) < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : (pos <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : (pos >= INT_MIN)) (PreH23 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH24 : ((c + flip) <= changes_pre)) (PreH25 : (flip <= 1)) (PreH26 : (changes_pre = n)) (PreH27 : (len = (Zlength (commands)))) (PreH28 : (W = ((2 * len) + 1))) (PreH29 : (O = len)) (PreH30 : (1 <= len)) (PreH31 : (len <= 100)) (PreH32 : (1 <= changes_pre)) (PreH33 : (changes_pre <= 50)) (PreH34 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH35 : ((0 : Int) <= i)) (PreH36 : (i < len)) (PreH37 : ((0 : Int) <= c)) (PreH38 : (c <= changes_pre)) (PreH39 : ((0 : Int) <= dir)) (PreH40 : (dir < 2)) (PreH41 : ((0 : Int) <= pos)) (PreH42 : (pos < W)) (PreH43 : ((0 : Int) <= flip)) (PreH44 : (flip <= 2)) (PreH45 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH46 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH47 : (dp ≠ (0 : Int))) (PreH48 : (ndp ≠ (0 : Int))) (PreH49 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH50 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH52 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH53 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ False ”

noncomputable def solver_safety_wit_70 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((((c + flip) * 2) + dir) * W) + (pos + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((c + flip) * 2) + dir) * W) + (pos + 1))) ”

noncomputable def solver_safety_wit_71 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1)))) ”

noncomputable def solver_safety_wit_72 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((((c + flip) * 2) + dir) * W) + (pos + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((c + flip) * 2) + dir) * W) + (pos + 1))) ”

noncomputable def solver_safety_wit_73 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1)))) ”

noncomputable def solver_safety_wit_74 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) ”

noncomputable def solver_safety_wit_75 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) ”

noncomputable def solver_safety_wit_76 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c + flip) * 2) + dir) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c + flip) * 2) + dir) * W)) ”

noncomputable def solver_safety_wit_77 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c + flip) * 2) + dir) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c + flip) * 2) + dir) * W)) ”

noncomputable def solver_safety_wit_78 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c + flip) * 2) + dir) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c + flip) * 2) + dir) * W)) ”

noncomputable def solver_safety_wit_79 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c + flip) * 2) + dir) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c + flip) * 2) + dir) * W)) ”

noncomputable def solver_safety_wit_80 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c + flip) * 2) + (Z.lxor dir 1)) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c + flip) * 2) + (Z.lxor dir 1)) * W)) ”

noncomputable def solver_safety_wit_81 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((((c + flip) * 2) + (Z.lxor dir 1)) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c + flip) * 2) + (Z.lxor dir 1)) * W)) ”

noncomputable def solver_safety_wit_82 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c + flip) * 2) + dir) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c + flip) * 2) + dir)) ”

noncomputable def solver_safety_wit_83 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c + flip) * 2) + dir) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c + flip) * 2) + dir)) ”

noncomputable def solver_safety_wit_84 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c + flip) * 2) + dir) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c + flip) * 2) + dir)) ”

noncomputable def solver_safety_wit_85 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c + flip) * 2) + dir) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c + flip) * 2) + dir)) ”

noncomputable def solver_safety_wit_86 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c + flip) * 2) + (Z.lxor dir 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c + flip) * 2) + (Z.lxor dir 1))) ”

noncomputable def solver_safety_wit_87 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((((c + flip) * 2) + (Z.lxor dir 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c + flip) * 2) + (Z.lxor dir 1))) ”

noncomputable def solver_safety_wit_88 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c + flip) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c + flip) * 2)) ”

noncomputable def solver_safety_wit_89 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c + flip) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c + flip) * 2)) ”

noncomputable def solver_safety_wit_90 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c + flip) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c + flip) * 2)) ”

noncomputable def solver_safety_wit_91 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c + flip) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c + flip) * 2)) ”

noncomputable def solver_safety_wit_92 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c + flip) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c + flip) * 2)) ”

noncomputable def solver_safety_wit_93 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (((c + flip) * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c + flip) * 2)) ”

noncomputable def solver_safety_wit_94 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_95 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_96 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_97 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_98 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_99 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + flip)) ”

noncomputable def solver_safety_wit_100 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_101 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_102 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_103 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_104 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_105 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_106 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_107 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_108 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_109 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_110 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_111 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_112 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) (1) (next_table)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_113 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) (1) (next_table)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_114 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + (-1)))) (1) (next_table)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_115 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + 1))) (1) (next_table)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_116 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + (-1)))) (1) (next_table)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_117 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + 1))) (1) (next_table)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_118 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_119 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_120 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_121 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_122 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) > changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((flip + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (flip + 1)) ”

noncomputable def solver_safety_wit_123 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip > 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((pos + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + 1)) ”

noncomputable def solver_safety_wit_124 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) = (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((pos + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + 1)) ”

noncomputable def solver_safety_wit_125 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= W)) (PreH19 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH20 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH21 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH27 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((dir + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (dir + 1)) ”

noncomputable def solver_safety_wit_126 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_safety_wit_127 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (current_table : (List Int)) (next_table : (List Int)) (len : Int) (W : Int) (O : Int) (i : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH17 : (TurtleNextPrefix commands i changes_pre ((((changes_pre + 1) * 2) * W) * 2) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (ndp))
  ** ((( &( "ndp" ) )) # Ptr |-> (dp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_128 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : (dp ≠ (0 : Int))) (PreH11 : (ndp ≠ (0 : Int))) (PreH12 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH13 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH14 : (TurtleLayerMeaning commands len changes_pre final_table)) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_129 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : (dp ≠ (0 : Int))) (PreH11 : (ndp ≠ (0 : Int))) (PreH12 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH13 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH14 : (TurtleLayerMeaning commands len changes_pre final_table)) ,
  ((( &( "c" ) )) # Int |->_)
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_130 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((changes_pre - c) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (changes_pre - c)) ”

noncomputable def solver_safety_wit_131 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_132 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_133 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_134 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= c)) (PreH11 : (c <= changes_pre)) (PreH12 : ((0 : Int) <= d)) (PreH13 : (d <= 2)) (PreH14 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH15 : ((0 : Int) <= ans)) (PreH16 : (ans <= len)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH22 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_135 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  ((( &( "p" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_136 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (((((c * 2) + d) * W) + p) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((c * 2) + d) * W) + p)) ”

noncomputable def solver_safety_wit_137 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((((c * 2) + d) * W) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((c * 2) + d) * W)) ”

noncomputable def solver_safety_wit_138 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (((c * 2) + d) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((c * 2) + d)) ”

noncomputable def solver_safety_wit_139 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((c * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c * 2)) ”

noncomputable def solver_safety_wit_140 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_141 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int |->_)
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((p - O) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p - O)) ”

noncomputable def solver_safety_wit_142 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (retval))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((p + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p + 1)) ”

noncomputable def solver_safety_wit_143 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (retval))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((p + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p + 1)) ”

noncomputable def solver_safety_wit_144 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((p + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p + 1)) ”

noncomputable def solver_safety_wit_145 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((p + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p + 1)) ”

noncomputable def solver_safety_wit_146 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) = (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((p + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p + 1)) ”

noncomputable def solver_safety_wit_147 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (p >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d < 2)) (PreH15 : ((0 : Int) <= p)) (PreH16 : (p <= W)) (PreH17 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= len)) (PreH20 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH21 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH27 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((d + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (d + 1)) ”

noncomputable def solver_safety_wit_148 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_safety_wit_149 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) ≠ (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (replace_Znth ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) (1) ((repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))))
  ** (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX spare_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (retval = (Zlength (commands))) ” &&
  “ (((2 * retval) + 1) = ((2 * retval) + 1)) ” &&
  “ (retval = retval) ” &&
  “ (1 <= retval) ” &&
  “ (retval <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < retval)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) <= INT_MAX) ” &&
  “ (retval_2 ≠ (0 : Int)) ” &&
  “ (retval_3 ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ (TurtleLayerMeaning commands (0 : Int) changes_pre current_table) ”
  &&  (charArray.full s_pre (retval + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) current_table)
  ** (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  TT && emp 
|--
  “ (TurtleLayerMeaning commands (0 : Int) n (replace_Znth ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) (1) ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * retval) + 1))))))) ” &&
  “ ((Zlength ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * retval) + 1)))))) = (((n + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((Zlength ((replace_Znth ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) (1) ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * retval) + 1)))))))) = (((n + 1) * 2) * ((2 * retval) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (TurtleLayerMeaning commands (0 : Int) n (replace_Znth ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) (1) ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * retval) + 1)))))))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  ((Zlength ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * retval) + 1)))))) = (((n + 1) * 2) * ((2 * retval) + 1)))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  ((Zlength ((replace_Znth ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval)) (1) ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * retval) + 1)))))))) = (((n + 1) * 2) * ((2 * retval) + 1)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval = ndp)) (PreH2 : (i < len)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= len)) (PreH14 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH15 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands i changes_pre current_table_2)) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * W))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (changes_pre + 1)) ” &&
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((4 * (0 : Int)) * W) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval = ndp)) (PreH2 : (i < len)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= len)) (PreH14 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH15 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands i changes_pre current_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((4 * (0 : Int)) * ((2 * O) + 1)) (repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * O) + 1))))) ” &&
  “ ((Zlength ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * O) + 1)))))) = (((n + 1) * 2) * ((2 * O) + 1))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval = ndp)) (PreH2 : (i < len)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= len)) (PreH14 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH15 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands i changes_pre current_table_2)) ,
  (TurtleNextPrefix commands i n ((4 * (0 : Int)) * ((2 * O) + 1)) (repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * O) + 1)))))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval = ndp)) (PreH2 : (i < len)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= len)) (PreH14 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH15 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands i changes_pre current_table_2)) ,
  ((Zlength ((repeat_Z ((0 : Int)) ((((n + 1) * 2) * ((2 * O) + 1)))))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_2_split_goal_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval = ndp)) (PreH2 : (i < len)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= len)) (PreH14 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH15 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands i changes_pre current_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + (0 : Int)) * W)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n (2 * (((c * 2) + (0 : Int)) * ((2 * O) + 1))) next_table_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  (TurtleNextPrefix commands i n (2 * (((c * 2) + (0 : Int)) * ((2 * O) + 1))) next_table_2)

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c <= changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= W) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + (0 : Int))) ” &&
  “ (((((c * 2) + dir) * W) + (0 : Int)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + (0 : Int))) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (0 : Int))) next_table_2) ” &&
  “ (((((c * 2) + dir) * ((2 * O) + 1)) + (0 : Int)) <= (((n + 1) * 2) * ((2 * O) + 1))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  (TurtleNextPrefix commands i n (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (0 : Int))) next_table_2)

noncomputable def solver_entail_wit_4_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  (((((c * 2) + dir) * ((2 * O) + 1)) + (0 : Int)) <= (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_4_split_goal_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos < W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= W)) (PreH19 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH20 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH21 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH27 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + pos)) ” &&
  “ (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (pos < W) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= W) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + pos)) ” &&
  “ (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : (pos >= INT_MIN)) (PreH10 : (dir >= INT_MIN)) (PreH11 : (c >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (O >= INT_MIN)) (PreH14 : (W >= INT_MIN)) (PreH15 : (len >= INT_MIN)) (PreH16 : (changes_pre >= INT_MIN)) (PreH17 : (pos < W)) (PreH18 : (changes_pre = n)) (PreH19 : (len = (Zlength (commands)))) (PreH20 : (W = ((2 * len) + 1))) (PreH21 : (O = len)) (PreH22 : (1 <= len)) (PreH23 : (len <= 100)) (PreH24 : (1 <= changes_pre)) (PreH25 : (changes_pre <= 50)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH27 : ((0 : Int) <= i)) (PreH28 : (i < len)) (PreH29 : ((0 : Int) <= c)) (PreH30 : (c <= changes_pre)) (PreH31 : ((0 : Int) <= dir)) (PreH32 : (dir < 2)) (PreH33 : ((0 : Int) <= pos)) (PreH34 : (pos <= W)) (PreH35 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH36 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH37 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH38 : (dp ≠ (0 : Int))) (PreH39 : (ndp ≠ (0 : Int))) (PreH40 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH41 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH42 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH43 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  TT && emp 
|--
  “ (((((c * 2) + dir) * ((2 * O) + 1)) + pos) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : (pos >= INT_MIN)) (PreH10 : (dir >= INT_MIN)) (PreH11 : (c >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (O >= INT_MIN)) (PreH14 : (W >= INT_MIN)) (PreH15 : (len >= INT_MIN)) (PreH16 : (changes_pre >= INT_MIN)) (PreH17 : (pos < W)) (PreH18 : (changes_pre = n)) (PreH19 : (len = (Zlength (commands)))) (PreH20 : (W = ((2 * len) + 1))) (PreH21 : (O = len)) (PreH22 : (1 <= len)) (PreH23 : (len <= 100)) (PreH24 : (1 <= changes_pre)) (PreH25 : (changes_pre <= 50)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH27 : ((0 : Int) <= i)) (PreH28 : (i < len)) (PreH29 : ((0 : Int) <= c)) (PreH30 : (c <= changes_pre)) (PreH31 : ((0 : Int) <= dir)) (PreH32 : (dir < 2)) (PreH33 : ((0 : Int) <= pos)) (PreH34 : (pos <= W)) (PreH35 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH36 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH37 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH38 : (dp ≠ (0 : Int))) (PreH39 : (ndp ≠ (0 : Int))) (PreH40 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH41 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH42 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH43 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  (((((c * 2) + dir) * ((2 * O) + 1)) + pos) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (0 : Int)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (0 : Int)) next_table_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (0 : Int)) next_table_2)

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_7_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (Z.lxor dir 1)) ” &&
  “ ((Z.lxor dir 1) < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : ((Z.lxor dir 1) <= INT_MAX)) (PreH10 : (pos <= INT_MAX)) (PreH11 : (flip >= INT_MIN)) (PreH12 : (dir >= INT_MIN)) (PreH13 : (c >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (O >= INT_MIN)) (PreH16 : (W >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (changes_pre >= INT_MIN)) (PreH19 : ((Z.lxor dir 1) >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ ((Z.lxor dir 1) < 2) ” &&
  “ ((0 : Int) <= (Z.lxor dir 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : ((Z.lxor dir 1) <= INT_MAX)) (PreH10 : (pos <= INT_MAX)) (PreH11 : (flip >= INT_MIN)) (PreH12 : (dir >= INT_MIN)) (PreH13 : (c >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (O >= INT_MIN)) (PreH16 : (W >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (changes_pre >= INT_MIN)) (PreH19 : ((Z.lxor dir 1) >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip ≠ (0 : Int))) ,
  ((Z.lxor dir 1) < 2)

noncomputable def solver_entail_wit_7_1_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : ((Z.lxor dir 1) <= INT_MAX)) (PreH10 : (pos <= INT_MAX)) (PreH11 : (flip >= INT_MIN)) (PreH12 : (dir >= INT_MIN)) (PreH13 : (c >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (O >= INT_MIN)) (PreH16 : (W >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (changes_pre >= INT_MIN)) (PreH19 : ((Z.lxor dir 1) >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.lxor dir 1))

noncomputable def solver_entail_wit_7_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH2 : ((c + flip) <= changes_pre)) (PreH3 : (flip <= 1)) (PreH4 : (changes_pre = n)) (PreH5 : (len = (Zlength (commands)))) (PreH6 : (W = ((2 * len) + 1))) (PreH7 : (O = len)) (PreH8 : (1 <= len)) (PreH9 : (len <= 100)) (PreH10 : (1 <= changes_pre)) (PreH11 : (changes_pre <= 50)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < len)) (PreH15 : ((0 : Int) <= c)) (PreH16 : (c <= changes_pre)) (PreH17 : ((0 : Int) <= dir)) (PreH18 : (dir < 2)) (PreH19 : ((0 : Int) <= pos)) (PreH20 : (pos < W)) (PreH21 : ((0 : Int) <= flip)) (PreH22 : (flip <= 2)) (PreH23 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH24 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH25 : (dp ≠ (0 : Int))) (PreH26 : (ndp ≠ (0 : Int))) (PreH27 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH30 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH31 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (Z.lxor dir 1)) ” &&
  “ ((Z.lxor dir 1) < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : ((Z.lxor dir 1) <= INT_MAX)) (PreH10 : (pos <= INT_MAX)) (PreH11 : (flip >= INT_MIN)) (PreH12 : (dir >= INT_MIN)) (PreH13 : (c >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (O >= INT_MIN)) (PreH16 : (W >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (changes_pre >= INT_MIN)) (PreH19 : ((Z.lxor dir 1) >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ ((Z.lxor dir 1) < 2) ” &&
  “ ((0 : Int) <= (Z.lxor dir 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : ((Z.lxor dir 1) <= INT_MAX)) (PreH10 : (pos <= INT_MAX)) (PreH11 : (flip >= INT_MIN)) (PreH12 : (dir >= INT_MIN)) (PreH13 : (c >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (O >= INT_MIN)) (PreH16 : (W >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (changes_pre >= INT_MIN)) (PreH19 : ((Z.lxor dir 1) >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip = (0 : Int))) ,
  ((Z.lxor dir 1) < 2)

noncomputable def solver_entail_wit_7_2_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip <= INT_MAX)) (PreH2 : (dir <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : ((Z.lxor dir 1) <= INT_MAX)) (PreH10 : (pos <= INT_MAX)) (PreH11 : (flip >= INT_MIN)) (PreH12 : (dir >= INT_MIN)) (PreH13 : (c >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (O >= INT_MIN)) (PreH16 : (W >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (changes_pre >= INT_MIN)) (PreH19 : ((Z.lxor dir 1) >= INT_MIN)) (PreH20 : (pos >= INT_MIN)) (PreH21 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH22 : ((c + flip) <= changes_pre)) (PreH23 : (flip <= 1)) (PreH24 : (changes_pre = n)) (PreH25 : (len = (Zlength (commands)))) (PreH26 : (W = ((2 * len) + 1))) (PreH27 : (O = len)) (PreH28 : (1 <= len)) (PreH29 : (len <= 100)) (PreH30 : (1 <= changes_pre)) (PreH31 : (changes_pre <= 50)) (PreH32 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH33 : ((0 : Int) <= i)) (PreH34 : (i < len)) (PreH35 : ((0 : Int) <= c)) (PreH36 : (c <= changes_pre)) (PreH37 : ((0 : Int) <= dir)) (PreH38 : (dir < 2)) (PreH39 : ((0 : Int) <= pos)) (PreH40 : (pos < W)) (PreH41 : ((0 : Int) <= flip)) (PreH42 : (flip <= 2)) (PreH43 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH44 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH45 : (dp ≠ (0 : Int))) (PreH46 : (ndp ≠ (0 : Int))) (PreH47 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH48 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH49 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH50 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH51 : (flip = (0 : Int))) ,
  ((0 : Int) <= (Z.lxor dir 1))

noncomputable def solver_entail_wit_7_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + (-1)) >= INT_MIN) ” &&
  “ (dir ≠ (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)

noncomputable def solver_entail_wit_7_4 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir = (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip ≠ (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + 1) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + 1) >= INT_MIN) ” &&
  “ (dir = (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)

noncomputable def solver_entail_wit_7_5 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir ≠ (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + (-1)) >= INT_MIN) ” &&
  “ (dir ≠ (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)

noncomputable def solver_entail_wit_7_6 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir = (0 : Int))) (PreH2 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH3 : ((c + flip) <= changes_pre)) (PreH4 : (flip <= 1)) (PreH5 : (changes_pre = n)) (PreH6 : (len = (Zlength (commands)))) (PreH7 : (W = ((2 * len) + 1))) (PreH8 : (O = len)) (PreH9 : (1 <= len)) (PreH10 : (len <= 100)) (PreH11 : (1 <= changes_pre)) (PreH12 : (changes_pre <= 50)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < len)) (PreH16 : ((0 : Int) <= c)) (PreH17 : (c <= changes_pre)) (PreH18 : ((0 : Int) <= dir)) (PreH19 : (dir < 2)) (PreH20 : ((0 : Int) <= pos)) (PreH21 : (pos < W)) (PreH22 : ((0 : Int) <= flip)) (PreH23 : (flip <= 2)) (PreH24 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH25 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH26 : (dp ≠ (0 : Int))) (PreH27 : (ndp ≠ (0 : Int))) (PreH28 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH29 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH30 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH31 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH32 : (flip = (0 : Int))) ,
  ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + 1) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + 1) >= INT_MIN) ” &&
  “ (dir = (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)

noncomputable def solver_entail_wit_8_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos < W)) (PreH2 : (pos >= (0 : Int))) (PreH3 : ((0 : Int) <= (Z.lxor dir 1))) (PreH4 : ((Z.lxor dir 1) < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : (pos <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : (pos >= INT_MIN)) (PreH23 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH24 : ((c + flip) <= changes_pre)) (PreH25 : (flip <= 1)) (PreH26 : (changes_pre = n)) (PreH27 : (len = (Zlength (commands)))) (PreH28 : (W = ((2 * len) + 1))) (PreH29 : (O = len)) (PreH30 : (1 <= len)) (PreH31 : (len <= 100)) (PreH32 : (1 <= changes_pre)) (PreH33 : (changes_pre <= 50)) (PreH34 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH35 : ((0 : Int) <= i)) (PreH36 : (i < len)) (PreH37 : ((0 : Int) <= c)) (PreH38 : (c <= changes_pre)) (PreH39 : ((0 : Int) <= dir)) (PreH40 : (dir < 2)) (PreH41 : ((0 : Int) <= pos)) (PreH42 : (pos < W)) (PreH43 : ((0 : Int) <= flip)) (PreH44 : (flip <= 2)) (PreH45 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH46 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH47 : (dp ≠ (0 : Int))) (PreH48 : (ndp ≠ (0 : Int))) (PreH49 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH50 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH52 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH53 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) ” &&
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (pos < W) ” &&
  “ (pos >= (0 : Int)) ” &&
  “ ((0 : Int) <= (Z.lxor dir 1)) ” &&
  “ ((Z.lxor dir 1) < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (84))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.lxor dir 1) <= INT_MAX)) (PreH2 : ((Z.lxor dir 1) >= INT_MIN)) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.lxor dir 1) <= INT_MAX)) (PreH2 : ((Z.lxor dir 1) >= INT_MIN)) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_8_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos < W)) (PreH2 : (pos >= (0 : Int))) (PreH3 : ((0 : Int) <= (Z.lxor dir 1))) (PreH4 : ((Z.lxor dir 1) < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : (pos <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (dir >= INT_MIN)) (PreH16 : (c >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (O >= INT_MIN)) (PreH19 : (W >= INT_MIN)) (PreH20 : (len >= INT_MIN)) (PreH21 : (changes_pre >= INT_MIN)) (PreH22 : (pos >= INT_MIN)) (PreH23 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH24 : ((c + flip) <= changes_pre)) (PreH25 : (flip <= 1)) (PreH26 : (changes_pre = n)) (PreH27 : (len = (Zlength (commands)))) (PreH28 : (W = ((2 * len) + 1))) (PreH29 : (O = len)) (PreH30 : (1 <= len)) (PreH31 : (len <= 100)) (PreH32 : (1 <= changes_pre)) (PreH33 : (changes_pre <= 50)) (PreH34 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH35 : ((0 : Int) <= i)) (PreH36 : (i < len)) (PreH37 : ((0 : Int) <= c)) (PreH38 : (c <= changes_pre)) (PreH39 : ((0 : Int) <= dir)) (PreH40 : (dir < 2)) (PreH41 : ((0 : Int) <= pos)) (PreH42 : (pos < W)) (PreH43 : ((0 : Int) <= flip)) (PreH44 : (flip <= 2)) (PreH45 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH46 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH47 : (dp ≠ (0 : Int))) (PreH48 : (ndp ≠ (0 : Int))) (PreH49 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH50 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH51 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH52 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH53 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) ” &&
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (pos < W) ” &&
  “ (pos >= (0 : Int)) ” &&
  “ ((0 : Int) <= (Z.lxor dir 1)) ” &&
  “ ((Z.lxor dir 1) < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> ((Z.lxor dir 1)))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> (pos))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.lxor dir 1) <= INT_MAX)) (PreH2 : ((Z.lxor dir 1) >= INT_MIN)) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.lxor dir 1) <= INT_MAX)) (PreH2 : ((Z.lxor dir 1) >= INT_MIN)) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_8_3 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1)))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + (-1)) < W) ” &&
  “ ((pos + (-1)) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + (-1)) >= INT_MIN) ” &&
  “ (dir ≠ (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1))) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_3_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1))) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_8_4 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + 1) < W) ” &&
  “ ((pos + 1) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + 1) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + 1) >= INT_MIN) ” &&
  “ (dir = (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> (70))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1)) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_4_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip ≠ (0 : Int))) ,
  ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1)) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_8_5 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1)))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + (-1)) < W) ” &&
  “ ((pos + (-1)) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + (-1)) >= INT_MIN) ” &&
  “ (dir ≠ (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + (-1))))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1))) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_5_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < W)) (PreH2 : ((pos + (-1)) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + (-1)) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + (-1)) >= INT_MIN)) (PreH25 : (dir ≠ (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1))) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_8_6 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + 1) < W) ” &&
  “ ((pos + 1) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + 1) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + 1) >= INT_MIN) ” &&
  “ (dir = (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "flip" ) )) # Int |-> (flip))
  ** ((( &( "nd" ) )) # Int |-> (dir))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "np" ) )) # Int |-> ((pos + 1)))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "cmd" ) )) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dir" ) )) # Int |-> (dir))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1)) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_6_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) < W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH56 : (flip = (0 : Int))) ,
  ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1)) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) (1) (next_table_2)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) (replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2))) ” &&
  “ ((Zlength ((replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) (replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2)))

noncomputable def solver_entail_wit_9_1_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  ((Zlength ((replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) (1) (next_table_2)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) (replace_Znth ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2))) ” &&
  “ ((Zlength ((replace_Znth ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) (replace_Znth ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2)))

noncomputable def solver_entail_wit_9_2_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  ((Zlength ((replace_Znth ((((((c + (0 : Int)) * 2) + (Z.lxor dir 1)) * ((2 * O) + 1)) + pos)) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_3 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + (-1)))) (1) (next_table_2)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) (replace_Znth ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2))) ” &&
  “ ((Zlength ((replace_Znth ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_3_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) (replace_Znth ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2)))

noncomputable def solver_entail_wit_9_3_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((Zlength ((replace_Znth ((((((c + flip) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_4 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + 1))) (1) (next_table_2)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1)) (replace_Znth ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2))) ” &&
  “ ((Zlength ((replace_Znth ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_4_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1)) (replace_Znth ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2)))

noncomputable def solver_entail_wit_9_4_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip ≠ (0 : Int))) ,
  ((Zlength ((replace_Znth ((((((c + flip) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_5 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + (-1)))) (1) (next_table_2)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) (replace_Znth ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2))) ” &&
  “ ((Zlength ((replace_Znth ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_5_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) (replace_Znth ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2)))

noncomputable def solver_entail_wit_9_5_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  ((Zlength ((replace_Znth ((((((c + (0 : Int)) * 2) + dir) * ((2 * O) + 1)) + (pos + (-1)))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_6 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) (replace_Znth ((((((c + flip) * 2) + dir) * W) + (pos + 1))) (1) (next_table_2)))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) (replace_Znth ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2))) ” &&
  “ ((Zlength ((replace_Znth ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_6_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) (replace_Znth ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2)))

noncomputable def solver_entail_wit_9_6_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH58 : (flip = (0 : Int))) ,
  ((Zlength ((replace_Znth ((((((c + (0 : Int)) * 2) + (0 : Int)) * ((2 * O) + 1)) + (pos + 1))) (1) (next_table_2)))) = (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_9_7 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) next_table_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_7_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip = (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) next_table_2)

noncomputable def solver_entail_wit_9_8 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) next_table_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_8_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + (-1)) < (0 : Int))) (PreH2 : ((0 : Int) <= dir)) (PreH3 : (dir < 2)) (PreH4 : (flip <= INT_MAX)) (PreH5 : (pos <= INT_MAX)) (PreH6 : (dir <= INT_MAX)) (PreH7 : (c <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (O <= INT_MAX)) (PreH10 : (W <= INT_MAX)) (PreH11 : (len <= INT_MAX)) (PreH12 : (changes_pre <= INT_MAX)) (PreH13 : ((pos + (-1)) <= INT_MAX)) (PreH14 : (flip >= INT_MIN)) (PreH15 : (pos >= INT_MIN)) (PreH16 : (dir >= INT_MIN)) (PreH17 : (c >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (O >= INT_MIN)) (PreH20 : (W >= INT_MIN)) (PreH21 : (len >= INT_MIN)) (PreH22 : (changes_pre >= INT_MIN)) (PreH23 : ((pos + (-1)) >= INT_MIN)) (PreH24 : (dir ≠ (0 : Int))) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH55 : (flip ≠ (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) next_table_2)

noncomputable def solver_entail_wit_9_9 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH56 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH56 : (flip ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1)) next_table_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_9_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH56 : (flip ≠ (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + (flip + 1)) next_table_2)

noncomputable def solver_entail_wit_9_10 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH56 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH56 : (flip = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) next_table_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_10_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((pos + 1) >= W)) (PreH2 : ((pos + 1) >= (0 : Int))) (PreH3 : ((0 : Int) <= dir)) (PreH4 : (dir < 2)) (PreH5 : (flip <= INT_MAX)) (PreH6 : (pos <= INT_MAX)) (PreH7 : (dir <= INT_MAX)) (PreH8 : (c <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (O <= INT_MAX)) (PreH11 : (W <= INT_MAX)) (PreH12 : (len <= INT_MAX)) (PreH13 : (changes_pre <= INT_MAX)) (PreH14 : ((pos + 1) <= INT_MAX)) (PreH15 : (flip >= INT_MIN)) (PreH16 : (pos >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : ((pos + 1) >= INT_MIN)) (PreH25 : (dir = (0 : Int))) (PreH26 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH27 : ((c + flip) <= changes_pre)) (PreH28 : (flip <= 1)) (PreH29 : (changes_pre = n)) (PreH30 : (len = (Zlength (commands)))) (PreH31 : (W = ((2 * len) + 1))) (PreH32 : (O = len)) (PreH33 : (1 <= len)) (PreH34 : (len <= 100)) (PreH35 : (1 <= changes_pre)) (PreH36 : (changes_pre <= 50)) (PreH37 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH38 : ((0 : Int) <= i)) (PreH39 : (i < len)) (PreH40 : ((0 : Int) <= c)) (PreH41 : (c <= changes_pre)) (PreH42 : ((0 : Int) <= dir)) (PreH43 : (dir < 2)) (PreH44 : ((0 : Int) <= pos)) (PreH45 : (pos < W)) (PreH46 : ((0 : Int) <= flip)) (PreH47 : (flip <= 2)) (PreH48 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH49 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH50 : (dp ≠ (0 : Int))) (PreH51 : (ndp ≠ (0 : Int))) (PreH52 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH53 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH54 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH55 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) (PreH56 : (flip = (0 : Int))) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + (0 : Int)) * ((2 * O) + 1)) + pos)) + ((0 : Int) + 1)) next_table_2)

noncomputable def solver_entail_wit_9_11 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) > changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= (flip + 1)) ” &&
  “ ((flip + 1) <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + (flip + 1)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) > changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) next_table_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_11_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) > changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  (TurtleNextPrefix commands i n ((2 * ((((c * 2) + dir) * ((2 * O) + 1)) + pos)) + (flip + 1)) next_table_2)

noncomputable def solver_entail_wit_10_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip > 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= (pos + 1)) ” &&
  “ ((pos + 1) <= W) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + (pos + 1))) ” &&
  “ (((((c * 2) + dir) * W) + (pos + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + (pos + 1))) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip > 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1))) next_table_2) ” &&
  “ (((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1)) <= (((n + 1) * 2) * ((2 * O) + 1))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip > 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  (TurtleNextPrefix commands i n (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1))) next_table_2)

noncomputable def solver_entail_wit_10_1_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip > 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  (((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1)) <= (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_10_1_split_goal_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (ndp : Int) (dp : Int) (current_table_2 : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (flip > 1)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos < W)) (PreH19 : ((0 : Int) <= flip)) (PreH20 : (flip <= 2)) (PreH21 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) ≠ (0 : Int))) (PreH22 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH23 : (dp ≠ (0 : Int))) (PreH24 : (ndp ≠ (0 : Int))) (PreH25 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH27 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH28 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_10_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) = (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= (pos + 1)) ” &&
  “ ((pos + 1) <= W) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + (pos + 1))) ” &&
  “ (((((c * 2) + dir) * W) + (pos + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + (pos + 1))) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1))) next_table_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) (PreH36 : ((Znth ((((c * 2) + dir) * W) + pos) current_table_2 (0 : Int)) = (0 : Int))) ,
  (TurtleNextPrefix commands i n (2 * ((((c * 2) + dir) * ((2 * O) + 1)) + (pos + 1))) next_table_2)

noncomputable def solver_entail_wit_11 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= W)) (PreH19 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH20 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH21 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH27 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= (dir + 1)) ” &&
  “ ((dir + 1) <= 2) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + (dir + 1)) * W)) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= W)) (PreH19 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH20 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH21 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH27 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n (2 * (((c * 2) + (dir + 1)) * ((2 * O) + 1))) next_table_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_11_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= W)) (PreH19 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH20 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH21 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH27 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) ,
  (TurtleNextPrefix commands i n (2 * (((c * 2) + (dir + 1)) * ((2 * O) + 1))) next_table_2)

noncomputable def solver_entail_wit_11_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (pos >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir < 2)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= W)) (PreH19 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH20 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH21 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH27 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_12 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= (changes_pre + 1)) ” &&
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((4 * (c + 1)) * W) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((4 * (c + 1)) * ((2 * O) + 1)) next_table_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  (TurtleNextPrefix commands i n ((4 * (c + 1)) * ((2 * O) + 1)) next_table_2)

noncomputable def solver_entail_wit_12_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (dir >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= changes_pre)) (PreH15 : ((0 : Int) <= dir)) (PreH16 : (dir <= 2)) (PreH17 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH23 : (TurtleNextPrefix commands i changes_pre (2 * (((c * 2) + dir) * W)) next_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_13 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table_2)
|--
  EX next_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((((changes_pre + 1) * 2) * W) * 2) next_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  TT && emp 
|--
  “ (TurtleNextPrefix commands i n ((((n + 1) * 2) * ((2 * O) + 1)) * 2) next_table_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_13_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  (TurtleNextPrefix commands i n ((((n + 1) * 2) * ((2 * O) + 1)) * 2) next_table_2)

noncomputable def solver_entail_wit_13_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (next_table_2 : (List Int)) (current_table_2 : (List Int)) (ndp : Int) (dp : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < len)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (changes_pre + 1))) (PreH15 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH16 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH17 : (dp ≠ (0 : Int))) (PreH18 : (ndp ≠ (0 : Int))) (PreH19 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : ((Zlength (next_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH22 : (TurtleNextPrefix commands i changes_pre ((4 * c) * W) next_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_14 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (current_table_2 : (List Int)) (next_table : (List Int)) (len : Int) (W : Int) (O : Int) (i : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH17 : (TurtleNextPrefix commands i changes_pre ((((changes_pre + 1) * 2) * W) * 2) next_table)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  EX spare_table : (List Int), EX current_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= len) ” &&
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands (i + 1) changes_pre current_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (current_table_2 : (List Int)) (next_table : (List Int)) (len : Int) (W : Int) (O : Int) (i : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH17 : (TurtleNextPrefix commands i changes_pre ((((changes_pre + 1) * 2) * W) * 2) next_table)) ,
  TT && emp 
|--
  “ (TurtleLayerMeaning commands (i + 1) n next_table) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_14_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (current_table_2 : (List Int)) (next_table : (List Int)) (len : Int) (W : Int) (O : Int) (i : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH17 : (TurtleNextPrefix commands i changes_pre ((((changes_pre + 1) * 2) * W) * 2) next_table)) ,
  (TurtleLayerMeaning commands (i + 1) n next_table)

noncomputable def solver_entail_wit_14_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (current_table_2 : (List Int)) (next_table : (List Int)) (len : Int) (W : Int) (O : Int) (i : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (current_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (TurtleLayerMeaning commands i changes_pre current_table_2)) (PreH17 : (TurtleNextPrefix commands i changes_pre ((((changes_pre + 1) * 2) * W) * 2) next_table)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_15 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i >= len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i >= len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  TT && emp 
|--
  “ (TurtleLayerMeaning commands O n current_table) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_15_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i >= len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  (TurtleLayerMeaning commands O n current_table)

noncomputable def solver_entail_wit_15_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i >= len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_16 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table_2 : (List Int)) (spare_table_2 : (List Int)) (len : Int) (W : Int) (O : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : (dp ≠ (0 : Int))) (PreH11 : (ndp ≠ (0 : Int))) (PreH12 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH13 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH14 : (TurtleLayerMeaning commands len changes_pre final_table_2)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (changes_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre (((0 : Int) * 2) * W) (0 : Int)) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (final_table_2 : (List Int)) (spare_table_2 : (List Int)) (len : Int) (W : Int) (O : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : (dp ≠ (0 : Int))) (PreH11 : (ndp ≠ (0 : Int))) (PreH12 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH13 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH14 : (TurtleLayerMeaning commands len changes_pre final_table_2)) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n (((0 : Int) * 2) * ((2 * len) + 1)) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_16_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (final_table_2 : (List Int)) (spare_table_2 : (List Int)) (len : Int) (W : Int) (O : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : (dp ≠ (0 : Int))) (PreH11 : (ndp ≠ (0 : Int))) (PreH12 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH13 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH14 : (TurtleLayerMeaning commands len changes_pre final_table_2)) ,
  (TurtleAnswerPrefix commands n (((0 : Int) * 2) * ((2 * len) + 1)) (0 : Int))

noncomputable def solver_entail_wit_16_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (final_table_2 : (List Int)) (spare_table_2 : (List Int)) (len : Int) (W : Int) (O : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH10 : (dp ≠ (0 : Int))) (PreH11 : (ndp ≠ (0 : Int))) (PreH12 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH13 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH14 : (TurtleLayerMeaning commands len changes_pre final_table_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_17 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre (((c * 2) + (0 : Int)) * W) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n (((c * 2) + (0 : Int)) * ((2 * O) + 1)) ans) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_17_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  (TurtleAnswerPrefix commands n (((c * 2) + (0 : Int)) * ((2 * O) + 1)) ans)

noncomputable def solver_entail_wit_17_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_18 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + (0 : Int))) ” &&
  “ (((((c * 2) + d) * W) + (0 : Int)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + (0 : Int)) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (0 : Int)) ans) ” &&
  “ (((((c * 2) + d) * ((2 * O) + 1)) + (0 : Int)) <= (((n + 1) * 2) * ((2 * O) + 1))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_18_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (0 : Int)) ans)

noncomputable def solver_entail_wit_18_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  (((((c * 2) + d) * ((2 * O) + 1)) + (0 : Int)) <= (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_18_split_goal_3 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d < 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_19 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (p < W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d < 2)) (PreH15 : ((0 : Int) <= p)) (PreH16 : (p <= W)) (PreH17 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= len)) (PreH20 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH21 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH27 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= ((((c * 2) + d) * W) + p)) ” &&
  “ (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (p < W) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + p)) ” &&
  “ (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans) ”
  &&  ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (ans <= INT_MAX)) (PreH2 : (p <= INT_MAX)) (PreH3 : (d <= INT_MAX)) (PreH4 : (c <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (d >= INT_MIN)) (PreH12 : (c >= INT_MIN)) (PreH13 : (O >= INT_MIN)) (PreH14 : (W >= INT_MIN)) (PreH15 : (len >= INT_MIN)) (PreH16 : (changes_pre >= INT_MIN)) (PreH17 : (p < W)) (PreH18 : (changes_pre = n)) (PreH19 : (len = (Zlength (commands)))) (PreH20 : (W = ((2 * len) + 1))) (PreH21 : (O = len)) (PreH22 : (1 <= len)) (PreH23 : (len <= 100)) (PreH24 : (1 <= changes_pre)) (PreH25 : (changes_pre <= 50)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH27 : ((0 : Int) <= c)) (PreH28 : (c <= changes_pre)) (PreH29 : ((0 : Int) <= d)) (PreH30 : (d < 2)) (PreH31 : ((0 : Int) <= p)) (PreH32 : (p <= W)) (PreH33 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH34 : ((0 : Int) <= ans)) (PreH35 : (ans <= len)) (PreH36 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH37 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH38 : (dp ≠ (0 : Int))) (PreH39 : (ndp ≠ (0 : Int))) (PreH40 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH41 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH42 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH43 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  TT && emp 
|--
  “ (((((c * 2) + d) * ((2 * O) + 1)) + p) < (((n + 1) * 2) * ((2 * O) + 1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_19_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (ans <= INT_MAX)) (PreH2 : (p <= INT_MAX)) (PreH3 : (d <= INT_MAX)) (PreH4 : (c <= INT_MAX)) (PreH5 : (O <= INT_MAX)) (PreH6 : (W <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (changes_pre <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (d >= INT_MIN)) (PreH12 : (c >= INT_MIN)) (PreH13 : (O >= INT_MIN)) (PreH14 : (W >= INT_MIN)) (PreH15 : (len >= INT_MIN)) (PreH16 : (changes_pre >= INT_MIN)) (PreH17 : (p < W)) (PreH18 : (changes_pre = n)) (PreH19 : (len = (Zlength (commands)))) (PreH20 : (W = ((2 * len) + 1))) (PreH21 : (O = len)) (PreH22 : (1 <= len)) (PreH23 : (len <= 100)) (PreH24 : (1 <= changes_pre)) (PreH25 : (changes_pre <= 50)) (PreH26 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH27 : ((0 : Int) <= c)) (PreH28 : (c <= changes_pre)) (PreH29 : ((0 : Int) <= d)) (PreH30 : (d < 2)) (PreH31 : ((0 : Int) <= p)) (PreH32 : (p <= W)) (PreH33 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH34 : ((0 : Int) <= ans)) (PreH35 : (ans <= len)) (PreH36 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH37 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH38 : (dp ≠ (0 : Int))) (PreH39 : (ndp ≠ (0 : Int))) (PreH40 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH41 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH42 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH43 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  (((((c * 2) + d) * ((2 * O) + 1)) + p) < (((n + 1) * 2) * ((2 * O) + 1)))

noncomputable def solver_entail_wit_20_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= (p + 1)) ” &&
  “ ((p + 1) <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + (p + 1))) ” &&
  “ (((((c * 2) + d) * W) + (p + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + (p + 1)) retval) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) (p - O)) ”
  &&  emp
)

noncomputable def solver_entail_wit_20_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) (p - O))

noncomputable def solver_entail_wit_20_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= (p + 1)) ” &&
  “ ((p + 1) <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + (p + 1))) ” &&
  “ (((((c * 2) + d) * W) + (p + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + (p + 1)) retval) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) (-(p - O))) ”
  &&  emp
)

noncomputable def solver_entail_wit_20_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval > ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) (-(p - O)))

noncomputable def solver_entail_wit_20_3 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= (p + 1)) ” &&
  “ ((p + 1) <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + (p + 1))) ” &&
  “ (((((c * 2) + d) * W) + (p + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + (p + 1)) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) ans) ”
  &&  emp
)

noncomputable def solver_entail_wit_20_3_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((0 : Int) <= (p - O))) (PreH3 : (retval = (p - O))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) ans)

noncomputable def solver_entail_wit_20_4 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= (p + 1)) ” &&
  “ ((p + 1) <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + (p + 1))) ” &&
  “ (((((c * 2) + d) * W) + (p + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + (p + 1)) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) ans) ”
  &&  emp
)

noncomputable def solver_entail_wit_20_4_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (retval : Int) (PreH1 : (retval <= ans)) (PreH2 : ((p - O) < (0 : Int))) (PreH3 : (retval = (-(p - O)))) (PreH4 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH5 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH6 : (ans <= INT_MAX)) (PreH7 : (O <= INT_MAX)) (PreH8 : (len <= INT_MAX)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (O >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : (p < W)) (PreH13 : (changes_pre = n)) (PreH14 : (len = (Zlength (commands)))) (PreH15 : (W = ((2 * len) + 1))) (PreH16 : (O = len)) (PreH17 : (1 <= len)) (PreH18 : (len <= 100)) (PreH19 : (1 <= changes_pre)) (PreH20 : (changes_pre <= 50)) (PreH21 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH22 : ((0 : Int) <= c)) (PreH23 : (c <= changes_pre)) (PreH24 : ((0 : Int) <= d)) (PreH25 : (d < 2)) (PreH26 : ((0 : Int) <= p)) (PreH27 : (p <= W)) (PreH28 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH29 : ((0 : Int) <= ans)) (PreH30 : (ans <= len)) (PreH31 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH32 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH33 : (dp ≠ (0 : Int))) (PreH34 : (ndp ≠ (0 : Int))) (PreH35 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH36 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH37 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH38 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH39 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) ≠ (0 : Int))) ,
  (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) ans)

noncomputable def solver_entail_wit_20_5 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) = (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= (p + 1)) ” &&
  “ ((p + 1) <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + (p + 1))) ” &&
  “ (((((c * 2) + d) * W) + (p + 1)) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + (p + 1)) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) = (0 : Int))) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) ans) ”
  &&  emp
)

noncomputable def solver_entail_wit_20_5_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table_2 (0 : Int)) = (0 : Int))) ,
  (TurtleAnswerPrefix commands n ((((c * 2) + d) * ((2 * O) + 1)) + (p + 1)) ans)

noncomputable def solver_entail_wit_21 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (p >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d < 2)) (PreH15 : ((0 : Int) <= p)) (PreH16 : (p <= W)) (PreH17 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= len)) (PreH20 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH21 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH27 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= (d + 1)) ” &&
  “ ((d + 1) <= 2) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre (((c * 2) + (d + 1)) * W) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (p >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d < 2)) (PreH15 : ((0 : Int) <= p)) (PreH16 : (p <= W)) (PreH17 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= len)) (PreH20 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH21 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH27 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n (((c * 2) + (d + 1)) * ((2 * O) + 1)) ans) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_21_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (p >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d < 2)) (PreH15 : ((0 : Int) <= p)) (PreH16 : (p <= W)) (PreH17 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= len)) (PreH20 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH21 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH27 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  (TurtleAnswerPrefix commands n (((c * 2) + (d + 1)) * ((2 * O) + 1)) ans)

noncomputable def solver_entail_wit_21_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (p >= W)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d < 2)) (PreH15 : ((0 : Int) <= p)) (PreH16 : (p <= W)) (PreH17 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH18 : ((0 : Int) <= ans)) (PreH19 : (ans <= len)) (PreH20 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH21 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH22 : (dp ≠ (0 : Int))) (PreH23 : (ndp ≠ (0 : Int))) (PreH24 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH25 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH26 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH27 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_22_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= (changes_pre + 1)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre (((c + 1) * 2) * W) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n (((c + 1) * 2) * ((2 * O) + 1)) ans) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_22_1_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  (TurtleAnswerPrefix commands n (((c + 1) * 2) * ((2 * O) + 1)) ans)

noncomputable def solver_entail_wit_22_1_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (d >= 2)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= changes_pre)) (PreH13 : ((0 : Int) <= d)) (PreH14 : (d <= 2)) (PreH15 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH16 : ((0 : Int) <= ans)) (PreH17 : (ans <= len)) (PreH18 : (dp ≠ (0 : Int))) (PreH19 : (ndp ≠ (0 : Int))) (PreH20 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH21 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH22 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH23 : (TurtleAnswerPrefix commands changes_pre (((c * 2) + d) * W) ans)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_entail_wit_22_2 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) ≠ (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= (changes_pre + 1)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre (((c + 1) * 2) * W) ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) ≠ (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  TT && emp 
|--
  “ (TurtleAnswerPrefix commands n (((c + 1) * 2) * ((2 * O) + 1)) ans) ”
  &&  emp
)

noncomputable def solver_entail_wit_22_2_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((Z.land (changes_pre - c) 1) ≠ (0 : Int))) (PreH2 : (c <= changes_pre)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (changes_pre + 1))) (PreH14 : ((0 : Int) <= ans)) (PreH15 : (ans <= len)) (PreH16 : (dp ≠ (0 : Int))) (PreH17 : (ndp ≠ (0 : Int))) (PreH18 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH20 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH21 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  (TurtleAnswerPrefix commands n (((c + 1) * 2) * ((2 * O) + 1)) ans)

noncomputable def solver_entail_wit_23 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table_2)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table_2)
|--
  EX spare_table : (List Int), EX final_table : (List Int),
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (Spec changes_pre commands ans) ”
  &&  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
) \/
(
forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  TT && emp 
|--
  “ (Spec n commands ans) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ”
  &&  emp
)

noncomputable def solver_entail_wit_23_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  (Spec n commands ans)

noncomputable def solver_entail_wit_23_split_goal_2 : Prop :=
  forall (commands : (List Int)) (n : Int) (changes_pre : Int) (spare_table_2 : (List Int)) (final_table_2 : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (c > changes_pre)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < len)) -> (((Znth k_2 commands (0 : Int)) = 70) ∨ ((Znth k_2 commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= c)) (PreH12 : (c <= (changes_pre + 1))) (PreH13 : ((0 : Int) <= ans)) (PreH14 : (ans <= len)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (final_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table_2)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands len changes_pre final_table_2)) (PreH20 : (TurtleAnswerPrefix commands changes_pre ((c * 2) * W) ans)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (ans : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (Spec changes_pre commands ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (Spec n commands ans) ”
  &&  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (ans : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (Spec changes_pre commands ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
)

noncomputable def solver_return_wit_1_split_goal_spatial : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (ans : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (Spec changes_pre commands ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  (
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (PreH1 : (1 <= (Zlength (commands)))) (PreH2 : ((Zlength (commands)) <= 100)) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (Zlength (commands)))) -> (((Znth i_2 commands (0 : Int)) = 70) ∨ ((Znth i_2 commands (0 : Int)) = 84)))) (PreH6 : (changes_pre = n)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= (Zlength (commands))) ” &&
  “ ((Zlength (commands)) < INT_MAX) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ”
) \/
(
forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (PreH1 : (changes_pre <= INT_MAX)) (PreH2 : (changes_pre >= INT_MIN)) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (Zlength (commands)))) -> (((Znth i_2 commands (0 : Int)) = 70) ∨ ((Znth i_2 commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ”
)

noncomputable def solver_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (PreH1 : (changes_pre <= INT_MAX)) (PreH2 : (changes_pre >= INT_MIN)) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (Zlength (commands)))) -> (((Znth i_2 commands (0 : Int)) = 70) ∨ ((Znth i_2 commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (PreH1 : (1 <= (Zlength (commands)))) (PreH2 : ((Zlength (commands)) <= 100)) (PreH3 : (1 <= n)) (PreH4 : (n <= 50)) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (Zlength (commands)))) -> (((Znth i_2 commands (0 : Int)) = 70) ∨ ((Znth i_2 commands (0 : Int)) = 84)))) (PreH6 : (changes_pre = n)) ,
  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= (Zlength (commands))) ” &&
  “ ((Zlength (commands)) < INT_MAX) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ” &&
  “ (1 <= (Zlength (commands))) ” &&
  “ ((Zlength (commands)) <= 100) ” &&
  “ (1 <= n) ” &&
  “ (n <= 50) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (Zlength (commands)))) -> (((Znth i_2 commands (0 : Int)) = 70) ∨ ((Znth i_2 commands (0 : Int)) = 84))) ” &&
  “ (changes_pre = n) ”
  &&  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux

noncomputable def solver_partial_solve_wit_2_pure : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  ((( &( "dp" ) )) # Ptr |->_)
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) <= INT_MAX) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) = (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ (1 = 1) ”

noncomputable def solver_partial_solve_wit_2_aux : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (PreH1 : (retval = (Zlength (commands)))) (PreH2 : (1 <= (Zlength (commands)))) (PreH3 : ((Zlength (commands)) <= 100)) (PreH4 : (1 <= n)) (PreH5 : (n <= 50)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH7 : (changes_pre = n)) ,
  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) <= INT_MAX) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) = (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ (1 = 1) ” &&
  “ (retval = (Zlength (commands))) ” &&
  “ (1 <= (Zlength (commands))) ” &&
  “ ((Zlength (commands)) <= 100) ” &&
  “ (1 <= n) ” &&
  “ (n <= 50) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ” &&
  “ (changes_pre = n) ”
  &&  (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_2 : Prop := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux

noncomputable def solver_partial_solve_wit_3_pure : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval = (Zlength (commands)))) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  ((( &( "ndp" ) )) # Ptr |->_)
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** ((( &( "dp" ) )) # Ptr |-> (retval_2))
  ** ((( &( "O" ) )) # Int |-> (retval))
  ** ((( &( "W" ) )) # Int |-> (((2 * retval) + 1)))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "len" ) )) # Int |-> (retval))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
|--
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) <= INT_MAX) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) = (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ (1 = 1) ”

noncomputable def solver_partial_solve_wit_3_aux : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 ≠ (0 : Int))) (PreH2 : (retval = (Zlength (commands)))) (PreH3 : (1 <= (Zlength (commands)))) (PreH4 : ((Zlength (commands)) <= 100)) (PreH5 : (1 <= n)) (PreH6 : (n <= 50)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH8 : (changes_pre = n)) ,
  (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) <= INT_MAX) ” &&
  “ ((((changes_pre + 1) * 2) * ((2 * retval) + 1)) = (((changes_pre + 1) * 2) * ((2 * retval) + 1))) ” &&
  “ (1 = 1) ” &&
  “ (retval_2 ≠ (0 : Int)) ” &&
  “ (retval = (Zlength (commands))) ” &&
  “ (1 <= (Zlength (commands))) ” &&
  “ ((Zlength (commands)) <= 100) ” &&
  “ (1 <= n) ” &&
  “ (n <= 50) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ” &&
  “ (changes_pre = n) ”
  &&  (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_3 : Prop := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 ≠ (0 : Int))) (PreH2 : (retval_2 ≠ (0 : Int))) (PreH3 : (retval = (Zlength (commands)))) (PreH4 : (1 <= (Zlength (commands)))) (PreH5 : ((Zlength (commands)) <= 100)) (PreH6 : (1 <= n)) (PreH7 : (n <= 50)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84)))) (PreH9 : (changes_pre = n)) ,
  (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (ucharArray.full retval_2 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (retval_3 ≠ (0 : Int)) ” &&
  “ (retval_2 ≠ (0 : Int)) ” &&
  “ (retval = (Zlength (commands))) ” &&
  “ (1 <= (Zlength (commands))) ” &&
  “ ((Zlength (commands)) <= 100) ” &&
  “ (1 <= n) ” &&
  “ (n <= 50) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (commands)))) -> (((Znth i commands (0 : Int)) = 70) ∨ ((Znth i commands (0 : Int)) = 84))) ” &&
  “ (changes_pre = n) ”
  &&  (((retval_2 + ((((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i retval_2 (((((0 : Int) * 2) + (0 : Int)) * ((2 * retval) + 1)) + retval) (0 : Int) (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (ucharArray.full retval_3 (((changes_pre + 1) * 2) * ((2 * retval) + 1)) (repeat_Z ((0 : Int)) ((((changes_pre + 1) * 2) * ((2 * retval) + 1)))))
  ** (charArray.full s_pre ((Zlength (commands)) + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_5_pure : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i < len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ”

noncomputable def solver_partial_solve_wit_5_aux : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : (i < len)) (PreH2 : (changes_pre = n)) (PreH3 : (len = (Zlength (commands)))) (PreH4 : (W = ((2 * len) + 1))) (PreH5 : (O = len)) (PreH6 : (1 <= len)) (PreH7 : (len <= 100)) (PreH8 : (1 <= changes_pre)) (PreH9 : (changes_pre <= 50)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= len)) (PreH13 : ((0 : Int) <= (((changes_pre + 1) * 2) * W))) (PreH14 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH15 : (dp ≠ (0 : Int))) (PreH16 : (ndp ≠ (0 : Int))) (PreH17 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH18 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH19 : (TurtleLayerMeaning commands i changes_pre current_table)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (i < len) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= len) ” &&
  “ ((0 : Int) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ”
  &&  (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_5 : Prop := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (current_table : (List Int)) (ndp : Int) (dp : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH2 : (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (i <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (pos < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < len)) (PreH21 : ((0 : Int) <= c)) (PreH22 : (c <= changes_pre)) (PreH23 : ((0 : Int) <= dir)) (PreH24 : (dir < 2)) (PreH25 : ((0 : Int) <= pos)) (PreH26 : (pos <= W)) (PreH27 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH28 : ((0 : Int) <= ((((c * 2) + dir) * W) + pos))) (PreH29 : (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH35 : (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + pos)) ” &&
  “ (((((c * 2) + dir) * W) + pos) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (pos < W) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= W) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((((c * 2) + dir) * W) + pos)) ” &&
  “ (((((c * 2) + dir) * W) + pos) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre (2 * ((((c * 2) + dir) * W) + pos)) next_table) ”
  &&  (((dp + (((((c * 2) + dir) * W) + pos) * sizeof(UCHAR)))) # UChar |-> ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int))))
  ** (ucharArray.missing_i dp ((((c * 2) + dir) * W) + pos) (0 : Int) (((changes_pre + 1) * 2) * W) current_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((c + flip) <= changes_pre)) (PreH2 : (flip <= 1)) (PreH3 : (changes_pre = n)) (PreH4 : (len = (Zlength (commands)))) (PreH5 : (W = ((2 * len) + 1))) (PreH6 : (O = len)) (PreH7 : (1 <= len)) (PreH8 : (len <= 100)) (PreH9 : (1 <= changes_pre)) (PreH10 : (changes_pre <= 50)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < len)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= changes_pre)) (PreH16 : ((0 : Int) <= dir)) (PreH17 : (dir < 2)) (PreH18 : ((0 : Int) <= pos)) (PreH19 : (pos < W)) (PreH20 : ((0 : Int) <= flip)) (PreH21 : (flip <= 2)) (PreH22 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH23 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH24 : (dp ≠ (0 : Int))) (PreH25 : (ndp ≠ (0 : Int))) (PreH26 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH27 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH28 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH29 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) ” &&
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (pos < W) ” &&
  “ (pos >= (0 : Int)) ” &&
  “ ((0 : Int) <= (Z.lxor dir 1)) ” &&
  “ ((Z.lxor dir 1) < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  (((ndp + ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ndp (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) (0 : Int) (((changes_pre + 1) * 2) * W) next_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos))) (PreH2 : ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W))) (PreH3 : (pos < W)) (PreH4 : (pos >= (0 : Int))) (PreH5 : ((0 : Int) <= (Z.lxor dir 1))) (PreH6 : ((Z.lxor dir 1) < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (dir <= INT_MAX)) (PreH9 : (c <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (O <= INT_MAX)) (PreH12 : (W <= INT_MAX)) (PreH13 : (len <= INT_MAX)) (PreH14 : (changes_pre <= INT_MAX)) (PreH15 : (pos <= INT_MAX)) (PreH16 : (flip >= INT_MIN)) (PreH17 : (dir >= INT_MIN)) (PreH18 : (c >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (O >= INT_MIN)) (PreH21 : (W >= INT_MIN)) (PreH22 : (len >= INT_MIN)) (PreH23 : (changes_pre >= INT_MIN)) (PreH24 : (pos >= INT_MIN)) (PreH25 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH26 : ((c + flip) <= changes_pre)) (PreH27 : (flip <= 1)) (PreH28 : (changes_pre = n)) (PreH29 : (len = (Zlength (commands)))) (PreH30 : (W = ((2 * len) + 1))) (PreH31 : (O = len)) (PreH32 : (1 <= len)) (PreH33 : (len <= 100)) (PreH34 : (1 <= changes_pre)) (PreH35 : (changes_pre <= 50)) (PreH36 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH37 : ((0 : Int) <= i)) (PreH38 : (i < len)) (PreH39 : ((0 : Int) <= c)) (PreH40 : (c <= changes_pre)) (PreH41 : ((0 : Int) <= dir)) (PreH42 : (dir < 2)) (PreH43 : ((0 : Int) <= pos)) (PreH44 : (pos < W)) (PreH45 : ((0 : Int) <= flip)) (PreH46 : (flip <= 2)) (PreH47 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH48 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH49 : (dp ≠ (0 : Int))) (PreH50 : (ndp ≠ (0 : Int))) (PreH51 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH52 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH53 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH54 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH55 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos)) ” &&
  “ ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (pos < W) ” &&
  “ (pos >= (0 : Int)) ” &&
  “ ((0 : Int) <= (Z.lxor dir 1)) ” &&
  “ ((Z.lxor dir 1) < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  (((ndp + ((((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ndp (((((c + flip) * 2) + (Z.lxor dir 1)) * W) + pos) (0 : Int) (((changes_pre + 1) * 2) * W) next_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1)))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + (-1)) < W) ” &&
  “ ((pos + (-1)) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + (-1)) >= INT_MIN) ” &&
  “ (dir ≠ (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  (((ndp + ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ndp (((((c + flip) * 2) + dir) * W) + (pos + (-1))) (0 : Int) (((changes_pre + 1) * 2) * W) next_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip ≠ (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + 1) < W) ” &&
  “ ((pos + 1) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + 1) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + 1) >= INT_MIN) ” &&
  “ (dir = (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip ≠ (0 : Int)) ”
  &&  (((ndp + ((((((c + flip) * 2) + dir) * W) + (pos + 1)) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ndp (((((c + flip) * 2) + dir) * W) + (pos + 1)) (0 : Int) (((changes_pre + 1) * 2) * W) next_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1))))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + (-1)) < W)) (PreH4 : ((pos + (-1)) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + (-1)) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + (-1)) >= INT_MIN)) (PreH27 : (dir ≠ (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + (-1)))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + (-1)) < W) ” &&
  “ ((pos + (-1)) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + (-1)) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + (-1)) >= INT_MIN) ” &&
  “ (dir ≠ (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  (((ndp + ((((((c + flip) * 2) + dir) * W) + (pos + (-1))) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ndp (((((c + flip) * 2) + dir) * W) + (pos + (-1))) (0 : Int) (((changes_pre + 1) * 2) * W) next_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (next_table : (List Int)) (ndp : Int) (dp : Int) (current_table : (List Int)) (flip : Int) (pos : Int) (dir : Int) (c : Int) (i : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1)))) (PreH2 : ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W))) (PreH3 : ((pos + 1) < W)) (PreH4 : ((pos + 1) >= (0 : Int))) (PreH5 : ((0 : Int) <= dir)) (PreH6 : (dir < 2)) (PreH7 : (flip <= INT_MAX)) (PreH8 : (pos <= INT_MAX)) (PreH9 : (dir <= INT_MAX)) (PreH10 : (c <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (O <= INT_MAX)) (PreH13 : (W <= INT_MAX)) (PreH14 : (len <= INT_MAX)) (PreH15 : (changes_pre <= INT_MAX)) (PreH16 : ((pos + 1) <= INT_MAX)) (PreH17 : (flip >= INT_MIN)) (PreH18 : (pos >= INT_MIN)) (PreH19 : (dir >= INT_MIN)) (PreH20 : (c >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (O >= INT_MIN)) (PreH23 : (W >= INT_MIN)) (PreH24 : (len >= INT_MIN)) (PreH25 : (changes_pre >= INT_MIN)) (PreH26 : ((pos + 1) >= INT_MIN)) (PreH27 : (dir = (0 : Int))) (PreH28 : ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84)) (PreH29 : ((c + flip) <= changes_pre)) (PreH30 : (flip <= 1)) (PreH31 : (changes_pre = n)) (PreH32 : (len = (Zlength (commands)))) (PreH33 : (W = ((2 * len) + 1))) (PreH34 : (O = len)) (PreH35 : (1 <= len)) (PreH36 : (len <= 100)) (PreH37 : (1 <= changes_pre)) (PreH38 : (changes_pre <= 50)) (PreH39 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH40 : ((0 : Int) <= i)) (PreH41 : (i < len)) (PreH42 : ((0 : Int) <= c)) (PreH43 : (c <= changes_pre)) (PreH44 : ((0 : Int) <= dir)) (PreH45 : (dir < 2)) (PreH46 : ((0 : Int) <= pos)) (PreH47 : (pos < W)) (PreH48 : ((0 : Int) <= flip)) (PreH49 : (flip <= 2)) (PreH50 : ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int))) (PreH51 : ((((changes_pre + 1) * 2) * W) <= INT_MAX)) (PreH52 : (dp ≠ (0 : Int))) (PreH53 : (ndp ≠ (0 : Int))) (PreH54 : ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W))) (PreH55 : ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W))) (PreH56 : (TurtleLayerMeaning commands i changes_pre current_table)) (PreH57 : (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table)) (PreH58 : (flip = (0 : Int))) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) next_table)
|--
  “ ((0 : Int) <= (((((c + flip) * 2) + dir) * W) + (pos + 1))) ” &&
  “ ((((((c + flip) * 2) + dir) * W) + (pos + 1)) < (((changes_pre + 1) * 2) * W)) ” &&
  “ ((pos + 1) < W) ” &&
  “ ((pos + 1) >= (0 : Int)) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ (flip <= INT_MAX) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (dir <= INT_MAX) ” &&
  “ (c <= INT_MAX) ” &&
  “ (i <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (W <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (changes_pre <= INT_MAX) ” &&
  “ ((pos + 1) <= INT_MAX) ” &&
  “ (flip >= INT_MIN) ” &&
  “ (pos >= INT_MIN) ” &&
  “ (dir >= INT_MIN) ” &&
  “ (c >= INT_MIN) ” &&
  “ (i >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (W >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (changes_pre >= INT_MIN) ” &&
  “ ((pos + 1) >= INT_MIN) ” &&
  “ (dir = (0 : Int)) ” &&
  “ ((Znth i (commands ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ 84) ” &&
  “ ((c + flip) <= changes_pre) ” &&
  “ (flip <= 1) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < len) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= dir) ” &&
  “ (dir < 2) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos < W) ” &&
  “ ((0 : Int) <= flip) ” &&
  “ (flip <= 2) ” &&
  “ ((Znth ((((c * 2) + dir) * W) + pos) current_table (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((((changes_pre + 1) * 2) * W) <= INT_MAX) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (current_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (next_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands i changes_pre current_table) ” &&
  “ (TurtleNextPrefix commands i changes_pre ((2 * ((((c * 2) + dir) * W) + pos)) + flip) next_table) ” &&
  “ (flip = (0 : Int)) ”
  &&  (((ndp + ((((((c + flip) * 2) + dir) * W) + (pos + 1)) * sizeof(UCHAR)))) # UChar |->_)
  ** (ucharArray.missing_i ndp (((((c + flip) * 2) + dir) * W) + (pos + 1)) (0 : Int) (((changes_pre + 1) * 2) * W) next_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) current_table)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ ((0 : Int) <= ((((c * 2) + d) * W) + p)) ” &&
  “ (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (p < W) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + p)) ” &&
  “ (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans) ”
  &&  (((dp + (((((c * 2) + d) * W) + p) * sizeof(UCHAR)))) # UChar |-> ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int))))
  ** (ucharArray.missing_i dp ((((c * 2) + d) * W) + p) (0 : Int) (((changes_pre + 1) * 2) * W) final_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)

noncomputable def solver_partial_solve_wit_15_pure : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int |->_)
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "d" ) )) # Int |-> (d))
  ** ((( &( "W" ) )) # Int |-> (W))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** ((( &( "changes" ) )) # Int |-> (changes_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "O" ) )) # Int |-> (O))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "dp" ) )) # Ptr |-> (dp))
  ** ((( &( "ndp" ) )) # Ptr |-> (ndp))
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (INT_MIN < (p - O)) ” &&
  “ ((p - O) <= INT_MAX) ”

noncomputable def solver_partial_solve_wit_15_aux : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (spare_table : (List Int)) (final_table : (List Int)) (ndp : Int) (dp : Int) (ans : Int) (p : Int) (d : Int) (c : Int) (O : Int) (W : Int) (len : Int) (PreH1 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH2 : (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W))) (PreH3 : (ans <= INT_MAX)) (PreH4 : (O <= INT_MAX)) (PreH5 : (len <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (O >= INT_MIN)) (PreH8 : (len >= INT_MIN)) (PreH9 : (p < W)) (PreH10 : (changes_pre = n)) (PreH11 : (len = (Zlength (commands)))) (PreH12 : (W = ((2 * len) + 1))) (PreH13 : (O = len)) (PreH14 : (1 <= len)) (PreH15 : (len <= 100)) (PreH16 : (1 <= changes_pre)) (PreH17 : (changes_pre <= 50)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c <= changes_pre)) (PreH21 : ((0 : Int) <= d)) (PreH22 : (d < 2)) (PreH23 : ((0 : Int) <= p)) (PreH24 : (p <= W)) (PreH25 : ((Z.land (changes_pre - c) 1) = (0 : Int))) (PreH26 : ((0 : Int) <= ans)) (PreH27 : (ans <= len)) (PreH28 : ((0 : Int) <= ((((c * 2) + d) * W) + p))) (PreH29 : (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W))) (PreH30 : (dp ≠ (0 : Int))) (PreH31 : (ndp ≠ (0 : Int))) (PreH32 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH33 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH34 : (TurtleLayerMeaning commands len changes_pre final_table)) (PreH35 : (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans)) (PreH36 : ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int))) ,
  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (INT_MIN < (p - O)) ” &&
  “ ((p - O) <= INT_MAX) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + p)) ” &&
  “ (((((c * 2) + d) * W) + p) < (((changes_pre + 1) * 2) * W)) ” &&
  “ (ans <= INT_MAX) ” &&
  “ (O <= INT_MAX) ” &&
  “ (len <= INT_MAX) ” &&
  “ (ans >= INT_MIN) ” &&
  “ (O >= INT_MIN) ” &&
  “ (len >= INT_MIN) ” &&
  “ (p < W) ” &&
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= changes_pre) ” &&
  “ ((0 : Int) <= d) ” &&
  “ (d < 2) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= W) ” &&
  “ ((Z.land (changes_pre - c) 1) = (0 : Int)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ ((0 : Int) <= ((((c * 2) + d) * W) + p)) ” &&
  “ (((((c * 2) + d) * W) + p) <= (((changes_pre + 1) * 2) * W)) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (TurtleLayerMeaning commands len changes_pre final_table) ” &&
  “ (TurtleAnswerPrefix commands changes_pre ((((c * 2) + d) * W) + p) ans) ” &&
  “ ((Znth ((((c * 2) + d) * W) + p) final_table (0 : Int)) ≠ (0 : Int)) ”
  &&  (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)

noncomputable def solver_partial_solve_wit_15 : Prop := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (ans : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (Spec changes_pre commands ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full dp (((changes_pre + 1) * 2) * W) final_table)
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (Spec changes_pre commands ans) ”
  &&  (ucharArray.full dp (((n + 1) * 2) * ((2 * len) + 1)) final_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)

noncomputable def solver_partial_solve_wit_17 : Prop :=
  forall (commands : (List Int)) (n : Int) (s_pre : Int) (changes_pre : Int) (final_table : (List Int)) (spare_table : (List Int)) (len : Int) (W : Int) (O : Int) (ans : Int) (dp : Int) (ndp : Int) (PreH1 : (changes_pre = n)) (PreH2 : (len = (Zlength (commands)))) (PreH3 : (W = ((2 * len) + 1))) (PreH4 : (O = len)) (PreH5 : (1 <= len)) (PreH6 : (len <= 100)) (PreH7 : (1 <= changes_pre)) (PreH8 : (changes_pre <= 50)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84)))) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= len)) (PreH12 : (dp ≠ (0 : Int))) (PreH13 : (ndp ≠ (0 : Int))) (PreH14 : ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W))) (PreH15 : ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W))) (PreH16 : (Spec changes_pre commands ans)) ,
  (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))
  ** (ucharArray.full ndp (((changes_pre + 1) * 2) * W) spare_table)
|--
  “ (changes_pre = n) ” &&
  “ (len = (Zlength (commands))) ” &&
  “ (W = ((2 * len) + 1)) ” &&
  “ (O = len) ” &&
  “ (1 <= len) ” &&
  “ (len <= 100) ” &&
  “ (1 <= changes_pre) ” &&
  “ (changes_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < len)) -> (((Znth k commands (0 : Int)) = 70) ∨ ((Znth k commands (0 : Int)) = 84))) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= len) ” &&
  “ (dp ≠ (0 : Int)) ” &&
  “ (ndp ≠ (0 : Int)) ” &&
  “ ((Zlength (final_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ ((Zlength (spare_table)) = (((changes_pre + 1) * 2) * W)) ” &&
  “ (Spec changes_pre commands ans) ”
  &&  (ucharArray.full ndp (((n + 1) * 2) * ((2 * len) + 1)) spare_table)
  ** (charArray.full s_pre (len + 1) (commands ++ ((0 : Int) :: (@List.nil Int))))


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_safety_wit_21 : solver_safety_wit_21
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_23 : solver_safety_wit_23
  proof_of_solver_safety_wit_24 : solver_safety_wit_24
  proof_of_solver_safety_wit_25 : solver_safety_wit_25
  proof_of_solver_safety_wit_26 : solver_safety_wit_26
  proof_of_solver_safety_wit_27 : solver_safety_wit_27
  proof_of_solver_safety_wit_28 : solver_safety_wit_28
  proof_of_solver_safety_wit_29 : solver_safety_wit_29
  proof_of_solver_safety_wit_30 : solver_safety_wit_30
  proof_of_solver_safety_wit_31 : solver_safety_wit_31
  proof_of_solver_safety_wit_32 : solver_safety_wit_32
  proof_of_solver_safety_wit_33 : solver_safety_wit_33
  proof_of_solver_safety_wit_34 : solver_safety_wit_34
  proof_of_solver_safety_wit_35 : solver_safety_wit_35
  proof_of_solver_safety_wit_36 : solver_safety_wit_36
  proof_of_solver_safety_wit_37 : solver_safety_wit_37
  proof_of_solver_safety_wit_38 : solver_safety_wit_38
  proof_of_solver_safety_wit_39 : solver_safety_wit_39
  proof_of_solver_safety_wit_40 : solver_safety_wit_40
  proof_of_solver_safety_wit_41 : solver_safety_wit_41
  proof_of_solver_safety_wit_42 : solver_safety_wit_42
  proof_of_solver_safety_wit_43 : solver_safety_wit_43
  proof_of_solver_safety_wit_44 : solver_safety_wit_44
  proof_of_solver_safety_wit_45 : solver_safety_wit_45
  proof_of_solver_safety_wit_46 : solver_safety_wit_46
  proof_of_solver_safety_wit_47 : solver_safety_wit_47
  proof_of_solver_safety_wit_48 : solver_safety_wit_48
  proof_of_solver_safety_wit_49 : solver_safety_wit_49
  proof_of_solver_safety_wit_50 : solver_safety_wit_50
  proof_of_solver_safety_wit_51 : solver_safety_wit_51
  proof_of_solver_safety_wit_52 : solver_safety_wit_52
  proof_of_solver_safety_wit_53 : solver_safety_wit_53
  proof_of_solver_safety_wit_54 : solver_safety_wit_54
  proof_of_solver_safety_wit_55 : solver_safety_wit_55
  proof_of_solver_safety_wit_56 : solver_safety_wit_56
  proof_of_solver_safety_wit_57 : solver_safety_wit_57
  proof_of_solver_safety_wit_58 : solver_safety_wit_58
  proof_of_solver_safety_wit_59 : solver_safety_wit_59
  proof_of_solver_safety_wit_60 : solver_safety_wit_60
  proof_of_solver_safety_wit_61 : solver_safety_wit_61
  proof_of_solver_safety_wit_62 : solver_safety_wit_62
  proof_of_solver_safety_wit_63 : solver_safety_wit_63
  proof_of_solver_safety_wit_64 : solver_safety_wit_64
  proof_of_solver_safety_wit_65 : solver_safety_wit_65
  proof_of_solver_safety_wit_66 : solver_safety_wit_66
  proof_of_solver_safety_wit_67 : solver_safety_wit_67
  proof_of_solver_safety_wit_68 : solver_safety_wit_68
  proof_of_solver_safety_wit_69 : solver_safety_wit_69
  proof_of_solver_safety_wit_70 : solver_safety_wit_70
  proof_of_solver_safety_wit_71 : solver_safety_wit_71
  proof_of_solver_safety_wit_72 : solver_safety_wit_72
  proof_of_solver_safety_wit_73 : solver_safety_wit_73
  proof_of_solver_safety_wit_74 : solver_safety_wit_74
  proof_of_solver_safety_wit_75 : solver_safety_wit_75
  proof_of_solver_safety_wit_76 : solver_safety_wit_76
  proof_of_solver_safety_wit_77 : solver_safety_wit_77
  proof_of_solver_safety_wit_78 : solver_safety_wit_78
  proof_of_solver_safety_wit_79 : solver_safety_wit_79
  proof_of_solver_safety_wit_80 : solver_safety_wit_80
  proof_of_solver_safety_wit_81 : solver_safety_wit_81
  proof_of_solver_safety_wit_82 : solver_safety_wit_82
  proof_of_solver_safety_wit_83 : solver_safety_wit_83
  proof_of_solver_safety_wit_84 : solver_safety_wit_84
  proof_of_solver_safety_wit_85 : solver_safety_wit_85
  proof_of_solver_safety_wit_86 : solver_safety_wit_86
  proof_of_solver_safety_wit_87 : solver_safety_wit_87
  proof_of_solver_safety_wit_88 : solver_safety_wit_88
  proof_of_solver_safety_wit_89 : solver_safety_wit_89
  proof_of_solver_safety_wit_90 : solver_safety_wit_90
  proof_of_solver_safety_wit_91 : solver_safety_wit_91
  proof_of_solver_safety_wit_92 : solver_safety_wit_92
  proof_of_solver_safety_wit_93 : solver_safety_wit_93
  proof_of_solver_safety_wit_94 : solver_safety_wit_94
  proof_of_solver_safety_wit_95 : solver_safety_wit_95
  proof_of_solver_safety_wit_96 : solver_safety_wit_96
  proof_of_solver_safety_wit_97 : solver_safety_wit_97
  proof_of_solver_safety_wit_98 : solver_safety_wit_98
  proof_of_solver_safety_wit_99 : solver_safety_wit_99
  proof_of_solver_safety_wit_100 : solver_safety_wit_100
  proof_of_solver_safety_wit_101 : solver_safety_wit_101
  proof_of_solver_safety_wit_102 : solver_safety_wit_102
  proof_of_solver_safety_wit_103 : solver_safety_wit_103
  proof_of_solver_safety_wit_104 : solver_safety_wit_104
  proof_of_solver_safety_wit_105 : solver_safety_wit_105
  proof_of_solver_safety_wit_106 : solver_safety_wit_106
  proof_of_solver_safety_wit_107 : solver_safety_wit_107
  proof_of_solver_safety_wit_108 : solver_safety_wit_108
  proof_of_solver_safety_wit_109 : solver_safety_wit_109
  proof_of_solver_safety_wit_110 : solver_safety_wit_110
  proof_of_solver_safety_wit_111 : solver_safety_wit_111
  proof_of_solver_safety_wit_112 : solver_safety_wit_112
  proof_of_solver_safety_wit_113 : solver_safety_wit_113
  proof_of_solver_safety_wit_114 : solver_safety_wit_114
  proof_of_solver_safety_wit_115 : solver_safety_wit_115
  proof_of_solver_safety_wit_116 : solver_safety_wit_116
  proof_of_solver_safety_wit_117 : solver_safety_wit_117
  proof_of_solver_safety_wit_118 : solver_safety_wit_118
  proof_of_solver_safety_wit_119 : solver_safety_wit_119
  proof_of_solver_safety_wit_120 : solver_safety_wit_120
  proof_of_solver_safety_wit_121 : solver_safety_wit_121
  proof_of_solver_safety_wit_122 : solver_safety_wit_122
  proof_of_solver_safety_wit_123 : solver_safety_wit_123
  proof_of_solver_safety_wit_124 : solver_safety_wit_124
  proof_of_solver_safety_wit_125 : solver_safety_wit_125
  proof_of_solver_safety_wit_126 : solver_safety_wit_126
  proof_of_solver_safety_wit_127 : solver_safety_wit_127
  proof_of_solver_safety_wit_128 : solver_safety_wit_128
  proof_of_solver_safety_wit_129 : solver_safety_wit_129
  proof_of_solver_safety_wit_130 : solver_safety_wit_130
  proof_of_solver_safety_wit_131 : solver_safety_wit_131
  proof_of_solver_safety_wit_132 : solver_safety_wit_132
  proof_of_solver_safety_wit_133 : solver_safety_wit_133
  proof_of_solver_safety_wit_134 : solver_safety_wit_134
  proof_of_solver_safety_wit_135 : solver_safety_wit_135
  proof_of_solver_safety_wit_136 : solver_safety_wit_136
  proof_of_solver_safety_wit_137 : solver_safety_wit_137
  proof_of_solver_safety_wit_138 : solver_safety_wit_138
  proof_of_solver_safety_wit_139 : solver_safety_wit_139
  proof_of_solver_safety_wit_140 : solver_safety_wit_140
  proof_of_solver_safety_wit_141 : solver_safety_wit_141
  proof_of_solver_safety_wit_142 : solver_safety_wit_142
  proof_of_solver_safety_wit_143 : solver_safety_wit_143
  proof_of_solver_safety_wit_144 : solver_safety_wit_144
  proof_of_solver_safety_wit_145 : solver_safety_wit_145
  proof_of_solver_safety_wit_146 : solver_safety_wit_146
  proof_of_solver_safety_wit_147 : solver_safety_wit_147
  proof_of_solver_safety_wit_148 : solver_safety_wit_148
  proof_of_solver_safety_wit_149 : solver_safety_wit_149
  proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3
  proof_of_solver_entail_wit_7_4 : solver_entail_wit_7_4
  proof_of_solver_entail_wit_7_5 : solver_entail_wit_7_5
  proof_of_solver_entail_wit_7_6 : solver_entail_wit_7_6
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8
  proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9
  proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10
  proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11
  proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1
  proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2
  proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1
  proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2
  proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3
  proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4
  proof_of_solver_entail_wit_8_5 : solver_entail_wit_8_5
  proof_of_solver_entail_wit_8_6 : solver_entail_wit_8_6
  proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1
  proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2
  proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3
  proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4
  proof_of_solver_entail_wit_9_5 : solver_entail_wit_9_5
  proof_of_solver_entail_wit_9_6 : solver_entail_wit_9_6
  proof_of_solver_entail_wit_9_7 : solver_entail_wit_9_7
  proof_of_solver_entail_wit_9_8 : solver_entail_wit_9_8
  proof_of_solver_entail_wit_9_9 : solver_entail_wit_9_9
  proof_of_solver_entail_wit_9_10 : solver_entail_wit_9_10
  proof_of_solver_entail_wit_9_11 : solver_entail_wit_9_11
  proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1
  proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2
  proof_of_solver_entail_wit_11 : solver_entail_wit_11
  proof_of_solver_entail_wit_12 : solver_entail_wit_12
  proof_of_solver_entail_wit_13 : solver_entail_wit_13
  proof_of_solver_entail_wit_14 : solver_entail_wit_14
  proof_of_solver_entail_wit_15 : solver_entail_wit_15
  proof_of_solver_entail_wit_16 : solver_entail_wit_16
  proof_of_solver_entail_wit_17 : solver_entail_wit_17
  proof_of_solver_entail_wit_18 : solver_entail_wit_18
  proof_of_solver_entail_wit_19 : solver_entail_wit_19
  proof_of_solver_entail_wit_20_1 : solver_entail_wit_20_1
  proof_of_solver_entail_wit_20_2 : solver_entail_wit_20_2
  proof_of_solver_entail_wit_20_3 : solver_entail_wit_20_3
  proof_of_solver_entail_wit_20_4 : solver_entail_wit_20_4
  proof_of_solver_entail_wit_20_5 : solver_entail_wit_20_5
  proof_of_solver_entail_wit_21 : solver_entail_wit_21
  proof_of_solver_entail_wit_22_1 : solver_entail_wit_22_1
  proof_of_solver_entail_wit_22_2 : solver_entail_wit_22_2
  proof_of_solver_entail_wit_23 : solver_entail_wit_23
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_goal
