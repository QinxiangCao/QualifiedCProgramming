import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P024_1104B_game_with_string_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  ((( &( "moves" ) )) # Int |->_)
  ** ((( &( "top" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_full ( &( "stack" ) ) 100005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  ((( &( "top" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_full ( &( "stack" ) ) 100005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "moves" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "top" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_full ( &( "stack" ) ) 100005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top ≠ (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "moves" ) )) # Int |-> (moves))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ ((top - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top - 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top ≠ (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "moves" ) )) # Int |-> (moves))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) = (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "moves" ) )) # Int |-> (moves))
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ ((top - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top - 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) = (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top - 1)))
  ** ((( &( "moves" ) )) # Int |-> (moves))
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ ((moves + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (moves + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) (top + 1) (reduced ++ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "moves" ) )) # Int |-> (moves))
|--
  “ ((top + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top + 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) (top + 1) (reduced ++ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "moves" ) )) # Int |-> (moves))
|--
  “ ((top + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top + 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) = (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top - 1)))
  ** ((( &( "moves" ) )) # Int |-> ((moves + 1)))
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) (top + 1) (reduced ++ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top + 1)))
  ** ((( &( "moves" ) )) # Int |-> (moves))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) (top + 1) (reduced ++ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top + 1)))
  ** ((( &( "moves" ) )) # Int |-> (moves))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : ((0 : Int) <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : ((0 : Int) <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves)))) (PreH12 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH13 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "moves" ) )) # Int |-> (moves))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_full ( &( "stack" ) ) 100005)
|--
  EX reduced : (List Int),
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (text))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) = ((0 : Int) + (2 * (0 : Int)))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) ((0 : Int)) (text)) reduced (0 : Int)) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) (0 : Int) reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) (0 : Int) 100005)
) \/
(
forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  TT && emp 
|--
  “ (PrefixGameState (sublist ((0 : Int)) ((0 : Int)) (text)) (@List.nil Int) (0 : Int)) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  (PrefixGameState (sublist ((0 : Int)) ((0 : Int)) (text)) (@List.nil Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  ((0 : Int) = (Zlength ((@List.nil Int))))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (text : (List Int)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (text)))) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) = (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced_2)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  EX reduced : (List Int),
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= (i + 1)) ” &&
  “ ((top - 1) = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= (moves + 1)) ” &&
  “ ((moves + 1) <= (i + 1)) ” &&
  “ ((i + 1) = ((top - 1) + (2 * (moves + 1)))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) ((i + 1)) (text)) reduced (moves + 1)) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) (top - 1) reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) (top - 1) 100005)
) \/
(
forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) = (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) top reduced_2)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  EX reduced : (List Int),
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= (i + 1)) ” &&
  “ ((top - 1) = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= (moves + 1)) ” &&
  “ ((moves + 1) <= (i + 1)) ” &&
  “ ((i + 1) = ((top - 1) + (2 * (moves + 1)))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) ((i + 1)) (text)) reduced (moves + 1)) ”
  &&  (charArray.full ( &( "stack" ) ) (top - 1) reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) (top - 1) 100005)
)

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) (top + 1) (reduced_2 ++ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX reduced : (List Int),
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= (i + 1)) ” &&
  “ ((top + 1) = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= (i + 1)) ” &&
  “ ((i + 1) = ((top + 1) + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) ((i + 1)) (text)) reduced moves) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) (top + 1) reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
) \/
(
forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (PrefixGameState (sublist ((0 : Int)) (((top + (2 * moves)) + 1)) (text)) (reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))) moves) ” &&
  “ (((0 : Int) + 1) = (Zlength ((reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int)))))) ” &&
  “ (((top + (2 * moves)) + 1) <= (Zlength (text))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (PrefixGameState (sublist ((0 : Int)) (((top + (2 * moves)) + 1)) (text)) (reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))) moves)

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (((0 : Int) + 1) = (Zlength ((reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))))

noncomputable def solver_entail_wit_2_2_split_goal_3 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (((top + (2 * moves)) + 1) <= (Zlength (text)))

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) (top + 1) (reduced_2 ++ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX reduced : (List Int),
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (text))) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= (i + 1)) ” &&
  “ ((top + 1) = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= (i + 1)) ” &&
  “ ((i + 1) = ((top + 1) + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) ((i + 1)) (text)) reduced moves) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) (top + 1) reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
) \/
(
forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (PrefixGameState (sublist ((0 : Int)) (((top + (2 * moves)) + 1)) (text)) (reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))) moves) ” &&
  “ ((top + 1) = (Zlength ((reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int)))))) ” &&
  “ (((top + (2 * moves)) + 1) <= (Zlength (text))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (PrefixGameState (sublist ((0 : Int)) (((top + (2 * moves)) + 1)) (text)) (reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))) moves)

noncomputable def solver_entail_wit_2_3_split_goal_2 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  ((top + 1) = (Zlength ((reduced_2 ++ ((Znth (top + (2 * moves)) (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) :: (@List.nil Int))))))

noncomputable def solver_entail_wit_2_3_split_goal_3 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced_2 (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced_2 moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (((top + (2 * moves)) + 1) <= (Zlength (text)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : ((0 : Int) <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : ((0 : Int) <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves)))) (PreH12 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH13 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (Spec text (Z.land moves 1)) ”
  &&  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_full ( &( "stack" ) ) 100005)
) \/
(
forall (text : (List Int)) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : ((0 : Int) <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : ((0 : Int) <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves)))) (PreH12 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH13 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (Spec text (Z.land moves 1)) ”
  &&  (charArray.undef_full ( &( "stack" ) ) 100005)
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : ((0 : Int) <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : ((0 : Int) <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves)))) (PreH12 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH13 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (Spec text (Z.land moves 1)) ”

noncomputable def solver_return_wit_1_split_goal_spatial : Prop :=
  forall (text : (List Int)) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : ((0 : Int) <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : ((0 : Int) <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves)))) (PreH12 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH13 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  (charArray.undef_full ( &( "stack" ) ) 100005)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : ((0 : Int) <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : ((0 : Int) <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves)))) (PreH12 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top ≠ (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (top ≠ (0 : Int)) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((( &( "stack" ) ) + ((top - 1) * sizeof(CHAR)))) # Char |-> ((Znth (top - 1) reduced (0 : Int))))
  ** (charArray.missing_i ( &( "stack" ) ) (top - 1) (0 : Int) top reduced)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top ≠ (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (top ≠ (0 : Int)) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (top = (0 : Int)) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : (top = (0 : Int))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : ((0 : Int) <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : ((0 : Int) <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves)))) (PreH13 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH14 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ (top = (0 : Int)) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((( &( "stack" ) ) + (top * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ ((Znth (top - 1) reduced (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ” &&
  “ (top ≠ (0 : Int)) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (text : (List Int)) (s_pre : Int) (moves : Int) (reduced : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) reduced (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : (top ≠ (0 : Int))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : ((0 : Int) <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves)))) (PreH14 : (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves)) (PreH15 : ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)
  ** (charArray.undef_seg ( &( "stack" ) ) top 100005)
|--
  “ ((Znth (top - 1) reduced (0 : Int)) ≠ (Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ” &&
  “ (top ≠ (0 : Int)) ” &&
  “ (1 <= (Zlength (text))) ” &&
  “ ((Zlength (text)) <= 100000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (Zlength (text)))) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (text))) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (reduced))) ” &&
  “ ((0 : Int) <= moves) ” &&
  “ (moves <= i) ” &&
  “ (i = (top + (2 * moves))) ” &&
  “ (PrefixGameState (sublist ((0 : Int)) (i) (text)) reduced moves) ” &&
  “ ((Znth i (text ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((( &( "stack" ) ) + (top * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg ( &( "stack" ) ) (top + 1) 100005)
  ** (charArray.full s_pre ((Zlength (text)) + 1) (text ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.full ( &( "stack" ) ) top reduced)


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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_goal
