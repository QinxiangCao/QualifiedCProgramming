import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P048_1607E_robot_on_the_board_1_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "c" ) )) # Int |->_)
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "r" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "maxc" ) )) # Int |->_)
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "minc" ) )) # Int |->_)
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "maxr" ) )) # Int |->_)
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "minr" ) )) # Int |->_)
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "bc" ) )) # Int |->_)
  ** ((( &( "br" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "br" ) )) # Int |->_)
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |->_)
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |->_)
  ** ((( &( "bc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "br" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((1 - (0 : Int)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (1 - (0 : Int))) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |->_)
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |->_)
  ** ((( &( "bc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "br" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |->_)
  ** ((( &( "bc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "br" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((1 - (0 : Int)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (1 - (0 : Int))) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |->_)
  ** ((( &( "bc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "br" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
  ** ((( &( "bc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "br" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minc" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "maxr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "minr" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "r" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (85 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 85) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH27 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((r - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r - 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH27 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (68 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 68) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH27 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH28 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((r + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r + 1)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH27 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH28 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (76 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 76) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH27 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH28 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH29 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((c - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c - 1)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH27 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH28 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH29 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((r - 1) > maxr)) (PreH2 : ((r - 1) < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = (0 : Int))) (PreH25 : (bc = (0 : Int))) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH28 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH29 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxr" ) )) # Int |->_)
  ** ((( &( "nminr" ) )) # Int |-> ((r - 1)))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r - 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((r + 1) > maxr)) (PreH2 : ((r + 1) < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = (0 : Int))) (PreH25 : (bc = (0 : Int))) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH28 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH29 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH30 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxr" ) )) # Int |->_)
  ** ((( &( "nminr" ) )) # Int |-> ((r + 1)))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r + 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (r > maxr)) (PreH2 : (r < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = (0 : Int))) (PreH25 : (bc = (0 : Int))) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH28 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH29 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH30 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH31 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxr" ) )) # Int |->_)
  ** ((( &( "nminr" ) )) # Int |-> (r))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c - 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (r > maxr)) (PreH2 : (r < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = (0 : Int))) (PreH25 : (bc = (0 : Int))) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH28 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH29 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH30 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH31 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxr" ) )) # Int |->_)
  ** ((( &( "nminr" ) )) # Int |-> (r))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c + 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> (c))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> ((r - 1)))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r - 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> (c))
  ** ((( &( "nmaxr" ) )) # Int |-> ((r - 1)))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r - 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> (c))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r - 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> (c))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> ((r + 1)))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r + 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> (c))
  ** ((( &( "nmaxr" ) )) # Int |-> ((r + 1)))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r + 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> (c))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> ((r + 1)))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> ((c - 1)))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> (r))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c - 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> ((c - 1)))
  ** ((( &( "nmaxr" ) )) # Int |-> (r))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c - 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> ((c - 1)))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c - 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> ((c + 1)))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> (r))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c + 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> ((c + 1)))
  ** ((( &( "nmaxr" ) )) # Int |-> (r))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c + 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  ((( &( "nmaxc" ) )) # Int |->_)
  ** ((( &( "nminc" ) )) # Int |-> ((c + 1)))
  ** ((( &( "nmaxr" ) )) # Int |-> (maxr))
  ** ((( &( "nminr" ) )) # Int |-> (minr))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> ((c + 1)))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ False ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (Zlength (moves)))) (PreH10 : ((-(i + 1)) <= r)) (PreH11 : (r <= (i + 1))) (PreH12 : ((-(i + 1)) <= c)) (PreH13 : (c <= (i + 1))) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : ((-(i + 1)) <= nminr)) (PreH23 : (nminr <= (0 : Int))) (PreH24 : ((0 : Int) <= nmaxr)) (PreH25 : (nmaxr <= (i + 1))) (PreH26 : ((-(i + 1)) <= nminc)) (PreH27 : (nminc <= (0 : Int))) (PreH28 : ((0 : Int) <= nmaxc)) (PreH29 : (nmaxc <= (i + 1))) (PreH30 : (br = (0 : Int))) (PreH31 : (bc = (0 : Int))) (PreH32 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH33 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH34 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "nminr" ) )) # Int |-> (nminr))
  ** ((( &( "nmaxr" ) )) # Int |-> (nmaxr))
  ** ((( &( "nminc" ) )) # Int |-> (nminc))
  ** ((( &( "nmaxc" ) )) # Int |-> (nmaxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((nmaxr - nminr) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (nmaxr - nminr)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxr - nminr) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1)) <= r)) (PreH12 : (r <= (i + 1))) (PreH13 : ((-(i + 1)) <= c)) (PreH14 : (c <= (i + 1))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= (0 : Int))) (PreH17 : ((0 : Int) <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= (0 : Int))) (PreH21 : ((0 : Int) <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1)) <= nminr)) (PreH24 : (nminr <= (0 : Int))) (PreH25 : ((0 : Int) <= nmaxr)) (PreH26 : (nmaxr <= (i + 1))) (PreH27 : ((-(i + 1)) <= nminc)) (PreH28 : (nminc <= (0 : Int))) (PreH29 : ((0 : Int) <= nmaxc)) (PreH30 : (nmaxc <= (i + 1))) (PreH31 : (br = (0 : Int))) (PreH32 : (bc = (0 : Int))) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH35 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "nminr" ) )) # Int |-> (nminr))
  ** ((( &( "nmaxr" ) )) # Int |-> (nmaxr))
  ** ((( &( "nminc" ) )) # Int |-> (nminc))
  ** ((( &( "nmaxc" ) )) # Int |-> (nmaxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((nmaxc - nminc) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (nmaxc - nminc)) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) < m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (nminr))
  ** ((( &( "maxr" ) )) # Int |-> (nmaxr))
  ** ((( &( "minc" ) )) # Int |-> (nminc))
  ** ((( &( "maxc" ) )) # Int |-> (nmaxc))
  ** ((( &( "br" ) )) # Int |-> (br))
  ** ((( &( "bc" ) )) # Int |-> (bc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= (0 : Int))) (PreH14 : ((0 : Int) <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= (0 : Int))) (PreH18 : ((0 : Int) <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = (0 : Int))) (PreH21 : (bc = (0 : Int))) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> (1))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (minr))
  ** ((( &( "bc" ) )) # Int |-> (minc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((1 - minr) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (1 - minr)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= (0 : Int))) (PreH14 : ((0 : Int) <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= (0 : Int))) (PreH18 : ((0 : Int) <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = (0 : Int))) (PreH21 : (bc = (0 : Int))) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> (1))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (minr))
  ** ((( &( "bc" ) )) # Int |-> (minc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= (0 : Int))) (PreH14 : ((0 : Int) <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= (0 : Int))) (PreH18 : ((0 : Int) <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = (0 : Int))) (PreH21 : (bc = (0 : Int))) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> ((1 - minr)))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (minr))
  ** ((( &( "bc" ) )) # Int |-> (minc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((1 - minc) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (1 - minc)) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= (0 : Int))) (PreH14 : ((0 : Int) <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= (0 : Int))) (PreH18 : ((0 : Int) <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = (0 : Int))) (PreH21 : (bc = (0 : Int))) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  ((( &( "row" ) )) # Ptr |-> (row_pre))
  ** ((row_pre) # Int |-> ((1 - minr)))
  ** ((( &( "col" ) )) # Ptr |-> (col_pre))
  ** ((col_pre) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "minr" ) )) # Int |-> (minr))
  ** ((( &( "maxr" ) )) # Int |-> (maxr))
  ** ((( &( "minc" ) )) # Int |-> (minc))
  ** ((( &( "maxc" ) )) # Int |-> (maxc))
  ** ((( &( "br" ) )) # Int |-> (minr))
  ** ((( &( "bc" ) )) # Int |-> (minc))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (moves))) ” &&
  “ ((-(0 : Int)) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-(0 : Int)) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-(0 : Int)) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-(0 : Int)) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (PrefixWindow moves (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ (WindowFits n_pre m_pre (0 : Int) (0 : Int) (0 : Int) (0 : Int)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (moves : (List Int)) (PreH1 : ((1 - (0 : Int)) <= INT_MAX)) (PreH2 : ((1 - (0 : Int)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
|--
  “ (WindowFits n_pre m_pre (0 : Int) (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ (PrefixWindow moves (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ”
  &&  (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (moves : (List Int)) (PreH1 : ((1 - (0 : Int)) <= INT_MAX)) (PreH2 : ((1 - (0 : Int)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
|--
  “ (WindowFits n_pre m_pre (0 : Int) (0 : Int) (0 : Int) (0 : Int)) ”

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (moves : (List Int)) (PreH1 : ((1 - (0 : Int)) <= INT_MAX)) (PreH2 : ((1 - (0 : Int)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
|--
  “ (PrefixWindow moves (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)) ”

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (moves : (List Int)) (PreH1 : ((1 - (0 : Int)) <= INT_MAX)) (PreH2 : ((1 - (0 : Int)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ”

noncomputable def solver_entail_wit_1_split_goal_spatial : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (moves : (List Int)) (PreH1 : ((1 - (0 : Int)) <= INT_MAX)) (PreH2 : ((1 - (0 : Int)) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  ((row_pre) # Int |-> ((1 - (0 : Int))))
  ** ((col_pre) # Int |-> ((1 - (0 : Int))))
|--
  (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr c maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr c maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr c maxc)

noncomputable def solver_entail_wit_2_1_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr minc c) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr minc c) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr minc c)

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c (r - 1) maxr minc maxc)

noncomputable def solver_entail_wit_2_3_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_4 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) c maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) c maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_4_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) c maxc)

noncomputable def solver_entail_wit_2_4_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_5 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) minc c) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) minc c) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_5_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) minc c)

noncomputable def solver_entail_wit_2_5_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_6 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_6_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c minr (r - 1) minc maxc)

noncomputable def solver_entail_wit_2_6_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) > maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_7 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c minr maxr c maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c minr maxr c maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_7_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c minr maxr c maxc)

noncomputable def solver_entail_wit_2_7_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_8 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c minr maxr minc c) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c minr maxr minc c) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_8_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c minr maxr minc c)

noncomputable def solver_entail_wit_2_8_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_9 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r - 1)) ” &&
  “ ((r - 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r - 1) c minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r - 1) c minr maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_9_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r - 1) c minr maxr minc maxc)

noncomputable def solver_entail_wit_2_9_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1) <= maxr)) (PreH4 : ((r - 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_10 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr c maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr c maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_10_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr c maxc)

noncomputable def solver_entail_wit_2_10_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_11 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr minc c) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr minc c) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_11_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr minc c)

noncomputable def solver_entail_wit_2_11_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_12 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_12_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c (r + 1) maxr minc maxc)

noncomputable def solver_entail_wit_2_12_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_13 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) c maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) c maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_13_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) c maxc)

noncomputable def solver_entail_wit_2_13_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_14 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc c) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc c) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_14_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc c)

noncomputable def solver_entail_wit_2_14_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_15 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_15_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c minr (r + 1) minc maxc)

noncomputable def solver_entail_wit_2_15_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) > maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_16 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c minr maxr c maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c minr maxr c maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_16_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c minr maxr c maxc)

noncomputable def solver_entail_wit_2_16_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_17 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c minr maxr minc c) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c minr maxr minc c) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_17_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c minr maxr minc c)

noncomputable def solver_entail_wit_2_17_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_18 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= (r + 1)) ” &&
  “ ((r + 1) <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) (r + 1) c minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) (r + 1) c minr maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_18_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) (r + 1) c minr maxr minc maxc)

noncomputable def solver_entail_wit_2_18_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1) <= maxr)) (PreH4 : ((r + 1) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_19 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) r maxr (c - 1) maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) r maxr (c - 1) maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_19_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) r maxr (c - 1) maxc)

noncomputable def solver_entail_wit_2_19_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_20 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) r maxr minc (c - 1)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) r maxr minc (c - 1)) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_20_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) r maxr minc (c - 1))

noncomputable def solver_entail_wit_2_20_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_21 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) r maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) r maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_21_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) r maxr minc maxc)

noncomputable def solver_entail_wit_2_21_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_22 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) minr r (c - 1) maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) minr r (c - 1) maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_22_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) minr r (c - 1) maxc)

noncomputable def solver_entail_wit_2_22_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_23 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) minr r minc (c - 1)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) minr r minc (c - 1)) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_23_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) minr r minc (c - 1))

noncomputable def solver_entail_wit_2_23_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_24 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) minr r minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) minr r minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_24_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) minr r minc maxc)

noncomputable def solver_entail_wit_2_24_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_25 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) minr maxr (c - 1) maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) minr maxr (c - 1) maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_25_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) minr maxr (c - 1) maxc)

noncomputable def solver_entail_wit_2_25_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_26 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) minr maxr minc (c - 1)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) minr maxr minc (c - 1)) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_26_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) minr maxr minc (c - 1))

noncomputable def solver_entail_wit_2_26_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) > maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_27 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c - 1)) ” &&
  “ ((c - 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c - 1) minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c - 1) minr maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_27_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c - 1) minr maxr minc maxc)

noncomputable def solver_entail_wit_2_27_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c - 1) <= maxc)) (PreH2 : ((c - 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 = (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_28 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) r maxr (c + 1) maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) r maxr (c + 1) maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_28_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) r maxr (c + 1) maxc)

noncomputable def solver_entail_wit_2_28_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_29 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) r maxr minc (c + 1)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) r maxr minc (c + 1)) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_29_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) r maxr minc (c + 1))

noncomputable def solver_entail_wit_2_29_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_30 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) r maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) r maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_30_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) r maxr minc maxc)

noncomputable def solver_entail_wit_2_30_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_31 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) minr r (c + 1) maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) minr r (c + 1) maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_31_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) minr r (c + 1) maxc)

noncomputable def solver_entail_wit_2_31_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_32 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) minr r minc (c + 1)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) minr r minc (c + 1)) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_32_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) minr r minc (c + 1))

noncomputable def solver_entail_wit_2_32_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_33 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) minr r minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) minr r minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_33_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) minr r minc maxc)

noncomputable def solver_entail_wit_2_33_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_34 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) minr maxr (c + 1) maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) minr maxr (c + 1) maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_34_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) minr maxr (c + 1) maxc)

noncomputable def solver_entail_wit_2_34_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_35 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) minr maxr minc (c + 1)) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) minr maxr minc (c + 1)) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_35_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) minr maxr minc (c + 1))

noncomputable def solver_entail_wit_2_35_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) > maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_2_36 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  EX oldr : Int, EX oldc : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= (c + 1)) ” &&
  “ ((c + 1) <= (i + 1)) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ ((-(i + 1)) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ (PrefixWindow moves (i + 1) r (c + 1) minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1) r (c + 1) minr maxr minc maxc) ” &&
  “ (i < (Zlength (moves))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_36_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (PrefixWindow moves (i + 1) r (c + 1) minr maxr minc maxc)

noncomputable def solver_entail_wit_2_36_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : ((c + 1) <= maxc)) (PreH2 : ((c + 1) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= (0 : Int))) (PreH20 : ((0 : Int) <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= (0 : Int))) (PreH24 : ((0 : Int) <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = (0 : Int))) (PreH27 : (bc = (0 : Int))) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH30 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) (PreH31 : (85 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH32 : (68 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH33 : (76 ≠ (Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) ,
  (i < (Zlength (moves)))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) < m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (moves))) ” &&
  “ ((-(i + 1)) <= r) ” &&
  “ (r <= (i + 1)) ” &&
  “ ((-(i + 1)) <= c) ” &&
  “ (c <= (i + 1)) ” &&
  “ ((-(i + 1)) <= nminr) ” &&
  “ (nminr <= (0 : Int)) ” &&
  “ ((0 : Int) <= nmaxr) ” &&
  “ (nmaxr <= (i + 1)) ” &&
  “ ((-(i + 1)) <= nminc) ” &&
  “ (nminc <= (0 : Int)) ” &&
  “ ((0 : Int) <= nmaxc) ” &&
  “ (nmaxc <= (i + 1)) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc) ” &&
  “ (WindowFits n_pre m_pre nminr nmaxr nminc nmaxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) < m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  TT && emp 
|--
  “ (WindowFits n_pre m_pre nminr nmaxr nminc nmaxc) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) < m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  (WindowFits n_pre m_pre nminr nmaxr nminc nmaxc)

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) < m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((-(Zlength (moves))) <= r) ” &&
  “ (r <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= c) ” &&
  “ (c <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (Zlength (moves))) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  TT && emp 
|--
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)

noncomputable def solver_entail_wit_4_1_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) = (0 : Int))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxr - nminr) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1)) <= r)) (PreH12 : (r <= (i + 1))) (PreH13 : ((-(i + 1)) <= c)) (PreH14 : (c <= (i + 1))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= (0 : Int))) (PreH17 : ((0 : Int) <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= (0 : Int))) (PreH21 : ((0 : Int) <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1)) <= nminr)) (PreH24 : (nminr <= (0 : Int))) (PreH25 : ((0 : Int) <= nmaxr)) (PreH26 : (nmaxr <= (i + 1))) (PreH27 : ((-(i + 1)) <= nminc)) (PreH28 : (nminc <= (0 : Int))) (PreH29 : ((0 : Int) <= nmaxc)) (PreH30 : (nmaxc <= (i + 1))) (PreH31 : (br = (0 : Int))) (PreH32 : (bc = (0 : Int))) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH35 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((-(Zlength (moves))) <= r) ” &&
  “ (r <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= c) ” &&
  “ (c <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (Zlength (moves))) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxr - nminr) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1)) <= r)) (PreH12 : (r <= (i + 1))) (PreH13 : ((-(i + 1)) <= c)) (PreH14 : (c <= (i + 1))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= (0 : Int))) (PreH17 : ((0 : Int) <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= (0 : Int))) (PreH21 : ((0 : Int) <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1)) <= nminr)) (PreH24 : (nminr <= (0 : Int))) (PreH25 : ((0 : Int) <= nmaxr)) (PreH26 : (nmaxr <= (i + 1))) (PreH27 : ((-(i + 1)) <= nminc)) (PreH28 : (nminc <= (0 : Int))) (PreH29 : ((0 : Int) <= nmaxc)) (PreH30 : (nmaxc <= (i + 1))) (PreH31 : (br = (0 : Int))) (PreH32 : (bc = (0 : Int))) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH35 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  TT && emp 
|--
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxr - nminr) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1)) <= r)) (PreH12 : (r <= (i + 1))) (PreH13 : ((-(i + 1)) <= c)) (PreH14 : (c <= (i + 1))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= (0 : Int))) (PreH17 : ((0 : Int) <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= (0 : Int))) (PreH21 : ((0 : Int) <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1)) <= nminr)) (PreH24 : (nminr <= (0 : Int))) (PreH25 : ((0 : Int) <= nmaxr)) (PreH26 : (nmaxr <= (i + 1))) (PreH27 : ((-(i + 1)) <= nminc)) (PreH28 : (nminc <= (0 : Int))) (PreH29 : ((0 : Int) <= nmaxc)) (PreH30 : (nmaxc <= (i + 1))) (PreH31 : (br = (0 : Int))) (PreH32 : (bc = (0 : Int))) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH35 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)

noncomputable def solver_entail_wit_4_2_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxr - nminr) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1)) <= r)) (PreH12 : (r <= (i + 1))) (PreH13 : ((-(i + 1)) <= c)) (PreH14 : (c <= (i + 1))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= (0 : Int))) (PreH17 : ((0 : Int) <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= (0 : Int))) (PreH21 : ((0 : Int) <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1)) <= nminr)) (PreH24 : (nminr <= (0 : Int))) (PreH25 : ((0 : Int) <= nmaxr)) (PreH26 : (nmaxr <= (i + 1))) (PreH27 : ((-(i + 1)) <= nminc)) (PreH28 : (nminc <= (0 : Int))) (PreH29 : ((0 : Int) <= nmaxc)) (PreH30 : (nmaxc <= (i + 1))) (PreH31 : (br = (0 : Int))) (PreH32 : (bc = (0 : Int))) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH35 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))

noncomputable def solver_entail_wit_4_3 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) >= m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((-(Zlength (moves))) <= r) ” &&
  “ (r <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= c) ” &&
  “ (c <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (Zlength (moves))) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) >= m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  TT && emp 
|--
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_3_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) >= m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)

noncomputable def solver_entail_wit_4_3_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (moves : (List Int)) (oldr : Int) (oldc : Int) (i : Int) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (nminr : Int) (nmaxr : Int) (nminc : Int) (nmaxc : Int) (br : Int) (bc : Int) (PreH1 : ((nmaxc - nminc) >= m_pre)) (PreH2 : ((nmaxr - nminr) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves (0 : Int)) = 76) ∨ ((Znth k_2 moves (0 : Int)) = 82)) ∨ ((Znth k_2 moves (0 : Int)) = 68)) ∨ ((Znth k_2 moves (0 : Int)) = 85)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1)) <= r)) (PreH13 : (r <= (i + 1))) (PreH14 : ((-(i + 1)) <= c)) (PreH15 : (c <= (i + 1))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1)) <= nminr)) (PreH25 : (nminr <= (0 : Int))) (PreH26 : ((0 : Int) <= nmaxr)) (PreH27 : (nmaxr <= (i + 1))) (PreH28 : ((-(i + 1)) <= nminc)) (PreH29 : (nminc <= (0 : Int))) (PreH30 : ((0 : Int) <= nmaxc)) (PreH31 : (nmaxc <= (i + 1))) (PreH32 : (br = (0 : Int))) (PreH33 : (bc = (0 : Int))) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc)) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH36 : (PrefixWindow moves (i + 1) r c nminr nmaxr nminc nmaxc)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= (0 : Int))) (PreH14 : ((0 : Int) <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= (0 : Int))) (PreH18 : ((0 : Int) <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = (0 : Int))) (PreH21 : (bc = (0 : Int))) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  ((row_pre) # Int |-> ((1 - minr)))
  ** ((col_pre) # Int |-> ((1 - minc)))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX out : (Int × Int),
  “ (Spec n_pre m_pre moves out) ”
  &&  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 ((fst (out)) :: (@List.nil Int)))
  ** (intArray.full col_pre 1 ((snd (out)) :: (@List.nil Int)))
) \/
(
forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : ((1 - minc) <= INT_MAX)) (PreH2 : ((1 - minr) <= INT_MAX)) (PreH3 : ((1 - minc) >= INT_MIN)) (PreH4 : ((1 - minr) >= INT_MIN)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH12 : ((-(Zlength (moves))) <= r)) (PreH13 : (r <= (Zlength (moves)))) (PreH14 : ((-(Zlength (moves))) <= c)) (PreH15 : (c <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minr)) (PreH17 : (minr <= (0 : Int))) (PreH18 : ((0 : Int) <= maxr)) (PreH19 : (maxr <= (Zlength (moves)))) (PreH20 : ((-(Zlength (moves))) <= minc)) (PreH21 : (minc <= (0 : Int))) (PreH22 : ((0 : Int) <= maxc)) (PreH23 : (maxc <= (Zlength (moves)))) (PreH24 : (br = (0 : Int))) (PreH25 : (bc = (0 : Int))) (PreH26 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  ((row_pre) # Int |-> ((1 - minr)))
  ** ((col_pre) # Int |-> ((1 - minc)))
|--
  EX out : (Int × Int),
  “ (Spec n_pre m_pre moves out) ”
  &&  (intArray.full row_pre 1 ((fst (out)) :: (@List.nil Int)))
  ** (intArray.full col_pre 1 ((snd (out)) :: (@List.nil Int)))
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85)))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (moves)))) -> (((((Znth i moves (0 : Int)) = 76) ∨ ((Znth i moves (0 : Int)) = 82)) ∨ ((Znth i moves (0 : Int)) = 68)) ∨ ((Znth i moves (0 : Int)) = 85))) ”
  &&  (intArray.undef_full row_pre 1)
  ** (intArray.undef_full col_pre 1)
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (moves))) ” &&
  “ ((-i) <= r) ” &&
  “ (r <= i) ” &&
  “ ((-i) <= c) ” &&
  “ (c <= i) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i r c minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (bc : Int) (br : Int) (maxc : Int) (minc : Int) (maxr : Int) (minr : Int) (c : Int) (r : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= (0 : Int))) (PreH16 : ((0 : Int) <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= (0 : Int))) (PreH20 : ((0 : Int) <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = (0 : Int))) (PreH23 : (bc = (0 : Int))) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc)) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc)) (PreH26 : ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (moves))) ” &&
  “ ((-i) <= r) ” &&
  “ (r <= i) ” &&
  “ ((-i) <= c) ” &&
  “ (c <= i) ” &&
  “ ((-i) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= i) ” &&
  “ ((-i) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= i) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (PrefixWindow moves i r c minr maxr minc maxc) ” &&
  “ (WindowFits n_pre m_pre minr maxr minc maxc) ” &&
  “ ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) ≠ (0 : Int)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (moves ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (col_pre : Int) (row_pre : Int) (m_pre : Int) (n_pre : Int) (s_pre : Int) (moves : (List Int)) (r : Int) (c : Int) (minr : Int) (maxr : Int) (minc : Int) (maxc : Int) (br : Int) (bc : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= (0 : Int))) (PreH14 : ((0 : Int) <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= (0 : Int))) (PreH18 : ((0 : Int) <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = (0 : Int))) (PreH21 : (bc = (0 : Int))) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc)) ,
  (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= 1000000) ” &&
  “ (1 <= (Zlength (moves))) ” &&
  “ ((Zlength (moves)) <= 1000000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (moves)))) -> (((((Znth k moves (0 : Int)) = 76) ∨ ((Znth k moves (0 : Int)) = 82)) ∨ ((Znth k moves (0 : Int)) = 68)) ∨ ((Znth k moves (0 : Int)) = 85))) ” &&
  “ ((-(Zlength (moves))) <= r) ” &&
  “ (r <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= c) ” &&
  “ (c <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minr) ” &&
  “ (minr <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxr) ” &&
  “ (maxr <= (Zlength (moves))) ” &&
  “ ((-(Zlength (moves))) <= minc) ” &&
  “ (minc <= (0 : Int)) ” &&
  “ ((0 : Int) <= maxc) ” &&
  “ (maxc <= (Zlength (moves))) ” &&
  “ (br = (0 : Int)) ” &&
  “ (bc = (0 : Int)) ” &&
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc) ”
  &&  (intArray.full row_pre 1 (1 :: (@List.nil Int)))
  ** (intArray.full col_pre 1 (1 :: (@List.nil Int)))
  ** (charArray.full s_pre ((Zlength (moves)) + 1) (moves ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_which_implies_wit_1 : Prop :=
  (
forall (row : Int) (col : Int) ,
  (intArray.undef_full row 1)
  ** (intArray.undef_full col 1)
|--
  ((row) # Int |->_)
  ** ((col) # Int |->_)
) \/
(
forall (row : Int) (col : Int) ,
  (intArray.undef_full row 1)
  ** (intArray.undef_full col 1)
|--
  EX x_2 : Int, EX x : Int,
  ((col) # Int |-> (x_2))
  ** ((row) # Int |-> (x))
)

noncomputable def solver_which_implies_wit_2 : Prop :=
  (
forall (row : Int) (col : Int) ,
  (intArray.full row 1 (1 :: (@List.nil Int)))
  ** (intArray.full col 1 (1 :: (@List.nil Int)))
|--
  ((row) # Int |-> (1))
  ** ((col) # Int |-> (1))
) \/
(
forall (row : Int) (col : Int) ,
  (intArray.full row 1 (1 :: (@List.nil Int)))
  ** (intArray.full col 1 (1 :: (@List.nil Int)))
|--
  ((row) # Int |-> (1))
  ** ((col) # Int |-> (1))
)

noncomputable def solver_which_implies_wit_2_split_goal_spatial : Prop :=
  forall (row : Int) (col : Int) ,
  (intArray.full row 1 (1 :: (@List.nil Int)))
  ** (intArray.full col 1 (1 :: (@List.nil Int)))
|--
  ((row) # Int |-> (1))
  ** ((col) # Int |-> (1))


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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4
  proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5
  proof_of_solver_entail_wit_2_6 : solver_entail_wit_2_6
  proof_of_solver_entail_wit_2_7 : solver_entail_wit_2_7
  proof_of_solver_entail_wit_2_8 : solver_entail_wit_2_8
  proof_of_solver_entail_wit_2_9 : solver_entail_wit_2_9
  proof_of_solver_entail_wit_2_10 : solver_entail_wit_2_10
  proof_of_solver_entail_wit_2_11 : solver_entail_wit_2_11
  proof_of_solver_entail_wit_2_12 : solver_entail_wit_2_12
  proof_of_solver_entail_wit_2_13 : solver_entail_wit_2_13
  proof_of_solver_entail_wit_2_14 : solver_entail_wit_2_14
  proof_of_solver_entail_wit_2_15 : solver_entail_wit_2_15
  proof_of_solver_entail_wit_2_16 : solver_entail_wit_2_16
  proof_of_solver_entail_wit_2_17 : solver_entail_wit_2_17
  proof_of_solver_entail_wit_2_18 : solver_entail_wit_2_18
  proof_of_solver_entail_wit_2_19 : solver_entail_wit_2_19
  proof_of_solver_entail_wit_2_20 : solver_entail_wit_2_20
  proof_of_solver_entail_wit_2_21 : solver_entail_wit_2_21
  proof_of_solver_entail_wit_2_22 : solver_entail_wit_2_22
  proof_of_solver_entail_wit_2_23 : solver_entail_wit_2_23
  proof_of_solver_entail_wit_2_24 : solver_entail_wit_2_24
  proof_of_solver_entail_wit_2_25 : solver_entail_wit_2_25
  proof_of_solver_entail_wit_2_26 : solver_entail_wit_2_26
  proof_of_solver_entail_wit_2_27 : solver_entail_wit_2_27
  proof_of_solver_entail_wit_2_28 : solver_entail_wit_2_28
  proof_of_solver_entail_wit_2_29 : solver_entail_wit_2_29
  proof_of_solver_entail_wit_2_30 : solver_entail_wit_2_30
  proof_of_solver_entail_wit_2_31 : solver_entail_wit_2_31
  proof_of_solver_entail_wit_2_32 : solver_entail_wit_2_32
  proof_of_solver_entail_wit_2_33 : solver_entail_wit_2_33
  proof_of_solver_entail_wit_2_34 : solver_entail_wit_2_34
  proof_of_solver_entail_wit_2_35 : solver_entail_wit_2_35
  proof_of_solver_entail_wit_2_36 : solver_entail_wit_2_36
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1
  proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_goal
