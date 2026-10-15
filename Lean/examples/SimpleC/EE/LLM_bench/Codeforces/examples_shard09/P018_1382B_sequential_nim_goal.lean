import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P018_1382B_sequential_nim_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))) ,
  ((( &( "c" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre piles)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (intArray.full a_pre n_pre piles)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Znth c piles (0 : Int)) = 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (intArray.full a_pre n_pre piles)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : ((0 : Int) <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre piles)
|--
  “ ((n_pre ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : ((0 : Int) <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre piles)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : ((0 : Int) <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre piles)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c ≠ n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : ((0 : Int) <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre piles)
|--
  “ ((c ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c ≠ n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : ((0 : Int) <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre piles)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c ≠ n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : ((0 : Int) <= c)) (PreH6 : (c <= n_pre)) (PreH7 : (LeadingOnes piles c)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre piles)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles (0 : Int))) ∧ ((Znth i_3 piles (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))) ,
  (intArray.full a_pre n_pre piles)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (piles))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (0 : Int))) -> ((Znth i_2 piles (0 : Int)) = 1)) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles (0 : Int))) ∧ ((Znth i_3 piles (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))) ,
  TT && emp 
|--
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (0 : Int))) -> ((Znth i_2 piles (0 : Int)) = 1)) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (piles : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles (0 : Int))) ∧ ((Znth i_3 piles (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))) ,
  forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (0 : Int))) -> ((Znth i_2 piles (0 : Int)) = 1))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (piles : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> ((1 <= (Znth i_3 piles (0 : Int))) ∧ ((Znth i_3 piles (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (piles)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Znth c piles (0 : Int)) = 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (intArray.full a_pre n_pre piles)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (piles))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= n_pre) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < (c + 1))) -> ((Znth i_2 piles (0 : Int)) = 1)) ”
  &&  (intArray.full a_pre n_pre piles)

noncomputable def solver_entail_wit_3_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (intArray.full a_pre n_pre piles)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (piles))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= n_pre) ” &&
  “ (LeadingOnes piles c) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  TT && emp 
|--
  “ (LeadingOnes piles c) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (LeadingOnes piles c)

noncomputable def solver_entail_wit_3_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Znth c piles (0 : Int)) ≠ 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (intArray.full a_pre n_pre piles)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (piles))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= n_pre) ” &&
  “ (LeadingOnes piles c) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Znth c piles (0 : Int)) ≠ 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  TT && emp 
|--
  “ (LeadingOnes piles c) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Znth c piles (0 : Int)) ≠ 1)) (PreH2 : (c < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= c)) (PreH8 : (c <= n_pre)) (PreH9 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (LeadingOnes piles c)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem c 2) ≠ (0 : Int))) (PreH2 : (c ≠ n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  (intArray.full a_pre n_pre piles)
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem c 2) ≠ (0 : Int))) (PreH2 : (c ≠ n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  TT && emp 
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem c 2) = (0 : Int))) (PreH2 : (c ≠ n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  (intArray.full a_pre n_pre piles)
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem c 2) = (0 : Int))) (PreH2 : (c ≠ n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  TT && emp 
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  emp
)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem n_pre 2) ≠ 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  (intArray.full a_pre n_pre piles)
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem n_pre 2) ≠ 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  TT && emp 
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem n_pre 2) = 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  (intArray.full a_pre n_pre piles)
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  (intArray.full a_pre n_pre piles)
) \/
(
forall (n_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : ((Z.rem n_pre 2) = 1)) (PreH2 : (c = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (piles)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : (LeadingOnes piles c)) ,
  TT && emp 
|--
  EX out : Int,
  “ (Spec piles out) ” &&
  “ (SolverReturnBridge out 1) ”
  &&  emp
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (piles : (List Int)) (c : Int) (PreH1 : (c < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (piles)))) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c <= n_pre)) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1))) ,
  (intArray.full a_pre n_pre piles)
|--
  “ (c < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (piles))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i piles (0 : Int))) ∧ ((Znth i piles (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= n_pre) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < c)) -> ((Znth i_2 piles (0 : Int)) = 1)) ”
  &&  (((a_pre + (c * sizeof(INT)))) # Int |-> ((Znth c piles (0 : Int))))
  ** (intArray.missing_i a_pre c (0 : Int) n_pre piles)


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
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1
  proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_goal
