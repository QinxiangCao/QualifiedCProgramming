import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P003_1763A_absolute_maximization_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  ((( &( "all_and" ) )) # Int |->_)
  ** ((( &( "all_or" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  ((( &( "all_or" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "all_and" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "all_or" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "all_or" ) )) # Int |-> ((Z.lor all_or (Znth i input (0 : Int)))))
  ** ((( &( "all_and" ) )) # Int |-> ((Z.land all_and (Znth i input (0 : Int)))))
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "all_or" ) )) # Int |-> (all_or))
  ** ((( &( "all_and" ) )) # Int |-> (all_and))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ ((all_or - all_and) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (all_or - all_and)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (3 <= n_pre) ” &&
  “ (n_pre <= 512) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1024) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) input (0 : Int))) ” &&
  “ ((Znth (0 : Int) input (0 : Int)) < 1024) ” &&
  “ (BitwiseScanState input (0 : Int) (0 : Int) (Znth (0 : Int) input (0 : Int))) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
) \/
(
forall (input : (List Int)) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  TT && emp 
|--
  “ (BitwiseScanState input (0 : Int) (0 : Int) (Znth (0 : Int) input (0 : Int))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  (BitwiseScanState input (0 : Int) (0 : Int) (Znth (0 : Int) input (0 : Int)))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (3 <= n_pre) ” &&
  “ (n_pre <= 512) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024))) ” &&
  “ ((0 : Int) <= (Z.lor all_or (Znth i input (0 : Int)))) ” &&
  “ ((Z.lor all_or (Znth i input (0 : Int))) < 1024) ” &&
  “ ((0 : Int) <= (Z.land all_and (Znth i input (0 : Int)))) ” &&
  “ ((Z.land all_and (Znth i input (0 : Int))) < 1024) ” &&
  “ (BitwiseScanState input (i + 1) (Z.lor all_or (Znth i input (0 : Int))) (Z.land all_and (Znth i input (0 : Int)))) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
) \/
(
forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  TT && emp 
|--
  “ (BitwiseScanState input (i + 1) (Z.lor all_or (Znth i input (0 : Int))) (Z.land all_and (Znth i input (0 : Int)))) ” &&
  “ ((Z.land all_and (Znth i input (0 : Int))) < 1024) ” &&
  “ ((0 : Int) <= (Z.land all_and (Znth i input (0 : Int)))) ” &&
  “ ((Z.lor all_or (Znth i input (0 : Int))) < 1024) ” &&
  “ ((0 : Int) <= (Z.lor all_or (Znth i input (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (BitwiseScanState input (i + 1) (Z.lor all_or (Znth i input (0 : Int))) (Z.land all_and (Znth i input (0 : Int))))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  ((Z.land all_and (Znth i input (0 : Int))) < 1024)

noncomputable def solver_entail_wit_2_split_goal_3 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  ((0 : Int) <= (Z.land all_and (Znth i input (0 : Int))))

noncomputable def solver_entail_wit_2_split_goal_4 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  ((Z.lor all_or (Znth i input (0 : Int))) < 1024)

noncomputable def solver_entail_wit_2_split_goal_5 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  ((0 : Int) <= (Z.lor all_or (Znth i input (0 : Int))))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ (Spec input (all_or - all_and)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
) \/
(
forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  TT && emp 
|--
  “ (Spec input (all_or - all_and)) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (Spec input (all_or - all_and))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (3 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 512)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024)))) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (3 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 512) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) < 1024))) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (3 <= n_pre) ” &&
  “ (n_pre <= 512) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024))) ” &&
  “ ((0 : Int) <= all_or) ” &&
  “ (all_or < 1024) ” &&
  “ ((0 : Int) <= all_and) ” &&
  “ (all_and < 1024) ” &&
  “ (BitwiseScanState input i all_or all_and) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (all_and : Int) (all_or : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 512)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024)))) (PreH8 : ((0 : Int) <= all_or)) (PreH9 : (all_or < 1024)) (PreH10 : ((0 : Int) <= all_and)) (PreH11 : (all_and < 1024)) (PreH12 : (BitwiseScanState input i all_or all_and)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (3 <= n_pre) ” &&
  “ (n_pre <= 512) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) < 1024))) ” &&
  “ ((0 : Int) <= all_or) ” &&
  “ (all_or < 1024) ” &&
  “ ((0 : Int) <= all_and) ” &&
  “ (all_and < 1024) ” &&
  “ (BitwiseScanState input i all_or all_and) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 512)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_goal
