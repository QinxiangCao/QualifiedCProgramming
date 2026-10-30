import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P006_38A_army_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (2 <= ((Zlength (years)) + 1))) (PreH2 : (((Zlength (years)) + 1) <= 100)) (PreH3 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> ((ans + (Znth i ((0 : Int) :: years) (0 : Int)))))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  (
forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ ((ans + (Znth i ((0 : Int) :: years) (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ”
) \/
(
forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ ((ans + (Znth i ((0 : Int) :: years) (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_3_split_goal_1 : Prop :=
  forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ ((ans + (Znth i ((0 : Int) :: years) (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_3_split_goal_2 : Prop :=
  forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ ((INT_MIN) <= (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (2 <= ((Zlength (years)) + 1))) (PreH2 : (((Zlength (years)) + 1) <= 100)) (PreH3 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years (0 : Int))) ∧ ((Znth idx_2 years (0 : Int)) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1))) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ (2 <= ((Zlength (years)) + 1)) ” &&
  “ (((Zlength (years)) + 1) <= 100) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100))) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= a_pre) ” &&
  “ (a_pre <= b_pre) ” &&
  “ (b_pre <= ((Zlength (years)) + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (100 * (a_pre - a_pre))) ” &&
  “ (Spec ((Zlength (years)) + 1) years a_pre a_pre (0 : Int)) ”
  &&  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
) \/
(
forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (PreH1 : (2 <= ((Zlength (years)) + 1))) (PreH2 : (((Zlength (years)) + 1) <= 100)) (PreH3 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years (0 : Int))) ∧ ((Znth idx_2 years (0 : Int)) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1))) ,
  TT && emp 
|--
  “ (Spec ((Zlength (years)) + 1) years a_pre a_pre (0 : Int)) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (PreH1 : (2 <= ((Zlength (years)) + 1))) (PreH2 : (((Zlength (years)) + 1) <= 100)) (PreH3 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years (0 : Int))) ∧ ((Znth idx_2 years (0 : Int)) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1))) ,
  (Spec ((Zlength (years)) + 1) years a_pre a_pre (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (PreH1 : (2 <= ((Zlength (years)) + 1))) (PreH2 : (((Zlength (years)) + 1) <= 100)) (PreH3 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < (Zlength (years)))) -> ((1 <= (Znth idx_2 years (0 : Int))) ∧ ((Znth idx_2 years (0 : Int)) <= 100)))) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre < b_pre)) (PreH6 : (b_pre <= ((Zlength (years)) + 1))) ,
  forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ (2 <= ((Zlength (years)) + 1)) ” &&
  “ (((Zlength (years)) + 1) <= 100) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100))) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= (i + 1)) ” &&
  “ ((i + 1) <= b_pre) ” &&
  “ (b_pre <= ((Zlength (years)) + 1)) ” &&
  “ ((0 : Int) <= (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ” &&
  “ ((ans + (Znth i ((0 : Int) :: years) (0 : Int))) <= (100 * ((i + 1) - a_pre))) ” &&
  “ (Spec ((Zlength (years)) + 1) years a_pre (i + 1) (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ”
  &&  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
) \/
(
forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  TT && emp 
|--
  “ (Spec ((Zlength (years)) + 1) years a_pre (i + 1) (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ” &&
  “ ((ans + (Znth i ((0 : Int) :: years) (0 : Int))) <= (100 * ((i + 1) - a_pre))) ” &&
  “ ((0 : Int) <= (ans + (Znth i ((0 : Int) :: years) (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (Spec ((Zlength (years)) + 1) years a_pre (i + 1) (ans + (Znth i ((0 : Int) :: years) (0 : Int))))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  ((ans + (Znth i ((0 : Int) :: years) (0 : Int))) <= (100 * ((i + 1) - a_pre)))

noncomputable def solver_entail_wit_2_split_goal_3 : Prop :=
  forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  ((0 : Int) <= (ans + (Znth i ((0 : Int) :: years) (0 : Int))))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i >= b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ (Spec ((Zlength (years)) + 1) years a_pre b_pre ans) ”
  &&  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
) \/
(
forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i >= b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  TT && emp 
|--
  “ (Spec ((Zlength (years)) + 1) years a_pre b_pre ans) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (years : (List Int)) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i >= b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (Spec ((Zlength (years)) + 1) years a_pre b_pre ans)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (years : (List Int)) (d_pre : Int) (a_pre : Int) (b_pre : Int) (ans : Int) (i : Int) (PreH1 : (i < b_pre)) (PreH2 : (2 <= ((Zlength (years)) + 1))) (PreH3 : (((Zlength (years)) + 1) <= 100)) (PreH4 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100)))) (PreH5 : (1 <= a_pre)) (PreH6 : (a_pre <= i)) (PreH7 : (i <= b_pre)) (PreH8 : (b_pre <= ((Zlength (years)) + 1))) (PreH9 : ((0 : Int) <= ans)) (PreH10 : (ans <= (100 * (i - a_pre)))) (PreH11 : (Spec ((Zlength (years)) + 1) years a_pre i ans)) ,
  (intArray.full d_pre ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)
|--
  “ (i < b_pre) ” &&
  “ (2 <= ((Zlength (years)) + 1)) ” &&
  “ (((Zlength (years)) + 1) <= 100) ” &&
  “ forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < (Zlength (years)))) -> ((1 <= (Znth idx years (0 : Int))) ∧ ((Znth idx years (0 : Int)) <= 100))) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= i) ” &&
  “ (i <= b_pre) ” &&
  “ (b_pre <= ((Zlength (years)) + 1)) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans <= (100 * (i - a_pre))) ” &&
  “ (Spec ((Zlength (years)) + 1) years a_pre i ans) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int |-> ((Znth i ((0 : Int) :: years) (0 : Int))))
  ** (intArray.missing_i d_pre i (0 : Int) ((Zlength (years)) + 1) ((0 : Int) :: years))
  ** (intArray.undef_seg d_pre ((Zlength (years)) + 1) 101)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_goal
