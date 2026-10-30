import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P020_433A_kitahara_harukis_gift_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i weights (0 : Int)) = 100) ∨ ((Znth i weights (0 : Int)) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))) ,
  ((( &( "total" ) )) # Int |->_)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full w_pre n_pre weights)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i weights (0 : Int)) = 100) ∨ ((Znth i weights (0 : Int)) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "total" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full w_pre n_pre weights)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> ((total + (Z.quot (Znth i weights (0 : Int)) 100))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
|--
  “ ((total + (Z.quot (Znth i weights (0 : Int)) 100)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total + (Z.quot (Znth i weights (0 : Int)) 100))) ”
) \/
(
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
|--
  “ ((total + (Z.quot (Znth i weights (0 : Int)) 100)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total + (Z.quot (Znth i weights (0 : Int)) 100))) ”
)

noncomputable def solver_safety_wit_4_split_goal_1 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
|--
  “ ((total + (Z.quot (Znth i weights (0 : Int)) 100)) <= INT_MAX) ”

noncomputable def solver_safety_wit_4_split_goal_2 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
|--
  “ ((INT_MIN) <= (total + (Z.quot (Znth i weights (0 : Int)) 100))) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
|--
  “ (((Znth i weights (0 : Int)) ≠ (INT_MIN)) ∨ (100 ≠ (-1))) ” &&
  “ (100 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
|--
  “ (100 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 100) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
|--
  “ ((total ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : (PrefixUnitTotal weights n_pre total)) (PreH8 : (Spec weights (0 : Int))) (PreH9 : (SolverReturnBridge (0 : Int) (0 : Int))) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH10 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH10 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 (repeat_Z ((0 : Int)) (205)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 (repeat_Z ((0 : Int)) (205)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : (ReachTable weights (0 : Int) total reach_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "u" ) )) # Int |->_)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ (((Znth i weights (0 : Int)) ≠ (INT_MIN)) ∨ (100 ≠ (-1))) ” &&
  “ (100 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l)) ,
  (intArray.full w_pre n_pre weights)
  ** ((( &( "u" ) )) # Int |->_)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ (100 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 100) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ ((s - u) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s - u)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l)) (PreH18 : ((Znth (s - u) reach_l (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "reach" ) ) 205 reach_l)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray.full w_pre n_pre weights)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l)) (PreH18 : ((Znth (s - u) reach_l (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "reach" ) ) 205 (replace_Znth (s) (1) (reach_l)))
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray.full w_pre n_pre weights)
|--
  “ ((s - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s - 1)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l)) (PreH18 : ((Znth (s - u) reach_l (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "reach" ) ) 205 reach_l)
  ** ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** (intArray.full w_pre n_pre weights)
|--
  “ ((s - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s - 1)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (total : Int) (i : Int) (u : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1) total reach_l)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : ((0 : Int) <= (Z.quot total 2))) (PreH9 : ((Z.quot total 2) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total)) (PreH11 : (ReachTable weights n_pre total reach_l)) (PreH12 : (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int)))) (PreH13 : (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int)))) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ ((total ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : ((0 : Int) <= (Z.quot total 2))) (PreH9 : ((Z.quot total 2) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total)) (PreH11 : (ReachTable weights n_pre total reach_l)) (PreH12 : (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int)))) (PreH13 : (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int)))) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i weights (0 : Int)) = 100) ∨ ((Znth i weights (0 : Int)) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))) ,
  (intArray.full w_pre n_pre weights)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (2 * (0 : Int))) ” &&
  “ (PrefixUnitTotal weights (0 : Int) (0 : Int)) ”
  &&  (intArray.full w_pre n_pre weights)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i weights (0 : Int)) = 100) ∨ ((Znth i weights (0 : Int)) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))) ,
  TT && emp 
|--
  “ (PrefixUnitTotal weights (0 : Int) (0 : Int)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i weights (0 : Int)) = 100) ∨ ((Znth i weights (0 : Int)) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))) ,
  (PrefixUnitTotal weights (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i weights (0 : Int)) = 100) ∨ ((Znth i weights (0 : Int)) = 200)))) (PreH4 : (n_pre = (Zlength (weights)))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (total + (Z.quot (Znth i weights (0 : Int)) 100))) ” &&
  “ ((total + (Z.quot (Znth i weights (0 : Int)) 100)) <= (2 * (i + 1))) ” &&
  “ (PrefixUnitTotal weights (i + 1) (total + (Z.quot (Znth i weights (0 : Int)) 100))) ”
  &&  (intArray.full w_pre n_pre weights)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  TT && emp 
|--
  “ (PrefixUnitTotal weights (i + 1) (total + (Z.quot (Znth i weights (0 : Int)) 100))) ” &&
  “ ((total + (Z.quot (Znth i weights (0 : Int)) 100)) <= (2 * (i + 1))) ” &&
  “ ((0 : Int) <= (total + (Z.quot (Znth i weights (0 : Int)) 100))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (PrefixUnitTotal weights (i + 1) (total + (Z.quot (Znth i weights (0 : Int)) 100)))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  ((total + (Z.quot (Znth i weights (0 : Int)) 100)) <= (2 * (i + 1)))

noncomputable def solver_entail_wit_2_split_goal_3 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  ((0 : Int) <= (total + (Z.quot (Znth i weights (0 : Int)) 100)))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) ≠ (0 : Int))) ,
  (intArray.full w_pre n_pre weights)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ (Spec weights (0 : Int)) ” &&
  “ (SolverReturnBridge (0 : Int) (0 : Int)) ”
  &&  (intArray.full w_pre n_pre weights)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (SolverReturnBridge (0 : Int) (0 : Int)) ” &&
  “ (Spec weights (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) ≠ (0 : Int))) ,
  (SolverReturnBridge (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) ≠ (0 : Int))) ,
  (Spec weights (0 : Int))

noncomputable def solver_entail_wit_3_split_goal_3 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) ≠ (0 : Int))) ,
  (PrefixUnitTotal weights n_pre total)

noncomputable def solver_entail_wit_3_split_goal_4 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) ≠ (0 : Int))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) = (0 : Int))) ,
  (charArray.undef_full ( &( "reach" ) ) 205)
  ** (intArray.full w_pre n_pre weights)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= (sizeof(CHAR) * 205)) ” &&
  “ ((sizeof(CHAR) * 205) < INT_MAX) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
) \/
(
forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) = (0 : Int))) ,
  (charArray.undef_full ( &( "reach" ) ) 205)
|--
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) = (0 : Int))) ,
  (charArray.undef_full ( &( "reach" ) ) 205)
|--
  “ (PrefixUnitTotal weights n_pre total) ”

noncomputable def solver_entail_wit_4_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) = (0 : Int))) ,
  (charArray.undef_full ( &( "reach" ) ) 205)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”

noncomputable def solver_entail_wit_4_split_goal_spatial : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) (PreH11 : ((Z.rem total 2) = (0 : Int))) ,
  (charArray.undef_full ( &( "reach" ) ) 205)
|--
  (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (retval : Int) (PreH1 : (retval = (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH11 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  (charArray.full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 205))))
  ** (intArray.full w_pre n_pre weights)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 (repeat_Z ((0 : Int)) (205)))
) \/
(
forall (weights : (List Int)) (n_pre : Int) (total : Int) (retval : Int) (PreH1 : (retval = (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH11 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  (charArray.full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 205))))
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  (charArray.full ( &( "reach" ) ) 205 (repeat_Z ((0 : Int)) (205)))
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (retval : Int) (PreH1 : (retval = (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH11 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  (charArray.full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 205))))
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”

noncomputable def solver_entail_wit_5_split_goal_spatial : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (retval : Int) (PreH1 : (retval = (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))))) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH11 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  (charArray.full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205) (repeat_Z ((0 : Int)) ((sizeof(CHAR) * 205))))
|--
  (charArray.full ( &( "reach" ) ) 205 (repeat_Z ((0 : Int)) (205)))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  (charArray.full ( &( "reach" ) ) 205 (replace_Znth ((0 : Int)) (1) ((repeat_Z ((0 : Int)) (205)))))
  ** (intArray.full w_pre n_pre weights)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ (ReachTable weights (0 : Int) total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  TT && emp 
|--
  “ (ReachTable weights (0 : Int) total (replace_Znth ((0 : Int)) (1) ((repeat_Z ((0 : Int)) (205))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  (ReachTable weights (0 : Int) total (replace_Znth ((0 : Int)) (1) ((repeat_Z ((0 : Int)) (205)))))

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : (ReachTable weights (0 : Int) total reach_l_2)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l_2)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (ReachTable weights (0 : Int) total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : (ReachTable weights (0 : Int) total reach_l_2)) ,
  TT && emp 
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (total : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : (ReachTable weights (0 : Int) total reach_l_2)) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l_2)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Z.quot (Znth i weights (0 : Int)) 100) = (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ (1 <= (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ ((Z.quot (Znth i weights (0 : Int)) 100) <= 2) ” &&
  “ (((Z.quot (Znth i weights (0 : Int)) 100) - 1) <= total) ” &&
  “ (total <= total) ” &&
  “ (ReachInnerProgress weights i total total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  TT && emp 
|--
  “ (ReachInnerProgress weights i total total reach_l_2) ” &&
  “ (((Z.quot (Znth i weights (0 : Int)) 100) - 1) <= total) ” &&
  “ ((Z.quot (Znth i weights (0 : Int)) 100) <= 2) ” &&
  “ (1 <= (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (ReachInnerProgress weights i total total reach_l_2)

noncomputable def solver_entail_wit_8_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (((Z.quot (Znth i weights (0 : Int)) 100) - 1) <= total)

noncomputable def solver_entail_wit_8_split_goal_3 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  ((Z.quot (Znth i weights (0 : Int)) 100) <= 2)

noncomputable def solver_entail_wit_8_split_goal_4 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (1 <= (Z.quot (Znth i weights (0 : Int)) 100))

noncomputable def solver_entail_wit_8_split_goal_5 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_9 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s < u)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l_2)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (u = (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ (1 <= u) ” &&
  “ (u <= 2) ” &&
  “ (ReachTable weights (i + 1) total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s < u)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) ,
  TT && emp 
|--
  “ (ReachTable weights (i + 1) total reach_l_2) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s < u)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) ,
  (ReachTable weights (i + 1) total reach_l_2)

noncomputable def solver_entail_wit_9_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s < u)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_10_1 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) (PreH18 : ((Znth (s - u) reach_l_2 (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "reach" ) ) 205 (replace_Znth (s) (1) (reach_l_2)))
  ** (intArray.full w_pre n_pre weights)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (u = (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ (1 <= u) ” &&
  “ (u <= 2) ” &&
  “ ((u - 1) <= (s - 1)) ” &&
  “ ((s - 1) <= total) ” &&
  “ (ReachInnerProgress weights i (s - 1) total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) (PreH18 : ((Znth (s - u) reach_l_2 (0 : Int)) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (ReachInnerProgress weights i (s - 1) total (replace_Znth (s) (1) (reach_l_2))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_1_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) (PreH18 : ((Znth (s - u) reach_l_2 (0 : Int)) ≠ (0 : Int))) ,
  (ReachInnerProgress weights i (s - 1) total (replace_Znth (s) (1) (reach_l_2)))

noncomputable def solver_entail_wit_10_2 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) (PreH18 : ((Znth (s - u) reach_l_2 (0 : Int)) = (0 : Int))) ,
  (charArray.full ( &( "reach" ) ) 205 reach_l_2)
  ** (intArray.full w_pre n_pre weights)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (u = (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ (1 <= u) ” &&
  “ (u <= 2) ” &&
  “ ((u - 1) <= (s - 1)) ” &&
  “ ((s - 1) <= total) ” &&
  “ (ReachInnerProgress weights i (s - 1) total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) (PreH18 : ((Znth (s - u) reach_l_2 (0 : Int)) = (0 : Int))) ,
  TT && emp 
|--
  “ (ReachInnerProgress weights i (s - 1) total reach_l_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_2_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l_2)) (PreH18 : ((Znth (s - u) reach_l_2 (0 : Int)) = (0 : Int))) ,
  (ReachInnerProgress weights i (s - 1) total reach_l_2)

noncomputable def solver_entail_wit_11 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (total : Int) (i : Int) (u : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1) total reach_l_2)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l_2)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (ReachTable weights (i + 1) total reach_l) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (total : Int) (i : Int) (u : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1) total reach_l_2)) ,
  TT && emp 
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_11_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (total : Int) (i : Int) (u : Int) (PreH1 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH12 : (1 <= u)) (PreH13 : (u <= 2)) (PreH14 : (ReachTable weights (i + 1) total reach_l_2)) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_entail_wit_12 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l_2)
|--
  EX reach_l : (List Int),
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ ((0 : Int) <= (Z.quot total 2)) ” &&
  “ ((Z.quot total 2) < 205) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ (ReachTable weights n_pre total reach_l) ” &&
  “ (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int))) ” &&
  “ (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int))) ”
  &&  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  TT && emp 
|--
  “ (SolverReturnBridge (Znth (Z.quot total 2) reach_l_2 (0 : Int)) (Znth (Z.quot total 2) reach_l_2 (0 : Int))) ” &&
  “ (Spec weights (Znth (Z.quot total 2) reach_l_2 (0 : Int))) ” &&
  “ (ReachTable weights n_pre total reach_l_2) ” &&
  “ ((Z.quot total 2) < 205) ” &&
  “ ((0 : Int) <= (Z.quot total 2)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_split_goal_1 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (SolverReturnBridge (Znth (Z.quot total 2) reach_l_2 (0 : Int)) (Znth (Z.quot total 2) reach_l_2 (0 : Int)))

noncomputable def solver_entail_wit_12_split_goal_2 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (Spec weights (Znth (Z.quot total 2) reach_l_2 (0 : Int)))

noncomputable def solver_entail_wit_12_split_goal_3 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  (ReachTable weights n_pre total reach_l_2)

noncomputable def solver_entail_wit_12_split_goal_4 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  ((Z.quot total 2) < 205)

noncomputable def solver_entail_wit_12_split_goal_5 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  ((0 : Int) <= (Z.quot total 2))

noncomputable def solver_entail_wit_12_split_goal_6 : Prop :=
  forall (weights : (List Int)) (n_pre : Int) (reach_l_2 : (List Int)) (i : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> (((Znth j_2 weights (0 : Int)) = 100) ∨ ((Znth j_2 weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l_2)) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : ((0 : Int) <= (Z.quot total 2))) (PreH9 : ((Z.quot total 2) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total)) (PreH11 : (ReachTable weights n_pre total reach_l)) (PreH12 : (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int)))) (PreH13 : (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int)))) ,
  (intArray.full w_pre n_pre weights)
|--
  EX out : Int,
  “ (Spec weights out) ” &&
  “ (SolverReturnBridge out (Znth (Z.quot total 2) reach_l (0 : Int))) ”
  &&  (intArray.full w_pre n_pre weights)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (reach_l : (List Int)) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : ((0 : Int) <= (Z.quot total 2))) (PreH9 : ((Z.quot total 2) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total)) (PreH11 : (ReachTable weights n_pre total reach_l)) (PreH12 : (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int)))) (PreH13 : (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int)))) ,
  TT && emp 
|--
  EX out : Int,
  “ (Spec weights out) ” &&
  “ (SolverReturnBridge out (Znth (Z.quot total 2) reach_l (0 : Int))) ”
  &&  emp
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : (PrefixUnitTotal weights n_pre total)) (PreH8 : (Spec weights (0 : Int))) (PreH9 : (SolverReturnBridge (0 : Int) (0 : Int))) ,
  (intArray.full w_pre n_pre weights)
|--
  EX out : Int,
  “ (Spec weights out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  (intArray.full w_pre n_pre weights)
) \/
(
forall (weights : (List Int)) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : (PrefixUnitTotal weights n_pre total)) (PreH8 : (Spec weights (0 : Int))) (PreH9 : (SolverReturnBridge (0 : Int) (0 : Int))) ,
  TT && emp 
|--
  EX out : Int,
  “ (Spec weights out) ” &&
  “ (SolverReturnBridge out (0 : Int)) ”
  &&  emp
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (2 * i))) (PreH10 : (PrefixUnitTotal weights i total)) ,
  (intArray.full w_pre n_pre weights)
|--
  “ (i < n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (2 * i)) ” &&
  “ (PrefixUnitTotal weights i total) ”
  &&  (((w_pre + (i * sizeof(INT)))) # Int |-> ((Znth i weights (0 : Int))))
  ** (intArray.missing_i w_pre i (0 : Int) n_pre weights)

noncomputable def solver_partial_solve_wit_2_pure : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH10 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr |-> (w_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full w_pre n_pre weights)
  ** (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
|--
  “ ((0 : Int) <= (sizeof(CHAR) * 205)) ” &&
  “ ((sizeof(CHAR) * 205) < INT_MAX) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 127) ”

noncomputable def solver_partial_solve_wit_2_aux : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) (PreH9 : ((0 : Int) <= (sizeof(CHAR) * 205))) (PreH10 : ((sizeof(CHAR) * 205) < INT_MAX)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
|--
  “ ((0 : Int) <= (sizeof(CHAR) * 205)) ” &&
  “ ((sizeof(CHAR) * 205) < INT_MAX) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 127) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= (sizeof(CHAR) * 205)) ” &&
  “ ((sizeof(CHAR) * 205) < INT_MAX) ”
  &&  (charArray.undef_full (( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR))) (sizeof(CHAR) * 205))
  ** (intArray.full w_pre n_pre weights)

noncomputable def solver_partial_solve_wit_2 : Prop := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : (PrefixUnitTotal weights n_pre total)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 (repeat_Z ((0 : Int)) (205)))
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ”
  &&  (((( &( "reach" ) ) + ((0 : Int) * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i ( &( "reach" ) ) (0 : Int) (0 : Int) 205 (repeat_Z ((0 : Int)) (205)))
  ** (intArray.full w_pre n_pre weights)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (i : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (ReachTable weights i total reach_l)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ (i < n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (ReachTable weights i total reach_l) ”
  &&  (((w_pre + (i * sizeof(INT)))) # Int |-> ((Znth i weights (0 : Int))))
  ** (intArray.missing_i w_pre i (0 : Int) n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l)) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ (s >= u) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (u = (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ (1 <= u) ” &&
  “ (u <= 2) ” &&
  “ ((u - 1) <= s) ” &&
  “ (s <= total) ” &&
  “ (ReachInnerProgress weights i s total reach_l) ”
  &&  (((( &( "reach" ) ) + ((s - u) * sizeof(CHAR)))) # Char |-> ((Znth (s - u) reach_l (0 : Int))))
  ** (charArray.missing_i ( &( "reach" ) ) (s - u) (0 : Int) 205 reach_l)
  ** (intArray.full w_pre n_pre weights)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (s : Int) (u : Int) (i : Int) (total : Int) (PreH1 : (s >= u)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH3 : (n_pre = (Zlength (weights)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Z.rem total 2) = (0 : Int))) (PreH9 : (PrefixUnitTotal weights n_pre total)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (u = (Z.quot (Znth i weights (0 : Int)) 100))) (PreH13 : (1 <= u)) (PreH14 : (u <= 2)) (PreH15 : ((u - 1) <= s)) (PreH16 : (s <= total)) (PreH17 : (ReachInnerProgress weights i s total reach_l)) (PreH18 : ((Znth (s - u) reach_l (0 : Int)) ≠ (0 : Int))) ,
  (charArray.full ( &( "reach" ) ) 205 reach_l)
  ** (intArray.full w_pre n_pre weights)
|--
  “ (s >= u) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (u = (Z.quot (Znth i weights (0 : Int)) 100)) ” &&
  “ (1 <= u) ” &&
  “ (u <= 2) ” &&
  “ ((u - 1) <= s) ” &&
  “ (s <= total) ” &&
  “ (ReachInnerProgress weights i s total reach_l) ” &&
  “ ((Znth (s - u) reach_l (0 : Int)) ≠ (0 : Int)) ”
  &&  (((( &( "reach" ) ) + (s * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i ( &( "reach" ) ) s (0 : Int) 205 reach_l)
  ** (intArray.full w_pre n_pre weights)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (weights : (List Int)) (w_pre : Int) (n_pre : Int) (reach_l : (List Int)) (total : Int) (PreH1 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200)))) (PreH2 : (n_pre = (Zlength (weights)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : ((0 : Int) <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Z.rem total 2) = (0 : Int))) (PreH8 : ((0 : Int) <= (Z.quot total 2))) (PreH9 : ((Z.quot total 2) < 205)) (PreH10 : (PrefixUnitTotal weights n_pre total)) (PreH11 : (ReachTable weights n_pre total reach_l)) (PreH12 : (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int)))) (PreH13 : (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int)))) ,
  (intArray.full w_pre n_pre weights)
  ** (charArray.full ( &( "reach" ) ) 205 reach_l)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> (((Znth j weights (0 : Int)) = 100) ∨ ((Znth j weights (0 : Int)) = 200))) ” &&
  “ (n_pre = (Zlength (weights))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Z.rem total 2) = (0 : Int)) ” &&
  “ ((0 : Int) <= (Z.quot total 2)) ” &&
  “ ((Z.quot total 2) < 205) ” &&
  “ (PrefixUnitTotal weights n_pre total) ” &&
  “ (ReachTable weights n_pre total reach_l) ” &&
  “ (Spec weights (Znth (Z.quot total 2) reach_l (0 : Int))) ” &&
  “ (SolverReturnBridge (Znth (Z.quot total 2) reach_l (0 : Int)) (Znth (Z.quot total 2) reach_l (0 : Int))) ”
  &&  (((( &( "reach" ) ) + ((Z.quot total 2) * sizeof(CHAR)))) # Char |-> ((Znth (Z.quot total 2) reach_l (0 : Int))))
  ** (charArray.missing_i ( &( "reach" ) ) (Z.quot total 2) (0 : Int) 205 reach_l)
  ** (intArray.full w_pre n_pre weights)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9 : solver_entail_wit_9
  proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1
  proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2
  proof_of_solver_entail_wit_11 : solver_entail_wit_11
  proof_of_solver_entail_wit_12 : solver_entail_wit_12
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_goal
