import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P003_1438A_specific_tastes_of_andre_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (n_pre : Int) (out_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (out_pre : Int) (written : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1))) ,
  (intArray.seg out_pre (0 : Int) (i + 1) (written ++ (1 :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (out_pre : Int) (written : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (out_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  (intArray.undef_full out_pre n_pre)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((Zlength (written)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k written (0 : Int)) = 1)) ”
  &&  (intArray.seg out_pre (0 : Int) (0 : Int) written)
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = 1)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = 1))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (out_pre : Int) (written_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written_2 (0 : Int)) = 1))) ,
  (intArray.seg out_pre (0 : Int) (i + 1) (written_2 ++ (1 :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (written)) = (i + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (i + 1))) -> ((Znth k written (0 : Int)) = 1)) ”
  &&  (intArray.seg out_pre (0 : Int) (i + 1) written)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
) \/
(
forall (n_pre : Int) (written_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written_2 (0 : Int)) = 1))) ,
  TT && emp 
|--
  “ ((Zlength ((written_2 ++ (1 :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (written_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written_2 (0 : Int)) = 1))) ,
  ((Zlength ((written_2 ++ (1 :: (@List.nil Int))))) = (i + 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (out_pre : Int) (written : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1))) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  EX out_spec : (List Int),
  “ (Spec n_pre out_spec) ”
  &&  (intArray.full out_pre n_pre out_spec)
) \/
(
forall (n_pre : Int) (written : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1))) ,
  TT && emp 
|--
  “ (Spec n_pre written) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (written : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1))) ,
  (Spec n_pre written)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (out_pre : Int) (written : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1))) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (written)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k written (0 : Int)) = 1)) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (intArray.seg out_pre (0 : Int) i written)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_goal
