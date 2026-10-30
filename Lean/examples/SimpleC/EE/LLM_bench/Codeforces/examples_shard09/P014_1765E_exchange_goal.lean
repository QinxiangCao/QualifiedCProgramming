import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P014_1765E_exchange_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ ((((n_pre + a_pre) - 1) ≠ (-9223372036854775808)) ∨ (a_pre ≠ (-1))) ” &&
  “ (a_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ (((n_pre + a_pre) - 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((n_pre + a_pre) - 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ ((n_pre + a_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (n_pre + a_pre)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  ((( &( "n" ) )) # Int64 |-> (n_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre (Z.quot ((n_pre + a_pre) - 1) a_pre)) ”
  &&  emp
) \/
(
forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre (Z.quot ((n_pre + a_pre) - 1) a_pre)) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  (Spec n_pre a_pre b_pre (Z.quot ((n_pre + a_pre) - 1) a_pre))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre 1) ”
  &&  emp
) \/
(
forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre 1) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)) ,
  (Spec n_pre a_pre b_pre 1)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_goal
