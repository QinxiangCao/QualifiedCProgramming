import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P022_705B_spider_man_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def next_parity_safety_wit_1 : Prop :=
  forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int |-> (par_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
|--
  “ ((par_pre + (a_pre - 1)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (par_pre + (a_pre - 1))) ”

noncomputable def next_parity_safety_wit_2 : Prop :=
  forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int |-> (par_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
|--
  “ ((a_pre - 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a_pre - 1)) ”

noncomputable def next_parity_safety_wit_3 : Prop :=
  forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int |-> (par_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def next_parity_safety_wit_4 : Prop :=
  forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int |-> (par_pre))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def next_parity_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (NextParity par_pre a_pre (Z.land (par_pre + (a_pre - 1)) 1)) ”
  &&  emp
) \/
(
forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (NextParity par_pre a_pre (Z.land (par_pre + (a_pre - 1)) 1)) ”
  &&  emp
)

noncomputable def next_parity_return_wit_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (par_pre : Int) (PreH1 : ((0 : Int) <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  (NextParity par_pre a_pre (Z.land (par_pre + (a_pre - 1)) 1))

noncomputable def solver_safety_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  ((( &( "par" ) )) # Int |->_)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.full added_pre n_pre added_values)
  ** (intArray.full_shape out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "par" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.full added_pre n_pre added_values)
  ** (intArray.full_shape out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (retval))
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (retval))
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (intArray.full out_pre (i + 1) (written ++ (1 :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (retval))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (intArray.full out_pre (i + 1) (written ++ (2 :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (retval))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full_shape out_pre n_pre)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) ((0 : Int)) (added_values)) written (0 : Int)) ”
  &&  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre (0 : Int) written)
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (out_pre : Int) (n_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (intArray.full_shape out_pre n_pre)
|--
  “ (SpiderPrefixState (sublist ((0 : Int)) ((0 : Int)) (added_values)) (@List.nil Int) (0 : Int)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ”
  &&  (intArray.undef_seg out_pre (0 : Int) n_pre)
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (intArray.full_shape out_pre n_pre)
|--
  “ (SpiderPrefixState (sublist ((0 : Int)) ((0 : Int)) (added_values)) (@List.nil Int) (0 : Int)) ”

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (intArray.full_shape out_pre n_pre)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ”

noncomputable def solver_entail_wit_1_split_goal_spatial : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_values : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i added_values (0 : Int))) ∧ ((Znth i added_values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (intArray.full_shape out_pre n_pre)
|--
  (intArray.undef_seg out_pre (0 : Int) n_pre)

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written_2 : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written_2 par)) ,
  (intArray.full out_pre (i + 1) (written_2 ++ (1 :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (int64Array.full added_pre n_pre added_values)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) ((i + 1)) (added_values)) written retval) ”
  &&  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre (i + 1) written)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
) \/
(
forall (n_pre : Int) (added_values : (List Int)) (written_2 : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written_2 par)) ,
  TT && emp 
|--
  “ (SpiderPrefixState (sublist ((0 : Int)) ((i + 1)) (added_values)) (written_2 ++ (1 :: (@List.nil Int))) retval) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (added_values : (List Int)) (written_2 : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written_2 par)) ,
  (SpiderPrefixState (sublist ((0 : Int)) ((i + 1)) (added_values)) (written_2 ++ (1 :: (@List.nil Int))) retval)

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written_2 : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written_2 par)) ,
  (intArray.full out_pre (i + 1) (written_2 ++ (2 :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (int64Array.full added_pre n_pre added_values)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) ((i + 1)) (added_values)) written retval) ”
  &&  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre (i + 1) written)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
) \/
(
forall (n_pre : Int) (added_values : (List Int)) (written_2 : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written_2 par)) ,
  TT && emp 
|--
  “ (SpiderPrefixState (sublist ((0 : Int)) ((i + 1)) (added_values)) (written_2 ++ (2 :: (@List.nil Int))) (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (added_values : (List Int)) (written_2 : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written_2 par)) ,
  (SpiderPrefixState (sublist ((0 : Int)) ((i + 1)) (added_values)) (written_2 ++ (2 :: (@List.nil Int))) (0 : Int))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  EX result : (List Int),
  “ (Spec added_values result) ”
  &&  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre n_pre result)
) \/
(
forall (out_pre : Int) (n_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (intArray.full out_pre i written)
|--
  EX result : (List Int),
  “ (Spec added_values result) ”
  &&  (intArray.full out_pre n_pre result)
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par) ”
  &&  (((added_pre + (i * sizeof(INT64)))) # Int64 |-> ((Znth i added_values (0 : Int))))
  ** (int64Array.missing_i added_pre i (0 : Int) n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)

noncomputable def solver_partial_solve_wit_2_pure : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (par))
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (1 <= (Znth i added_values (0 : Int))) ” &&
  “ ((Znth i added_values (0 : Int)) <= 1000000000) ” &&
  “ (par <= 1) ” &&
  “ ((0 : Int) <= par) ”
) \/
(
forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (par <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (par >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (added_values)))) (PreH11 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (par))
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ ((0 : Int) <= par) ” &&
  “ (par <= 1) ”
)

noncomputable def solver_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (par <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (par >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (added_values)))) (PreH11 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (par))
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ ((0 : Int) <= par) ”

noncomputable def solver_partial_solve_wit_2_pure_split_goal_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (par <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (par >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (added_values)))) (PreH11 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** ((( &( "added" ) )) # Ptr |-> (added_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "par" ) )) # Int |-> (par))
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (par <= 1) ”

noncomputable def solver_partial_solve_wit_2_aux : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (1 <= (Znth i added_values (0 : Int))) ” &&
  “ ((Znth i added_values (0 : Int)) <= 1000000000) ” &&
  “ (par <= 1) ” &&
  “ ((0 : Int) <= par) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par) ”
  &&  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)

noncomputable def solver_partial_solve_wit_2 : Prop := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (retval ≠ (0 : Int)) ” &&
  “ (NextParity par (Znth i added_values (0 : Int)) retval) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (added_pre : Int) (added_values : (List Int)) (written : (List Int)) (par : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (NextParity par (Znth i added_values (0 : Int)) retval)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par)) ,
  (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (retval = (0 : Int)) ” &&
  “ (NextParity par (Znth i added_values (0 : Int)) retval) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (added_values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((1 <= (Znth j added_values (0 : Int))) ∧ ((Znth j added_values (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (SpiderPrefixState (sublist ((0 : Int)) (i) (added_values)) written par) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (int64Array.full added_pre n_pre added_values)
  ** (intArray.full out_pre i written)


structure VC_Correct : Type where
  proof_of_next_parity_safety_wit_1 : next_parity_safety_wit_1
  proof_of_next_parity_safety_wit_2 : next_parity_safety_wit_2
  proof_of_next_parity_safety_wit_3 : next_parity_safety_wit_3
  proof_of_next_parity_safety_wit_4 : next_parity_safety_wit_4
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_next_parity_return_wit_1 : next_parity_return_wit_1
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_goal
