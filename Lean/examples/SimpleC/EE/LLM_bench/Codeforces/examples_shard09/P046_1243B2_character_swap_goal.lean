import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P046_1243B2_character_swap_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i source (0 : Int))) ∧ ((Znth i source (0 : Int)) <= 122)))) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target (0 : Int))) ∧ ((Znth i_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full ( &( "cnt" ) ) 26 (repeat_Z ((0 : Int)) (26)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (((Znth i source (0 : Int)) - 97) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i source (0 : Int)) - 97)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (97 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 97) ”

noncomputable def solver_safety_wit_4 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) ”
) \/
(
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) ”
)

noncomputable def solver_safety_wit_4_split_goal_1 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_4_split_goal_2 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ ((INT_MIN) <= ((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full t_pre n_pre target)
  ** (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth i target (0 : Int)) - 97) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i target (0 : Int)) - 97)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full t_pre n_pre target)
  ** (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (97 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 97) ”

noncomputable def solver_safety_wit_7 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1)) ”
) \/
(
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1)) ”
)

noncomputable def solver_safety_wit_7_split_goal_1 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_7_split_goal_2 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ ((INT_MIN) <= ((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i target (0 : Int)) - 97)) (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int)) + 1)) ((replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  ((( &( "c" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : ((0 : Int) <= c)) (PreH9 : (c <= 26)) (PreH10 : (CountedPrefix source target n_pre counts)) (PreH11 : (CountsEvenBefore counts c)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (26 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 26) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts)) (PreH12 : (CountsEvenBefore counts c)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (((Znth c counts (0 : Int)) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts)) (PreH12 : (CountsEvenBefore counts c)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts)) (PreH9 : (CombinedOddAt source target c)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts)) (PreH9 : (CombinedOddAt source target c)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts)) (PreH12 : (CountsEvenBefore counts c)) (PreH13 : ((Z.rem (Znth c counts (0 : Int)) 2) = (0 : Int))) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts)) (PreH9 : (CombinedEven source target)) ,
  ((( &( "m" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts)) (PreH9 : (CombinedEven source target)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "m" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops)))) (PreH15 : (OperationLists ops is js)) (PreH16 : (RepairState source target ss tt i ops)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (charArray.full t_pre n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops)))) (PreH15 : (OperationLists ops is js)) (PreH16 : (RepairState source target ss tt i ops)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (charArray.full t_pre n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : ((Znth j ss (0 : Int)) ≠ (Znth i ss (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js)) (PreH20 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js)) (PreH20 : (RepairState source target ss tt i ops)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ False ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ False ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (intArray.full oj_pre (m + 1) (js ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((m + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (m + 1)) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js)) (PreH20 : (RepairState source target ss tt i ops)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js)) (PreH20 : (RepairState source target ss tt i ops)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : ((Znth j tt (0 : Int)) ≠ (Znth i ss (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ False ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ False ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j ss (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((m + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (m + 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre ((m + 1) + 1) ((is ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre ((m + 1) + 1) ((is ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_44 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oj_pre ((m + 1) + 1) ((js ++ ((j + 1) :: (@List.nil Int))) ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre ((m + 1) + 1) (2 * n_pre))
  ** (intArray.full oi_pre ((m + 1) + 1) ((is ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (((m + 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((m + 1) + 1)) ”

noncomputable def solver_safety_wit_45 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oj_pre ((m + 1) + 1) ((js ++ ((j + 1) :: (@List.nil Int))) ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre ((m + 1) + 1) (2 * n_pre))
  ** (intArray.full oi_pre ((m + 1) + 1) ((is ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (((m + 1) + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_46 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : ((Znth i ss (0 : Int)) = (Znth i tt (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops)))) (PreH15 : (OperationLists ops is js)) (PreH16 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_47 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (intArray.full oj_pre (m + 1) (js ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "oi" ) )) # Ptr |-> (oi_pre))
  ** ((( &( "oj" ) )) # Ptr |-> (oj_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i source (0 : Int))) ∧ ((Znth i source (0 : Int)) <= 122)))) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target (0 : Int))) ∧ ((Znth i_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) ,
  (intArray.full ( &( "cnt" ) ) 26 (repeat_Z ((0 : Int)) (26)))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  EX counts : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (CountedPrefix source target (0 : Int) counts) ”
  &&  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i source (0 : Int))) ∧ ((Znth i source (0 : Int)) <= 122)))) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target (0 : Int))) ∧ ((Znth i_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) ,
  TT && emp 
|--
  “ (CountedPrefix source target (0 : Int) (repeat_Z ((0 : Int)) (26))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i source (0 : Int))) ∧ ((Znth i source (0 : Int)) <= 122)))) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target (0 : Int))) ∧ ((Znth i_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) ,
  (CountedPrefix source target (0 : Int) (repeat_Z ((0 : Int)) (26)))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i source (0 : Int))) ∧ ((Znth i source (0 : Int)) <= 122)))) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target (0 : Int))) ∧ ((Znth i_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i source (0 : Int))) ∧ ((Znth i source (0 : Int)) <= 122)))) (PreH5 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 target (0 : Int))) ∧ ((Znth i_2 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i target (0 : Int)) - 97)) (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts_2 (0 : Int)) + 1)) (counts_2)) (0 : Int)) + 1)) ((replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts_2 (0 : Int)) + 1)) (counts_2)))))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  EX counts : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (CountedPrefix source target (i + 1) counts) ”
  &&  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  TT && emp 
|--
  “ (CountedPrefix source target (i + 1) (replace_Znth (((Znth i target (0 : Int)) - 97)) (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts_2 (0 : Int)) + 1)) (counts_2)) (0 : Int)) + 1)) ((replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts_2 (0 : Int)) + 1)) (counts_2))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  (CountedPrefix source target (i + 1) (replace_Znth (((Znth i target (0 : Int)) - 97)) (((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts_2 (0 : Int)) + 1)) (counts_2)) (0 : Int)) + 1)) ((replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts_2 (0 : Int)) + 1)) (counts_2)))))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 26) ” &&
  “ (CountedPrefix source target n_pre counts) ” &&
  “ (CountsEvenBefore counts (0 : Int)) ”
  &&  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  TT && emp 
|--
  “ (CountsEvenBefore counts_2 (0 : Int)) ” &&
  “ (CountedPrefix source target n_pre counts_2) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  (CountsEvenBefore counts_2 (0 : Int))

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  (CountedPrefix source target n_pre counts_2)

noncomputable def solver_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_3_split_goal_4 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts_2)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) (PreH13 : ((Z.rem (Znth c counts_2 (0 : Int)) 2) ≠ (0 : Int))) ,
  (intArray.full ( &( "cnt" ) ) 26 counts_2)
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  EX counts : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < 26) ” &&
  “ (CountedPrefix source target n_pre counts) ” &&
  “ (CombinedOddAt source target c) ”
  &&  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) (PreH13 : ((Z.rem (Znth c counts_2 (0 : Int)) 2) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (CombinedOddAt source target c) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) (PreH13 : ((Z.rem (Znth c counts_2 (0 : Int)) 2) ≠ (0 : Int))) ,
  (CombinedOddAt source target c)

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c >= 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ (CountedPrefix source target n_pre counts) ” &&
  “ (CombinedEven source target) ”
  &&  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c >= 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) ,
  TT && emp 
|--
  “ (CombinedEven source target) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c >= 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) ,
  (CombinedEven source target)

noncomputable def solver_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c >= 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_5_split_goal_3 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c >= 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH6 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) (PreH13 : ((Z.rem (Znth c counts_2 (0 : Int)) 2) = (0 : Int))) ,
  (intArray.full ( &( "cnt" ) ) 26 counts_2)
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  EX counts : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= 26) ” &&
  “ (CountedPrefix source target n_pre counts) ” &&
  “ (CountsEvenBefore counts (c + 1)) ”
  &&  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) (PreH13 : ((Z.rem (Znth c counts_2 (0 : Int)) 2) = (0 : Int))) ,
  TT && emp 
|--
  “ (CountsEvenBefore counts_2 (c + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts_2)) (PreH12 : (CountsEvenBefore counts_2 c)) (PreH13 : ((Z.rem (Znth c counts_2 (0 : Int)) 2) = (0 : Int))) ,
  (CountsEvenBefore counts_2 (c + 1))

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH5 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts_2)) (PreH9 : (CombinedEven source target)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (2 * (0 : Int))) ” &&
  “ ((0 : Int) = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt (0 : Int) ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre (0 : Int) is)
  ** (intArray.undef_seg oi_pre (0 : Int) (2 * n_pre))
  ** (intArray.full oj_pre (0 : Int) js)
  ** (intArray.undef_seg oj_pre (0 : Int) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 source (0 : Int))) ∧ ((Znth k_3 source (0 : Int)) <= 122)))) (PreH5 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 target (0 : Int))) ∧ ((Znth k_4 target (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (source)))) (PreH7 : ((Zlength (target)) = n_pre)) (PreH8 : (CountedPrefix source target n_pre counts_2)) (PreH9 : (CombinedEven source target)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (source))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (2 * (0 : Int))) ” &&
  “ ((0 : Int) = (Zlength (ops))) ” &&
  “ (OperationLists ops (@List.nil Int) (@List.nil Int)) ” &&
  “ (RepairState source target source target (0 : Int) ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2)) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (charArray.full t_pre n_pre tt_2)
  ** (charArray.full s_pre n_pre ss_2)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) (i + 1)) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2)) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (source))) ” &&
  “ (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) (i + 1)) ” &&
  “ ((Zlength (ops_2)) = (Zlength (ops))) ” &&
  “ (OperationLists ops is_2 js_2) ” &&
  “ (RepairState source target ss_2 tt_2 i ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_9 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth j ss_2 (0 : Int)) ≠ (Znth i ss_2 (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss_2 (0 : Int))) ∧ ((Znth k ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 (0 : Int))) ∧ ((Znth k_2 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2)) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (charArray.full s_pre n_pre ss_2)
  ** (charArray.full t_pre n_pre tt_2)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) (j + 1)) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth j ss_2 (0 : Int)) ≠ (Znth i ss_2 (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss_2 (0 : Int))) ∧ ((Znth k ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 (0 : Int))) ∧ ((Znth k_2 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2)) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= (Zlength (source))) ” &&
  “ (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) (j + 1)) ” &&
  “ ((Zlength (ops_2)) = (Zlength (ops))) ” &&
  “ (OperationLists ops is_2 js_2) ” &&
  “ (RepairState source target ss_2 tt_2 i ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_10 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2)) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (charArray.full s_pre n_pre ss_2)
  ** (charArray.full t_pre n_pre tt_2)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) (i + 1)) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops_2)))) (PreH19 : (OperationLists ops_2 is_2 js_2)) (PreH20 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (source))) ” &&
  “ (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) (Zlength (source))) ” &&
  “ (NoValueInRange tt_2 (Znth i ss_2 (0 : Int)) (i + 1) (i + 1)) ” &&
  “ ((Zlength (ops_2)) = (Zlength (ops))) ” &&
  “ (OperationLists ops is_2 js_2) ” &&
  “ (RepairState source target ss_2 tt_2 i ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_11 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth j tt_2 (0 : Int)) ≠ (Znth i ss_2 (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss_2 (0 : Int))) ∧ ((Znth k ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 (0 : Int))) ∧ ((Znth k_2 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2)) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (charArray.full s_pre n_pre ss_2)
  ** (charArray.full t_pre n_pre tt_2)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) (j + 1)) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth j tt_2 (0 : Int)) ≠ (Znth i ss_2 (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss_2 (0 : Int))) ∧ ((Znth k ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 (0 : Int))) ∧ ((Znth k_2 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH15 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2)) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= (Zlength (source))) ” &&
  “ (NoValueInRange tt_2 (Znth i ss_2 (0 : Int)) (i + 1) (j + 1)) ” &&
  “ ((Zlength (ops_2)) = (Zlength (ops))) ” &&
  “ (OperationLists ops is_2 js_2) ” &&
  “ (RepairState source target ss_2 tt_2 i ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_1 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt_2 (0 : Int)) = (Znth i ss_2 (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH8 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops_2)))) (PreH21 : (OperationLists ops_2 is_2 js_2)) (PreH22 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (intArray.full oj_pre ((m + 1) + 1) ((js_2 ++ ((j + 1) :: (@List.nil Int))) ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre ((m + 1) + 1) (2 * n_pre))
  ** (intArray.full oi_pre ((m + 1) + 1) ((is_2 ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)) (0 : Int))) ((replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)) (0 : Int))) ((replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)))))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= ((m + 1) + 1)) ” &&
  “ (((m + 1) + 1) <= (2 * (i + 1))) ” &&
  “ (((m + 1) + 1) = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt (i + 1) ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre ((m + 1) + 1) is)
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (intArray.full oj_pre ((m + 1) + 1) js)
  ** (intArray.undef_seg oj_pre ((m + 1) + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt_2 (0 : Int)) = (Znth i ss_2 (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH8 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops_2)))) (PreH21 : (OperationLists ops_2 is_2 js_2)) (PreH22 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (source)))) -> ((97 <= (Znth k (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)) (0 : Int))) ((replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)))) (0 : Int))) ∧ ((Znth k (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)) (0 : Int))) ((replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)))) (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (source)))) -> ((97 <= (Znth k_2 (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)) (0 : Int))) ((replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)))) (0 : Int))) ∧ ((Znth k_2 (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)) (0 : Int))) ((replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)))) (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (source))) ” &&
  “ ((0 : Int) <= (((Zlength (ops_2)) + 1) + 1)) ” &&
  “ ((((Zlength (ops_2)) + 1) + 1) <= (2 * (i + 1))) ” &&
  “ ((((Zlength (ops_2)) + 1) + 1) = (Zlength (ops))) ” &&
  “ (OperationLists ops ((is_2 ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))) ((js_2 ++ ((j + 1) :: (@List.nil Int))) ++ ((i + 1) :: (@List.nil Int)))) ” &&
  “ (RepairState source target (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)) (0 : Int))) ((replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)))) (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt_2 (0 : Int))) (ss_2)) (0 : Int))) ((replace_Znth (j) ((Znth j ss_2 (0 : Int))) (tt_2)))) (i + 1) ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_2 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth i ss_2 (0 : Int)) = (Znth i tt_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss_2 (0 : Int))) ∧ ((Znth k ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 (0 : Int))) ∧ ((Znth k_2 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2)) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (charArray.full t_pre n_pre tt_2)
  ** (charArray.full s_pre n_pre ss_2)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * (i + 1))) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt (i + 1) ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : ((Znth i ss_2 (0 : Int)) = (Znth i tt_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss_2 (0 : Int))) ∧ ((Znth k ss_2 (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt_2 (0 : Int))) ∧ ((Znth k_2 tt_2 (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= m)) (PreH13 : (m <= (2 * i))) (PreH14 : (m = (Zlength (ops_2)))) (PreH15 : (OperationLists ops_2 is_2 js_2)) (PreH16 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (source))) ” &&
  “ ((Zlength (ops_2)) <= (2 * (i + 1))) ” &&
  “ ((Zlength (ops_2)) = (Zlength (ops))) ” &&
  “ (OperationLists ops is_2 js_2) ” &&
  “ (RepairState source target ss_2 tt_2 (i + 1) ops) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_3 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts_2 : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss_2 (0 : Int)) = (Znth i ss_2 (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH8 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2)) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  (intArray.full oj_pre (m + 1) (js_2 ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is_2 ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss_2 (0 : Int))) (tt_2)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt_2 (0 : Int))) (ss_2)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts_2)
|--
  EX counts : (List Int), EX is : (List Int), EX js : (List Int), EX ops : (List (Int × Int)), EX tt : (List Int), EX ss : (List Int),
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (m + 1)) ” &&
  “ ((m + 1) <= (2 * (i + 1))) ” &&
  “ ((m + 1) = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt (i + 1) ops) ”
  &&  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre (m + 1) is)
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full oj_pre (m + 1) js)
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
) \/
(
forall (n_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt_2 : (List Int)) (ss_2 : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss_2 (0 : Int)) = (Znth i ss_2 (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((97 <= (Znth k_3 ss_2 (0 : Int))) ∧ ((Znth k_3 ss_2 (0 : Int)) <= 122)))) (PreH8 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < n_pre)) -> ((97 <= (Znth k_4 tt_2 (0 : Int))) ∧ ((Znth k_4 tt_2 (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss_2 (0 : Int)) ≠ (Znth i tt_2 (0 : Int)))) (PreH16 : (NoValueInRange ss_2 (Znth i ss_2 (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2)) (PreH21 : (RepairState source target ss_2 tt_2 i ops_2)) ,
  TT && emp 
|--
  EX ops : (List (Int × Int)),
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (source)))) -> ((97 <= (Znth k (replace_Znth (j) ((Znth i tt_2 (0 : Int))) (ss_2)) (0 : Int))) ∧ ((Znth k (replace_Znth (j) ((Znth i tt_2 (0 : Int))) (ss_2)) (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (source)))) -> ((97 <= (Znth k_2 (replace_Znth (i) ((Znth j ss_2 (0 : Int))) (tt_2)) (0 : Int))) ∧ ((Znth k_2 (replace_Znth (i) ((Znth j ss_2 (0 : Int))) (tt_2)) (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (source))) ” &&
  “ ((0 : Int) <= ((Zlength (ops_2)) + 1)) ” &&
  “ (((Zlength (ops_2)) + 1) <= (2 * (i + 1))) ” &&
  “ (((Zlength (ops_2)) + 1) = (Zlength (ops))) ” &&
  “ (OperationLists ops (is_2 ++ ((j + 1) :: (@List.nil Int))) (js_2 ++ ((i + 1) :: (@List.nil Int)))) ” &&
  “ (RepairState source target (replace_Znth (j) ((Znth i tt_2 (0 : Int))) (ss_2)) (replace_Znth (i) ((Znth j ss_2 (0 : Int))) (tt_2)) (i + 1) ops) ”
  &&  emp
)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= m)) (PreH12 : (m <= (2 * i))) (PreH13 : (m = (Zlength (ops_2)))) (PreH14 : (OperationLists ops_2 is_2 js_2)) (PreH15 : (RepairState source target ss tt i ops_2)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
|--
  EX js : (List Int), EX is : (List Int), EX ops : (List (Int × Int)), EX out : (Option (List (Int × Int))),
  “ (Spec source target out) ” &&
  “ (out = (Some (ops))) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (1 <= (Zlength (ops))) ” &&
  “ ((Zlength (ops)) <= (2 * n_pre)) ” &&
  “ ((Zlength (is)) = (Zlength (ops))) ” &&
  “ ((Zlength (js)) = (Zlength (ops))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (ops)))) -> (((Znth q is (0 : Int)) = ((fst ((Znth q ops __default__Prod_Z_Z))) + 1)) ∧ ((Znth q js (0 : Int)) = ((snd ((Znth q ops __default__Prod_Z_Z))) + 1)))) ”
  &&  (charArray.full_shape s_pre n_pre)
  ** (charArray.full_shape t_pre n_pre)
  ** (intArray.full oi_pre (Zlength (ops)) is)
  ** (intArray.undef_seg oi_pre (Zlength (ops)) (2 * n_pre))
  ** (intArray.full oj_pre (Zlength (ops)) js)
  ** (intArray.undef_seg oj_pre (Zlength (ops)) (2 * n_pre))
) \/
(
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i >= n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= m)) (PreH12 : (m <= (2 * i))) (PreH13 : (m = (Zlength (ops_2)))) (PreH14 : (OperationLists ops_2 is_2 js_2)) (PreH15 : (RepairState source target ss tt i ops_2)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
|--
  EX js : (List Int), EX is : (List Int), EX ops : (List (Int × Int)),
  “ (Spec source target (Some (ops))) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (1 <= (Zlength (ops))) ” &&
  “ ((Zlength (ops)) <= (2 * n_pre)) ” &&
  “ ((Zlength (is)) = (Zlength (ops))) ” &&
  “ ((Zlength (js)) = (Zlength (ops))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < (Zlength (ops)))) -> (((Znth q is (0 : Int)) = ((fst ((Znth q ops __default__Prod_Z_Z))) + 1)) ∧ ((Znth q js (0 : Int)) = ((snd ((Znth q ops __default__Prod_Z_Z))) + 1)))) ”
  &&  (charArray.full_shape s_pre n_pre)
  ** (charArray.full_shape t_pre n_pre)
  ** (intArray.full oi_pre (Zlength (ops)) is)
  ** (intArray.undef_seg oi_pre (Zlength (ops)) (2 * n_pre))
  ** (intArray.full oj_pre (Zlength (ops)) js)
  ** (intArray.undef_seg oj_pre (Zlength (ops)) (2 * n_pre))
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2)) (PreH21 : (RepairState source target ss tt i ops_2)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
|--
  EX oj_cells : (List (Option Int)), EX oi_cells : (List (Option Int)), EX out : (Option (List (Int × Int))),
  “ (Spec source target out) ” &&
  “ (out = None) ” &&
  “ ((-1) = (-1)) ”
  &&  (charArray.full_shape s_pre n_pre)
  ** (charArray.full_shape t_pre n_pre)
  ** (intArray.mixed_full oi_pre (2 * n_pre) oi_cells)
  ** (intArray.mixed_full oj_pre (2 * n_pre) oj_cells)
) \/
(
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (is_2 : (List Int)) (js_2 : (List Int)) (ops_2 : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j >= n_pre)) (PreH2 : (j >= n_pre)) (PreH3 : (Pre source target)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH7 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH8 : (n_pre = (Zlength (source)))) (PreH9 : ((Zlength (target)) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH15 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH16 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops_2)))) (PreH20 : (OperationLists ops_2 is_2 js_2)) (PreH21 : (RepairState source target ss tt i ops_2)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is_2)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js_2)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
|--
  EX oj_cells : (List (Option Int)), EX oi_cells : (List (Option Int)),
  “ (Spec source target None) ”
  &&  (charArray.full_shape s_pre n_pre)
  ** (charArray.full_shape t_pre n_pre)
  ** (intArray.mixed_full oi_pre (2 * n_pre) oi_cells)
  ** (intArray.mixed_full oj_pre (2 * n_pre) oj_cells)
)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts)) (PreH9 : (CombinedOddAt source target c)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  EX oj_cells : (List (Option Int)), EX oi_cells : (List (Option Int)), EX out : (Option (List (Int × Int))),
  “ (Spec source target out) ” &&
  “ (out = None) ” &&
  “ ((-1) = (-1)) ”
  &&  (charArray.full_shape s_pre n_pre)
  ** (charArray.full_shape t_pre n_pre)
  ** (intArray.mixed_full oi_pre (2 * n_pre) oi_cells)
  ** (intArray.mixed_full oj_pre (2 * n_pre) oj_cells)
) \/
(
forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (Pre source target)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : ((Zlength (target)) = n_pre)) (PreH6 : ((0 : Int) <= c)) (PreH7 : (c < 26)) (PreH8 : (CountedPrefix source target n_pre counts)) (PreH9 : (CombinedOddAt source target c)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  EX oj_cells : (List (Option Int)), EX oi_cells : (List (Option Int)),
  “ (Spec source target None) ”
  &&  (charArray.full_shape s_pre n_pre)
  ** (charArray.full_shape t_pre n_pre)
  ** (intArray.mixed_full oi_pre (2 * n_pre) oi_cells)
  ** (intArray.mixed_full oj_pre (2 * n_pre) oj_cells)
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountedPrefix source target i counts) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i source (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountedPrefix source target i counts) ”
  &&  (((( &( "cnt" ) ) + (((Znth i source (0 : Int)) - 97) * sizeof(INT)))) # Int |-> ((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int))))
  ** (intArray.missing_i ( &( "cnt" ) ) ((Znth i source (0 : Int)) - 97) (0 : Int) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountedPrefix source target i counts) ”
  &&  (((( &( "cnt" ) ) + (((Znth i source (0 : Int)) - 97) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "cnt" ) ) ((Znth i source (0 : Int)) - 97) (0 : Int) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountedPrefix source target i counts) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i target (0 : Int))))
  ** (charArray.missing_i t_pre i (0 : Int) n_pre target)
  ** (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full s_pre n_pre source)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (charArray.full t_pre n_pre target)
  ** (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full s_pre n_pre source)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountedPrefix source target i counts) ”
  &&  (((( &( "cnt" ) ) + (((Znth i target (0 : Int)) - 97) * sizeof(INT)))) # Int |-> ((Znth ((Znth i target (0 : Int)) - 97) (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)) (0 : Int))))
  ** (intArray.missing_i ( &( "cnt" ) ) ((Znth i target (0 : Int)) - 97) (0 : Int) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CountedPrefix source target i counts)) ,
  (intArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountedPrefix source target i counts) ”
  &&  (((( &( "cnt" ) ) + (((Znth i target (0 : Int)) - 97) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "cnt" ) ) ((Znth i target (0 : Int)) - 97) (0 : Int) 26 (replace_Znth (((Znth i source (0 : Int)) - 97)) (((Znth ((Znth i source (0 : Int)) - 97) counts (0 : Int)) + 1)) (counts)))
  ** (charArray.full t_pre n_pre target)
  ** (charArray.full s_pre n_pre source)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (c : Int) (PreH1 : (c < 26)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= c)) (PreH10 : (c <= 26)) (PreH11 : (CountedPrefix source target n_pre counts)) (PreH12 : (CountsEvenBefore counts c)) ,
  (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (c < 26) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k source (0 : Int))) ∧ ((Znth k source (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 target (0 : Int))) ∧ ((Znth k_2 target (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= 26) ” &&
  “ (CountedPrefix source target n_pre counts) ” &&
  “ (CountsEvenBefore counts c) ”
  &&  (((( &( "cnt" ) ) + (c * sizeof(INT)))) # Int |-> ((Znth c counts (0 : Int))))
  ** (intArray.missing_i ( &( "cnt" ) ) c (0 : Int) 26 counts)
  ** (charArray.full s_pre n_pre source)
  ** (charArray.full t_pre n_pre target)
  ** (intArray.undef_full oi_pre (2 * n_pre))
  ** (intArray.undef_full oj_pre (2 * n_pre))

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= m)) (PreH12 : (m <= (2 * i))) (PreH13 : (m = (Zlength (ops)))) (PreH14 : (OperationLists ops is js)) (PreH15 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i ss (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= m)) (PreH12 : (m <= (2 * i))) (PreH13 : (m = (Zlength (ops)))) (PreH14 : (OperationLists ops is js)) (PreH15 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (i < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i tt (0 : Int))))
  ** (charArray.missing_i t_pre i (0 : Int) n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH14 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH15 : ((0 : Int) <= m)) (PreH16 : (m <= (2 * i))) (PreH17 : (m = (Zlength (ops)))) (PreH18 : (OperationLists ops is js)) (PreH19 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j ss (0 : Int))))
  ** (charArray.missing_i s_pre j (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH14 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH15 : ((0 : Int) <= m)) (PreH16 : (m <= (2 * i))) (PreH17 : (m = (Zlength (ops)))) (PreH18 : (OperationLists ops is js)) (PreH19 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i ss (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j ss (0 : Int))))
  ** (charArray.missing_i s_pre j (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i tt (0 : Int))))
  ** (charArray.missing_i t_pre i (0 : Int) n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i s_pre j (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_15 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i t_pre i (0 : Int) n_pre tt)
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((oi_pre + (m * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** (intArray.full oi_pre m is)
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_17 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j)) (PreH17 : ((0 : Int) <= m)) (PreH18 : (m <= (2 * i))) (PreH19 : (m = (Zlength (ops)))) (PreH20 : (OperationLists ops is js)) (PreH21 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j ss (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((oj_pre + (m * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre m js)
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_18 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH14 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH15 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js)) (PreH20 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j tt (0 : Int))))
  ** (charArray.missing_i t_pre j (0 : Int) n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_19 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : (Pre source target)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (source)))) (PreH8 : ((Zlength (target)) = n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH14 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH15 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH16 : ((0 : Int) <= m)) (PreH17 : (m <= (2 * i))) (PreH18 : (m = (Zlength (ops)))) (PreH19 : (OperationLists ops is js)) (PreH20 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i ss (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_20 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j ss (0 : Int))))
  ** (charArray.missing_i s_pre j (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_21 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j tt (0 : Int))))
  ** (charArray.missing_i t_pre j (0 : Int) n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_22 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre tt)
  ** (charArray.full s_pre n_pre ss)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i s_pre j (0 : Int) n_pre ss)
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_23 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (charArray.full t_pre n_pre tt)
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i t_pre j (0 : Int) n_pre tt)
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_24 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oi_pre m is)
  ** (intArray.undef_seg oi_pre m (2 * n_pre))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((oi_pre + (m * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oi_pre m is)
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_25 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre m js)
  ** (intArray.undef_seg oj_pre m (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((oj_pre + (m * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre m js)
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_26 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))))
  ** (charArray.missing_i s_pre j (0 : Int) n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_27 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))))
  ** (charArray.missing_i t_pre i (0 : Int) n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_28 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((s_pre + (j * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i s_pre j (0 : Int) n_pre (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_29 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (charArray.full t_pre n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i t_pre i (0 : Int) n_pre (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_30 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((oi_pre + ((m + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full oi_pre (m + 1) (is ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)

noncomputable def solver_partial_solve_wit_31 : Prop :=
  forall (oj_pre : Int) (oi_pre : Int) (n_pre : Int) (t_pre : Int) (s_pre : Int) (target : (List Int)) (source : (List Int)) (counts : (List Int)) (is : (List Int)) (js : (List Int)) (ops : (List (Int × Int))) (m : Int) (j : Int) (i : Int) (tt : (List Int)) (ss : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int)))) (PreH3 : (j < n_pre)) (PreH4 : (Pre source target)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122)))) (PreH9 : (n_pre = (Zlength (source)))) (PreH10 : ((Zlength (target)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int)))) (PreH16 : (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre)) (PreH17 : (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j)) (PreH18 : ((0 : Int) <= m)) (PreH19 : (m <= (2 * i))) (PreH20 : (m = (Zlength (ops)))) (PreH21 : (OperationLists ops is js)) (PreH22 : (RepairState source target ss tt i ops)) ,
  (intArray.full oi_pre ((m + 1) + 1) ((is ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oj_pre (m + 1) (2 * n_pre))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)
|--
  “ (j < n_pre) ” &&
  “ ((Znth j tt (0 : Int)) = (Znth i ss (0 : Int))) ” &&
  “ (j < n_pre) ” &&
  “ (Pre source target) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 50) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((97 <= (Znth k ss (0 : Int))) ∧ ((Znth k ss (0 : Int)) <= 122))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((97 <= (Znth k_2 tt (0 : Int))) ∧ ((Znth k_2 tt (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (source))) ” &&
  “ ((Zlength (target)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((Znth i ss (0 : Int)) ≠ (Znth i tt (0 : Int))) ” &&
  “ (NoValueInRange ss (Znth i ss (0 : Int)) (i + 1) n_pre) ” &&
  “ (NoValueInRange tt (Znth i ss (0 : Int)) (i + 1) j) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= (2 * i)) ” &&
  “ (m = (Zlength (ops))) ” &&
  “ (OperationLists ops is js) ” &&
  “ (RepairState source target ss tt i ops) ”
  &&  (((oj_pre + ((m + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg oj_pre ((m + 1) + 1) (2 * n_pre))
  ** (intArray.full oi_pre ((m + 1) + 1) ((is ++ ((j + 1) :: (@List.nil Int))) ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg oi_pre ((m + 1) + 1) (2 * n_pre))
  ** (charArray.full t_pre n_pre (replace_Znth (i) ((Znth j (replace_Znth (j) ((Znth j tt (0 : Int))) (ss)) (0 : Int))) ((replace_Znth (j) ((Znth j ss (0 : Int))) (tt)))))
  ** (charArray.full s_pre n_pre (replace_Znth (j) ((Znth i (replace_Znth (j) ((Znth j ss (0 : Int))) (tt)) (0 : Int))) ((replace_Znth (j) ((Znth j tt (0 : Int))) (ss)))))
  ** (intArray.full oj_pre (m + 1) (js ++ ((j + 1) :: (@List.nil Int))))
  ** (intArray.full ( &( "cnt" ) ) 26 counts)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
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
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18
  proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19
  proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20
  proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21
  proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22
  proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23
  proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24
  proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25
  proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26
  proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27
  proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28
  proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29
  proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30
  proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9 : solver_entail_wit_9
  proof_of_solver_entail_wit_10 : solver_entail_wit_10
  proof_of_solver_entail_wit_11 : solver_entail_wit_11
  proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1
  proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2
  proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P046_1243B2_character_swap_goal
