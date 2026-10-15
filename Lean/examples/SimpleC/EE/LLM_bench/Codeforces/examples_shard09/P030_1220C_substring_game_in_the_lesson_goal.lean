import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P030_1220C_substring_game_in_the_lesson_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "mn" ) )) # Char |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_full win_pre n_pre)
|--
  “ ((122 + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (122 + 1)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "mn" ) )) # Char |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_full win_pre n_pre)
|--
  “ (122 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 122) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "mn" ) )) # Char |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_full win_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "mn" ) )) # Char |-> ((122 + 1)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_full win_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn < (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ (1 :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "mn" ) )) # Char |-> (mn))
|--
  “ False ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "mn" ) )) # Char |-> ((Znth k text (0 : Int))))
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "mn" ) )) # Char |-> (mn))
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn < (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ (1 :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "win" ) )) # Ptr |-> (win_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "mn" ) )) # Char |-> (mn))
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text (0 : Int))) ∧ ((Znth i_2 text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.undef_full win_pre n_pre)
|--
  EX out : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (PrefixMinimum text (0 : Int) (122 + 1)) ” &&
  “ (SpecPrefix text (0 : Int) out) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (0 : Int) out)
  ** (charArray.undef_seg win_pre (0 : Int) n_pre)
) \/
(
forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text (0 : Int))) ∧ ((Znth i_2 text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  TT && emp 
|--
  “ (SpecPrefix text (0 : Int) (@List.nil Int)) ” &&
  “ (PrefixMinimum text (0 : Int) (122 + 1)) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text (0 : Int))) ∧ ((Znth i_2 text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (SpecPrefix text (0 : Int) (@List.nil Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text (0 : Int))) ∧ ((Znth i_2 text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (PrefixMinimum text (0 : Int) (122 + 1))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text (0 : Int))) ∧ ((Znth i_2 text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
|--
  EX out : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= n_pre) ” &&
  “ (PrefixMinimum text (k + 1) (Znth k text (0 : Int))) ” &&
  “ (SpecPrefix text (k + 1) out) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) out)
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
) \/
(
forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  TT && emp 
|--
  “ (SpecPrefix text (k + 1) (out_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ (PrefixMinimum text (k + 1) (Znth k text (0 : Int))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (SpecPrefix text (k + 1) (out_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_entail_wit_2_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (PrefixMinimum text (k + 1) (Znth k text (0 : Int)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
|--
  EX out : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= n_pre) ” &&
  “ (PrefixMinimum text (k + 1) mn) ” &&
  “ (SpecPrefix text (k + 1) out) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) out)
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
) \/
(
forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  TT && emp 
|--
  “ (SpecPrefix text (k + 1) (out_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ (PrefixMinimum text (k + 1) mn) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (SpecPrefix text (k + 1) (out_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (PrefixMinimum text (k + 1) mn)

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn < (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out_2 ++ (1 :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
|--
  EX out : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= n_pre) ” &&
  “ (PrefixMinimum text (k + 1) mn) ” &&
  “ (SpecPrefix text (k + 1) out) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) out)
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
) \/
(
forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn < (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  TT && emp 
|--
  “ (SpecPrefix text (k + 1) (out_2 ++ (1 :: (@List.nil Int)))) ” &&
  “ (PrefixMinimum text (k + 1) mn) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn < (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (SpecPrefix text (k + 1) (out_2 ++ (1 :: (@List.nil Int))))

noncomputable def solver_entail_wit_2_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) >= mn)) (PreH2 : (mn < (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out_2)) ,
  (PrefixMinimum text (k + 1) mn)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (PrefixMinimum text k mn)) (PreH9 : (SpecPrefix text k out_2)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre k out_2)
  ** (charArray.undef_seg win_pre k n_pre)
|--
  EX out : (List Int),
  “ (Spec text out) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre n_pre out)
) \/
(
forall (win_pre : Int) (n_pre : Int) (text : (List Int)) (out_2 : (List Int)) (mn : Int) (k : Int) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (PrefixMinimum text k mn)) (PreH9 : (SpecPrefix text k out_2)) ,
  (charArray.full win_pre k out_2)
|--
  EX out : (List Int),
  “ (Spec text out) ”
  &&  (charArray.full win_pre n_pre out)
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (PrefixMinimum text k mn)) (PreH9 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre k out)
  ** (charArray.undef_seg win_pre k n_pre)
|--
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (PrefixMinimum text k mn) ” &&
  “ (SpecPrefix text k out) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char |-> ((Znth k text (0 : Int))))
  ** (charArray.missing_i s_pre k (0 : Int) n_pre text)
  ** (charArray.full win_pre k out)
  ** (charArray.undef_seg win_pre k n_pre)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : (mn >= (Znth k text (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : ((0 : Int) <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn)) (PreH10 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre k out)
  ** (charArray.undef_seg win_pre k n_pre)
|--
  “ (mn >= (Znth k text (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (PrefixMinimum text k mn) ” &&
  “ (SpecPrefix text k out) ”
  &&  (((win_pre + (k * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre k out)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : (mn < (Znth k text (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : ((0 : Int) <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn)) (PreH10 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre k out)
  ** (charArray.undef_seg win_pre k n_pre)
|--
  “ (mn < (Znth k text (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (PrefixMinimum text k mn) ” &&
  “ (SpecPrefix text k out) ”
  &&  (((win_pre + (k * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre k out)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : (mn >= (Znth k text (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : ((0 : Int) <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn)) (PreH10 : (SpecPrefix text k out)) ,
  (charArray.full win_pre (k + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** (charArray.full s_pre n_pre text)
|--
  “ (mn >= (Znth k text (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (PrefixMinimum text k mn) ” &&
  “ (SpecPrefix text k out) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char |-> ((Znth k text (0 : Int))))
  ** (charArray.missing_i s_pre k (0 : Int) n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : (mn < (Znth k text (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : ((0 : Int) <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn)) (PreH10 : (SpecPrefix text k out)) ,
  (charArray.full win_pre (k + 1) (out ++ (1 :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
  ** (charArray.full s_pre n_pre text)
|--
  “ (mn < (Znth k text (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (PrefixMinimum text k mn) ” &&
  “ (SpecPrefix text k out) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char |-> ((Znth k text (0 : Int))))
  ** (charArray.missing_i s_pre k (0 : Int) n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ (1 :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (win_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (out : (List Int)) (mn : Int) (k : Int) (PreH1 : ((Znth k text (0 : Int)) < mn)) (PreH2 : (mn >= (Znth k text (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : ((0 : Int) <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn)) (PreH11 : (SpecPrefix text k out)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)
|--
  “ ((Znth k text (0 : Int)) < mn) ” &&
  “ (mn >= (Znth k text (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 500000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122))) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (PrefixMinimum text k mn) ” &&
  “ (SpecPrefix text k out) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char |-> ((Znth k text (0 : Int))))
  ** (charArray.missing_i s_pre k (0 : Int) n_pre text)
  ** (charArray.full win_pre (k + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg win_pre (k + 1) n_pre)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_goal
