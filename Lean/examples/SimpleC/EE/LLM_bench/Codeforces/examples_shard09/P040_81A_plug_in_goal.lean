import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P040_81A_plug_in_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "top" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_full out_pre (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "top" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_full out_pre (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((top - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top - 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack (0 : Int)) = (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((top - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top - 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre (top + 1) (stack ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
|--
  “ ((top + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre (top + 1) (stack ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> (top))
|--
  “ ((top + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top + 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack (0 : Int)) = (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top - 1)))
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre (top + 1) (stack ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top + 1)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre (top + 1) (stack ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "top" ) )) # Int |-> ((top + 1)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.undef_full out_pre (n_pre + 1))
|--
  EX stack : (List Int),
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) ((0 : Int)) (text)) stack) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre (0 : Int) stack)
  ** (charArray.undef_seg out_pre (0 : Int) (n_pre + 1))
) \/
(
forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  TT && emp 
|--
  “ (Spec (sublist ((0 : Int)) ((0 : Int)) (text)) (@List.nil Int)) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (Spec (sublist ((0 : Int)) ((0 : Int)) (text)) (@List.nil Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((0 : Int) = (Zlength ((@List.nil Int))))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((97 <= (Znth i text (0 : Int))) ∧ ((Znth i text (0 : Int)) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack_2 (0 : Int)) = (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack_2)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  EX stack : (List Int),
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= (i + 1)) ” &&
  “ ((top - 1) = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) ((i + 1)) (text)) stack) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre (top - 1) stack)
  ** (charArray.undef_seg out_pre (top - 1) (n_pre + 1))
) \/
(
forall (out_pre : Int) (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack_2 (0 : Int)) = (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  (charArray.full out_pre top stack_2)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  EX stack : (List Int),
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= (i + 1)) ” &&
  “ ((top - 1) = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) ((i + 1)) (text)) stack) ”
  &&  (charArray.full out_pre (top - 1) stack)
  ** (charArray.undef_seg out_pre (top - 1) (n_pre + 1))
)

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  (charArray.full out_pre (top + 1) (stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
|--
  EX stack : (List Int),
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= (i + 1)) ” &&
  “ ((top + 1) = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) ((i + 1)) (text)) stack) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre (top + 1) stack)
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
) \/
(
forall (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  TT && emp 
|--
  “ (Spec (sublist ((0 : Int)) ((i + 1)) (text)) (stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int)))) ” &&
  “ ((top + 1) = (Zlength ((stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  (Spec (sublist ((0 : Int)) ((i + 1)) (text)) (stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  ((top + 1) = (Zlength ((stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))))

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack_2 (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  (charArray.full out_pre (top + 1) (stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
|--
  EX stack : (List Int),
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= (i + 1)) ” &&
  “ ((top + 1) = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) ((i + 1)) (text)) stack) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre (top + 1) stack)
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
) \/
(
forall (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack_2 (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  TT && emp 
|--
  “ (Spec (sublist ((0 : Int)) ((i + 1)) (text)) (stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int)))) ” &&
  “ ((top + 1) = (Zlength ((stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack_2 (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  (Spec (sublist ((0 : Int)) ((i + 1)) (text)) (stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))

noncomputable def solver_entail_wit_2_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (text : (List Int)) (stack_2 : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack_2 (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack_2)) ,
  ((top + 1) = (Zlength ((stack_2 ++ ((Znth i text (0 : Int)) :: (@List.nil Int))))))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre (top + 1) (stack ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
|--
  EX out_spec : (List Int),
  “ (Spec text out_spec) ” &&
  “ (top = (Zlength (out_spec))) ”
  &&  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre ((Zlength (out_spec)) + 1) (out_spec ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre ((Zlength (out_spec)) + 1) (n_pre + 1))
) \/
(
forall (out_pre : Int) (n_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre (top + 1) (stack ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
|--
  EX out_spec : (List Int),
  “ (Spec text out_spec) ” &&
  “ (top = (Zlength (out_spec))) ”
  &&  (charArray.full out_pre ((Zlength (out_spec)) + 1) (out_spec ++ ((0 : Int) :: (@List.nil Int))))
  ** (charArray.undef_seg out_pre ((Zlength (out_spec)) + 1) (n_pre + 1))
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ (top > (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((out_pre + ((top - 1) * sizeof(CHAR)))) # Char |-> ((Znth (top - 1) stack (0 : Int))))
  ** (charArray.missing_i out_pre (top - 1) (0 : Int) top stack)
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_seg out_pre top (n_pre + 1))

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full out_pre top stack)
  ** (charArray.full s_pre n_pre text)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ (top > (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i text (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ (top <= (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i text (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (top <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ (top <= (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((out_pre + (top * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((Znth (top - 1) stack (0 : Int)) ≠ (Znth i text (0 : Int))) ” &&
  “ (top > (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char |-> ((Znth i text (0 : Int))))
  ** (charArray.missing_i s_pre i (0 : Int) n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : ((Znth (top - 1) stack (0 : Int)) ≠ (Znth i text (0 : Int)))) (PreH2 : (top > (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ ((Znth (top - 1) stack (0 : Int)) ≠ (Znth i text (0 : Int))) ” &&
  “ (top > (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((out_pre + (top * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (s_pre : Int) (text : (List Int)) (stack : (List Int)) (top : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist ((0 : Int)) (i) (text)) stack)) ,
  (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)
  ** (charArray.undef_seg out_pre top (n_pre + 1))
|--
  “ (i >= n_pre) ” &&
  “ (n_pre = (Zlength (text))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((97 <= (Znth j text (0 : Int))) ∧ ((Znth j text (0 : Int)) <= 122))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= i) ” &&
  “ (top = (Zlength (stack))) ” &&
  “ (Spec (sublist ((0 : Int)) (i) (text)) stack) ”
  &&  (((out_pre + (top * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg out_pre (top + 1) (n_pre + 1))
  ** (charArray.full s_pre n_pre text)
  ** (charArray.full out_pre top stack)


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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_goal
