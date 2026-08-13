import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.bubble_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bubble_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bubble_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def bubble_sort_safety_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_safety_wit_2 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= (n_pre - 1))) (PreH5 : (Permutation l a)) (PreH6 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH7 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_safety_wit_3 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (i = (0 : Int))) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_safety_wit_4 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (i = (0 : Int))) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_safety_wit_5 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= (n_pre - 1))) (PreH5 : (Permutation l a)) (PreH6 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH7 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_safety_wit_6 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ False ”

noncomputable def bubble_sort_safety_wit_7 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_safety_wit_8 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Zlength (a)) = n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a)
|--
  “ (((n_pre - 1) - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre - 1) - i)) ”

noncomputable def bubble_sort_safety_wit_9 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Zlength (a)) = n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_safety_wit_10 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Zlength (a)) = n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_safety_wit_11 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : (j < ((n_pre - 1) - i))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH10 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_safety_wit_12 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : (j < ((n_pre - 1) - i))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH10 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_safety_wit_13 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_safety_wit_14 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_safety_wit_15 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a (0 : Int))) (a)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_safety_wit_16 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a (0 : Int))) (a)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_safety_wit_17 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre (replace_Znth ((j + 1)) ((Znth j a (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a (0 : Int))) (a)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_safety_wit_18 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) <= (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_safety_wit_19 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH10 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def bubble_sort_entail_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  (“ (n_pre = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((Zlength (l)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l))
  ||
  (EX a : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ”
  &&  (intArray.full arr_pre n_pre a))

noncomputable def bubble_sort_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a_2 : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH8 : forall (p_3 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_3) ∧ (p_3 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  EX a : (List Int),
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (0 : Int))) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth ((0 : Int)) (a) ((0 : Int))))) ”
  &&  (intArray.full arr_pre n_pre a)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a_2 : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH8 : forall (p_3 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_3) ∧ (p_3 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) ,
  TT && emp 
|--
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (0 : Int))) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth ((0 : Int)) (a_2) ((0 : Int))))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int))))) ”
  &&  emp
)

noncomputable def bubble_sort_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a_2 : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH8 : forall (p_3 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_3) ∧ (p_3 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) ,
  forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (0 : Int))) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth ((0 : Int)) (a_2) ((0 : Int)))))

noncomputable def bubble_sort_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a_2 : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH8 : forall (p_3 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_3) ∧ (p_3 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))

noncomputable def bubble_sort_entail_wit_3_1 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre (replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))
|--
  EX a : (List Int),
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (j + 1))) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth ((j + 1)) (a) ((0 : Int))))) ”
  &&  (intArray.full arr_pre n_pre a)
) \/
(
forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - i)) (n_pre) ((replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2))))))) ” &&
  “ (Permutation l (replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2))))) ” &&
  “ ((Zlength ((replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))) = n_pre) ”
  &&  emp
)

noncomputable def bubble_sort_entail_wit_3_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  (increasing (sublist ((n_pre - i)) (n_pre) ((replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))))

noncomputable def bubble_sort_entail_wit_3_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  (Permutation l (replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))

noncomputable def bubble_sort_entail_wit_3_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  ((Zlength ((replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))) = n_pre)

noncomputable def bubble_sort_entail_wit_3_2 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) <= (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  EX a : (List Int),
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (j + 1))) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth ((j + 1)) (a) ((0 : Int))))) ”
  &&  (intArray.full arr_pre n_pre a)

noncomputable def bubble_sort_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  EX a : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (i + 1)))) ∧ ((n_pre - (i + 1)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ”
  &&  (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (i + 1)))) ∧ ((n_pre - (i + 1)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int))))) ” &&
  “ (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a_2))) ”
  &&  emp
)

noncomputable def bubble_sort_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (i + 1)))) ∧ ((n_pre - (i + 1)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))

noncomputable def bubble_sort_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) ,
  (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a_2)))

noncomputable def bubble_sort_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ” &&
  “ ((Zlength (l1)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) ,
  TT && emp 
|--
  “ (increasing l) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def bubble_sort_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) ,
  (increasing l)

noncomputable def bubble_sort_return_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) ,
  (Permutation l l)

noncomputable def bubble_sort_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ” &&
  “ ((Zlength (l1)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) ,
  TT && emp 
|--
  “ (increasing a) ”
  &&  emp
)

noncomputable def bubble_sort_return_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) ,
  (increasing a)

noncomputable def bubble_sort_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : (j < ((n_pre - 1) - i))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH10 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
|--
  “ (j < ((n_pre - 1) - i)) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int))))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a)

noncomputable def bubble_sort_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : (j < ((n_pre - 1) - i))) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH10 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
|--
  “ (j < ((n_pre - 1) - i)) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int))))) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) a (0 : Int))))
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre a)

noncomputable def bubble_sort_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
|--
  “ ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i)) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int))))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a)

noncomputable def bubble_sort_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
|--
  “ ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i)) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int))))) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) a (0 : Int))))
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre a)

noncomputable def bubble_sort_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre a)
|--
  “ ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i)) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int))))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a)

noncomputable def bubble_sort_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (j : Int) (i : Int) (a : (List Int)) (PreH1 : ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i))) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i))) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int)))))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a (0 : Int))) (a)))
|--
  “ ((Znth j a (0 : Int)) > (Znth (j + 1) a (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i)) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < j)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (j) (a) ((0 : Int))))) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre (replace_Znth (j) ((Znth (j + 1) a (0 : Int))) (a)))

noncomputable def bubble_sort_alter_safety_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((False ∨ (True ∧ (n_pre = (0 : Int)))) ∨ (True ∧ (n_pre > (0 : Int)))) ”

noncomputable def bubble_sort_alter_safety_wit_2_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = (0 : Int))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_alter_safety_wit_3_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_alter_safety_wit_4_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= (n_pre - 1))) (PreH5 : (Permutation l a)) (PreH6 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH7 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH8 : (n_pre >= (0 : Int))) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_alter_safety_wit_5_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (i = (0 : Int))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= (0 : Int))) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_alter_safety_wit_6_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (i = (0 : Int))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= (0 : Int))) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter_safety_wit_7_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= (n_pre - 1))) (PreH5 : (Permutation l a)) (PreH6 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH7 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH8 : (n_pre >= (0 : Int))) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter_safety_wit_8_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ False ”

noncomputable def bubble_sort_alter_safety_wit_9_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_alter_safety_wit_10_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i_2 : Int) (a : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH9 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH10 : (i_2 < (n_pre - 1))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : ((0 : Int) <= i_2)) (PreH14 : (i_2 <= (n_pre - 1))) (PreH15 : (Permutation l a)) (PreH16 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a)))) (PreH17 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH18 : (n_pre >= (0 : Int))) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ (((n_pre - 1) - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre - 1) - i)) ”

noncomputable def bubble_sort_alter_safety_wit_11_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i_2))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH9 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH10 : (i < (n_pre - 1))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre - 1))) (PreH15 : (Permutation l a)) (PreH16 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH17 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH18 : (n_pre >= (0 : Int))) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_alter_safety_wit_12_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i_2))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH9 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH10 : (i < (n_pre - 1))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre - 1))) (PreH15 : (Permutation l a)) (PreH16 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH17 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH18 : (n_pre >= (0 : Int))) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter_safety_wit_13_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter_safety_wit_14_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter_safety_wit_15_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter_safety_wit_16_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter_safety_wit_17_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter_safety_wit_18_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter_safety_wit_19_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter_safety_wit_20_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) <= (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter_safety_wit_21_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i_2 : Int) (a : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def bubble_sort_alter_entail_wit_1_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (n_pre = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre = (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def bubble_sort_alter_entail_wit_2_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX a : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (l) ((0 : Int))) <= (Znth (q) (l) ((0 : Int))))) ” &&
  “ (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (l))) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def bubble_sort_alter_entail_wit_2_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (l) ((0 : Int))) <= (Znth (q) (l) ((0 : Int)))))

noncomputable def bubble_sort_alter_entail_wit_2_normal_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (l)))

noncomputable def bubble_sort_alter_entail_wit_2_normal_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  (Permutation l l)

noncomputable def bubble_sort_alter_entail_wit_3_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a)
|--
  EX a_2 : (List Int),
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (0 : Int))) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth ((0 : Int)) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a_2)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (0 : Int))) -> ((Znth (p_3) (a) ((0 : Int))) <= (Znth ((0 : Int)) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (q_2) (a) ((0 : Int))))) ”
  &&  emp
)

noncomputable def bubble_sort_alter_entail_wit_3_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (0 : Int))) -> ((Znth (p_3) (a) ((0 : Int))) <= (Znth ((0 : Int)) (a) ((0 : Int)))))

noncomputable def bubble_sort_alter_entail_wit_3_normal_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (q_2) (a) ((0 : Int)))))

noncomputable def bubble_sort_alter_entail_wit_4_1_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))
|--
  EX a_2 : (List Int),
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (j + 1))) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth ((j + 1)) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a_2)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3))))))) ” &&
  “ (Permutation l (replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3))))) ” &&
  “ ((Zlength ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))) = n_pre) ”
  &&  emp
)

noncomputable def bubble_sort_alter_entail_wit_4_1_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (increasing (sublist ((n_pre - i_2)) (n_pre) ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))))

noncomputable def bubble_sort_alter_entail_wit_4_1_normal_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (Permutation l (replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))

noncomputable def bubble_sort_alter_entail_wit_4_1_normal_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  ((Zlength ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))) = n_pre)

noncomputable def bubble_sort_alter_entail_wit_4_2_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) <= (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_3)
|--
  EX a_2 : (List Int),
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (j + 1))) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth ((j + 1)) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a_2)

noncomputable def bubble_sort_alter_entail_wit_5_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i_2 : Int) (a_2 : (List Int)) (j : Int) (i : Int) (a_3 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_3)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_3)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a_2)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_3)
|--
  EX a : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (i + 1)))) ∧ ((n_pre - (i + 1)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i_2 : Int) (a_2 : (List Int)) (j : Int) (i : Int) (a_3 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_3)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_3)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a_2)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a_3))) ”
  &&  emp
)

noncomputable def bubble_sort_alter_entail_wit_5_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i_2 : Int) (a_2 : (List Int)) (j : Int) (i : Int) (a_3 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_3)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_3)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a_2)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a_3)))

noncomputable def bubble_sort_alter_return_wit_1_zero : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ” &&
  “ ((Zlength (l1)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  TT && emp 
|--
  “ (increasing l) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def bubble_sort_alter_return_wit_1_zero_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  (increasing l)

noncomputable def bubble_sort_alter_return_wit_1_zero_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  (Permutation l l)

noncomputable def bubble_sort_alter_return_wit_2_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ” &&
  “ ((Zlength (l1)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ (increasing a) ”
  &&  emp
)

noncomputable def bubble_sort_alter_return_wit_2_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  (increasing a)

noncomputable def bubble_sort_alter_partial_solve_wit_1_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter_partial_solve_wit_2_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter_partial_solve_wit_3_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter_partial_solve_wit_4_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter_partial_solve_wit_5_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter_partial_solve_wit_6_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))

noncomputable def bubble_sort_alter1_safety_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((False ∨ (True ∧ (n_pre = (0 : Int)))) ∨ (True ∧ (n_pre > (0 : Int)))) ”

noncomputable def bubble_sort_alter1_safety_wit_2_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = (0 : Int))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_alter1_safety_wit_3_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_alter1_safety_wit_4_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= (n_pre - 1))) (PreH5 : (Permutation l a)) (PreH6 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH7 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH8 : (n_pre >= (0 : Int))) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_5_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (i = (0 : Int))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= (0 : Int))) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_6_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (i = (0 : Int))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre >= (0 : Int))) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (n_pre = (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter1_safety_wit_7_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((Zlength (a)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= (n_pre - 1))) (PreH5 : (Permutation l a)) (PreH6 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH7 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH8 : (n_pre >= (0 : Int))) (PreH9 : (n_pre <= 100000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter1_safety_wit_8_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ False ”

noncomputable def bubble_sort_alter1_safety_wit_9_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def bubble_sort_alter1_safety_wit_10_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i_2 : Int) (a : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH9 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH10 : (i_2 < (n_pre - 1))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : ((0 : Int) <= i_2)) (PreH14 : (i_2 <= (n_pre - 1))) (PreH15 : (Permutation l a)) (PreH16 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a)))) (PreH17 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH18 : (n_pre >= (0 : Int))) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ (((n_pre - 1) - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre - 1) - i)) ”

noncomputable def bubble_sort_alter1_safety_wit_11_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i_2))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH9 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH10 : (i < (n_pre - 1))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre - 1))) (PreH15 : (Permutation l a)) (PreH16 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH17 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH18 : (n_pre >= (0 : Int))) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_12_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Zlength (a_2)) = n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 < (n_pre - 1))) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= ((n_pre - 1) - i_2))) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH9 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH10 : (i < (n_pre - 1))) (PreH11 : (1 <= n_pre)) (PreH12 : ((Zlength (a)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre - 1))) (PreH15 : (Permutation l a)) (PreH16 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH17 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH18 : (n_pre >= (0 : Int))) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter1_safety_wit_13_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_14_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter1_safety_wit_15_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_16_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter1_safety_wit_17_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_18_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))
  ** ((( &( "tmp" ) )) # Int |-> ((Znth j a_2 (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def bubble_sort_alter1_safety_wit_19_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth ((j + 1)) ((Znth j a_2 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_20_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) <= (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def bubble_sort_alter1_safety_wit_21_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i_2 : Int) (a : (List Int)) (j : Int) (i : Int) (a_2 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_2)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def bubble_sort_alter1_entail_wit_1_zero : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (n_pre = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre = (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def bubble_sort_alter1_entail_wit_2_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX a : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (l) ((0 : Int))) <= (Znth (q) (l) ((0 : Int))))) ” &&
  “ (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (l))) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def bubble_sort_alter1_entail_wit_2_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (0 : Int)))) ∧ ((n_pre - (0 : Int)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (l) ((0 : Int))) <= (Znth (q) (l) ((0 : Int)))))

noncomputable def bubble_sort_alter1_entail_wit_2_normal_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  (increasing (sublist ((n_pre - (0 : Int))) (n_pre) (l)))

noncomputable def bubble_sort_alter1_entail_wit_2_normal_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre >= (0 : Int))) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (n_pre > (0 : Int))) ,
  (Permutation l l)

noncomputable def bubble_sort_alter1_entail_wit_3_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a)
|--
  EX a_2 : (List Int),
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - 1) - i)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (0 : Int))) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth ((0 : Int)) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a_2)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (0 : Int))) -> ((Znth (p_3) (a) ((0 : Int))) <= (Znth ((0 : Int)) (a) ((0 : Int))))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (q_2) (a) ((0 : Int))))) ”
  &&  emp
)

noncomputable def bubble_sort_alter1_entail_wit_3_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (0 : Int))) -> ((Znth (p_3) (a) ((0 : Int))) <= (Znth ((0 : Int)) (a) ((0 : Int)))))

noncomputable def bubble_sort_alter1_entail_wit_3_normal_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a) ((0 : Int))) <= (Znth (q_2) (a) ((0 : Int)))))

noncomputable def bubble_sort_alter1_entail_wit_4_1_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))
|--
  EX a_2 : (List Int),
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (j + 1))) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth ((j + 1)) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a_2)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3))))))) ” &&
  “ (Permutation l (replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3))))) ” &&
  “ ((Zlength ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))) = n_pre) ”
  &&  emp
)

noncomputable def bubble_sort_alter1_entail_wit_4_1_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (increasing (sublist ((n_pre - i_2)) (n_pre) ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))))

noncomputable def bubble_sort_alter1_entail_wit_4_1_normal_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (Permutation l (replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))

noncomputable def bubble_sort_alter1_entail_wit_4_1_normal_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) > (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  ((Zlength ((replace_Znth ((j + 1)) ((Znth j a_3 (0 : Int))) ((replace_Znth (j) ((Znth (j + 1) a_3 (0 : Int))) (a_3)))))) = n_pre)

noncomputable def bubble_sort_alter1_entail_wit_4_2_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_3 : (List Int)) (PreH1 : ((Znth j a_3 (0 : Int)) <= (Znth (j + 1) a_3 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_3)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_3)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_3)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_3)
|--
  EX a_2 : (List Int),
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (j + 1))) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth ((j + 1)) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a_2)

noncomputable def bubble_sort_alter1_entail_wit_5_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i_2 : Int) (a_2 : (List Int)) (j : Int) (i : Int) (a_3 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_3)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_3)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a_2)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre a_3)
|--
  EX a : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - (i + 1)))) ∧ ((n_pre - (i + 1)) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre a)
  ** ((( &( "j" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i_2 : Int) (a_2 : (List Int)) (j : Int) (i : Int) (a_3 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_3)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_3)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a_2)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a_3))) ”
  &&  emp
)

noncomputable def bubble_sort_alter1_entail_wit_5_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i_2 : Int) (a_2 : (List Int)) (j : Int) (i : Int) (a_3 : (List Int)) (PreH1 : (j >= ((n_pre - 1) - i))) (PreH2 : ((Zlength (a_3)) = n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i))) (PreH7 : (Permutation l a_3)) (PreH8 : (increasing (sublist ((n_pre - i)) (n_pre) (a_3)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i))) ∧ ((n_pre - i) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_3) ((0 : Int))) <= (Znth (q_2) (a_3) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_3) ((0 : Int))) <= (Znth (j) (a_3) ((0 : Int)))))) (PreH11 : (i_2 < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a_2)) = n_pre)) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= (n_pre - 1))) (PreH16 : (Permutation l a_2)) (PreH17 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a_2) ((0 : Int))) <= (Znth (q) (a_2) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (increasing (sublist ((n_pre - (i + 1))) (n_pre) (a_3)))

noncomputable def bubble_sort_alter1_return_wit_1_zero : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ” &&
  “ ((Zlength (l1)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  TT && emp 
|--
  “ (increasing l) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def bubble_sort_alter1_return_wit_1_zero_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  (increasing l)

noncomputable def bubble_sort_alter1_return_wit_1_zero_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (n_pre = (0 : Int))) (PreH3 : (i = (0 : Int))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (n_pre >= (0 : Int))) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (n_pre = (0 : Int))) ,
  (Permutation l l)

noncomputable def bubble_sort_alter1_return_wit_2_normal : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ” &&
  “ ((Zlength (l1)) = n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  TT && emp 
|--
  “ (increasing a) ”
  &&  emp
)

noncomputable def bubble_sort_alter1_return_wit_2_normal_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (PreH1 : (i >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : ((Zlength (a)) = n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre - 1))) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH9 : (n_pre >= (0 : Int))) (PreH10 : (n_pre <= 100000)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (n_pre > (0 : Int))) ,
  (increasing a)

noncomputable def bubble_sort_alter1_partial_solve_wit_1_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter1_partial_solve_wit_2_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : (j < ((n_pre - 1) - i_2))) (PreH2 : ((Zlength (a_2)) = n_pre)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < (n_pre - 1))) (PreH5 : ((0 : Int) <= j)) (PreH6 : (j <= ((n_pre - 1) - i_2))) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH10 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH11 : (i < (n_pre - 1))) (PreH12 : (1 <= n_pre)) (PreH13 : ((Zlength (a)) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= (n_pre - 1))) (PreH16 : (Permutation l a)) (PreH17 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH18 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH19 : (n_pre >= (0 : Int))) (PreH20 : (n_pre <= 100000)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter1_partial_solve_wit_3_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter1_partial_solve_wit_4_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |-> ((Znth (j + 1) a_2 (0 : Int))))
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter1_partial_solve_wit_5_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre a_2)
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre a_2)

noncomputable def bubble_sort_alter1_partial_solve_wit_6_normal : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (i : Int) (a : (List Int)) (j : Int) (i_2 : Int) (a_2 : (List Int)) (PreH1 : ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int)))) (PreH2 : (j < ((n_pre - 1) - i_2))) (PreH3 : ((Zlength (a_2)) = n_pre)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < (n_pre - 1))) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= ((n_pre - 1) - i_2))) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int)))))) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int)))))) (PreH12 : (i < (n_pre - 1))) (PreH13 : (1 <= n_pre)) (PreH14 : ((Zlength (a)) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i <= (n_pre - 1))) (PreH17 : (Permutation l a)) (PreH18 : (increasing (sublist ((n_pre - i)) (n_pre) (a)))) (PreH19 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int)))))) (PreH20 : (n_pre >= (0 : Int))) (PreH21 : (n_pre <= 100000)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (n_pre > (0 : Int))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))
|--
  “ ((Znth j a_2 (0 : Int)) > (Znth (j + 1) a_2 (0 : Int))) ” &&
  “ (j < ((n_pre - 1) - i_2)) ” &&
  “ ((Zlength (a_2)) = n_pre) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - i_2)) ” &&
  “ (Permutation l a_2) ” &&
  “ (increasing (sublist ((n_pre - i_2)) (n_pre) (a_2))) ” &&
  “ forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < (n_pre - i_2))) ∧ ((n_pre - i_2) <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (a_2) ((0 : Int))) <= (Znth (q_2) (a_2) ((0 : Int))))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < j)) -> ((Znth (p_3) (a_2) ((0 : Int))) <= (Znth (j) (a_2) ((0 : Int))))) ” &&
  “ (i < (n_pre - 1)) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (a)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre - 1)) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((n_pre - i)) (n_pre) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (n_pre - i))) ∧ ((n_pre - i) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (a) ((0 : Int))) <= (Znth (q) (a) ((0 : Int))))) ” &&
  “ (n_pre >= (0 : Int)) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (n_pre > (0 : Int)) ”
  &&  (((arr_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre (j + 1) (0 : Int) n_pre (replace_Znth (j) ((Znth (j + 1) a_2 (0 : Int))) (a_2)))


structure VC_Correct : Type where
  proof_of_bubble_sort_safety_wit_1 : bubble_sort_safety_wit_1
  proof_of_bubble_sort_safety_wit_2 : bubble_sort_safety_wit_2
  proof_of_bubble_sort_safety_wit_3 : bubble_sort_safety_wit_3
  proof_of_bubble_sort_safety_wit_4 : bubble_sort_safety_wit_4
  proof_of_bubble_sort_safety_wit_5 : bubble_sort_safety_wit_5
  proof_of_bubble_sort_safety_wit_6 : bubble_sort_safety_wit_6
  proof_of_bubble_sort_safety_wit_7 : bubble_sort_safety_wit_7
  proof_of_bubble_sort_safety_wit_8 : bubble_sort_safety_wit_8
  proof_of_bubble_sort_safety_wit_9 : bubble_sort_safety_wit_9
  proof_of_bubble_sort_safety_wit_10 : bubble_sort_safety_wit_10
  proof_of_bubble_sort_safety_wit_11 : bubble_sort_safety_wit_11
  proof_of_bubble_sort_safety_wit_12 : bubble_sort_safety_wit_12
  proof_of_bubble_sort_safety_wit_13 : bubble_sort_safety_wit_13
  proof_of_bubble_sort_safety_wit_14 : bubble_sort_safety_wit_14
  proof_of_bubble_sort_safety_wit_15 : bubble_sort_safety_wit_15
  proof_of_bubble_sort_safety_wit_16 : bubble_sort_safety_wit_16
  proof_of_bubble_sort_safety_wit_17 : bubble_sort_safety_wit_17
  proof_of_bubble_sort_safety_wit_18 : bubble_sort_safety_wit_18
  proof_of_bubble_sort_safety_wit_19 : bubble_sort_safety_wit_19
  proof_of_bubble_sort_entail_wit_3_2 : bubble_sort_entail_wit_3_2
  proof_of_bubble_sort_partial_solve_wit_1 : bubble_sort_partial_solve_wit_1
  proof_of_bubble_sort_partial_solve_wit_2 : bubble_sort_partial_solve_wit_2
  proof_of_bubble_sort_partial_solve_wit_3 : bubble_sort_partial_solve_wit_3
  proof_of_bubble_sort_partial_solve_wit_4 : bubble_sort_partial_solve_wit_4
  proof_of_bubble_sort_partial_solve_wit_5 : bubble_sort_partial_solve_wit_5
  proof_of_bubble_sort_partial_solve_wit_6 : bubble_sort_partial_solve_wit_6
  proof_of_bubble_sort_alter_safety_wit_1 : bubble_sort_alter_safety_wit_1
  proof_of_bubble_sort_alter_safety_wit_2_zero : bubble_sort_alter_safety_wit_2_zero
  proof_of_bubble_sort_alter_safety_wit_3_normal : bubble_sort_alter_safety_wit_3_normal
  proof_of_bubble_sort_alter_safety_wit_4_normal : bubble_sort_alter_safety_wit_4_normal
  proof_of_bubble_sort_alter_safety_wit_5_zero : bubble_sort_alter_safety_wit_5_zero
  proof_of_bubble_sort_alter_safety_wit_6_zero : bubble_sort_alter_safety_wit_6_zero
  proof_of_bubble_sort_alter_safety_wit_7_normal : bubble_sort_alter_safety_wit_7_normal
  proof_of_bubble_sort_alter_safety_wit_8_zero : bubble_sort_alter_safety_wit_8_zero
  proof_of_bubble_sort_alter_safety_wit_9_normal : bubble_sort_alter_safety_wit_9_normal
  proof_of_bubble_sort_alter_safety_wit_10_normal : bubble_sort_alter_safety_wit_10_normal
  proof_of_bubble_sort_alter_safety_wit_11_normal : bubble_sort_alter_safety_wit_11_normal
  proof_of_bubble_sort_alter_safety_wit_12_normal : bubble_sort_alter_safety_wit_12_normal
  proof_of_bubble_sort_alter_safety_wit_13_normal : bubble_sort_alter_safety_wit_13_normal
  proof_of_bubble_sort_alter_safety_wit_14_normal : bubble_sort_alter_safety_wit_14_normal
  proof_of_bubble_sort_alter_safety_wit_15_normal : bubble_sort_alter_safety_wit_15_normal
  proof_of_bubble_sort_alter_safety_wit_16_normal : bubble_sort_alter_safety_wit_16_normal
  proof_of_bubble_sort_alter_safety_wit_17_normal : bubble_sort_alter_safety_wit_17_normal
  proof_of_bubble_sort_alter_safety_wit_18_normal : bubble_sort_alter_safety_wit_18_normal
  proof_of_bubble_sort_alter_safety_wit_19_normal : bubble_sort_alter_safety_wit_19_normal
  proof_of_bubble_sort_alter_safety_wit_20_normal : bubble_sort_alter_safety_wit_20_normal
  proof_of_bubble_sort_alter_safety_wit_21_normal : bubble_sort_alter_safety_wit_21_normal
  proof_of_bubble_sort_alter_entail_wit_1_zero : bubble_sort_alter_entail_wit_1_zero
  proof_of_bubble_sort_alter_entail_wit_4_2_normal : bubble_sort_alter_entail_wit_4_2_normal
  proof_of_bubble_sort_alter_partial_solve_wit_1_normal : bubble_sort_alter_partial_solve_wit_1_normal
  proof_of_bubble_sort_alter_partial_solve_wit_2_normal : bubble_sort_alter_partial_solve_wit_2_normal
  proof_of_bubble_sort_alter_partial_solve_wit_3_normal : bubble_sort_alter_partial_solve_wit_3_normal
  proof_of_bubble_sort_alter_partial_solve_wit_4_normal : bubble_sort_alter_partial_solve_wit_4_normal
  proof_of_bubble_sort_alter_partial_solve_wit_5_normal : bubble_sort_alter_partial_solve_wit_5_normal
  proof_of_bubble_sort_alter_partial_solve_wit_6_normal : bubble_sort_alter_partial_solve_wit_6_normal
  proof_of_bubble_sort_alter1_safety_wit_1 : bubble_sort_alter1_safety_wit_1
  proof_of_bubble_sort_alter1_safety_wit_2_zero : bubble_sort_alter1_safety_wit_2_zero
  proof_of_bubble_sort_alter1_safety_wit_3_normal : bubble_sort_alter1_safety_wit_3_normal
  proof_of_bubble_sort_alter1_safety_wit_4_normal : bubble_sort_alter1_safety_wit_4_normal
  proof_of_bubble_sort_alter1_safety_wit_5_zero : bubble_sort_alter1_safety_wit_5_zero
  proof_of_bubble_sort_alter1_safety_wit_6_zero : bubble_sort_alter1_safety_wit_6_zero
  proof_of_bubble_sort_alter1_safety_wit_7_normal : bubble_sort_alter1_safety_wit_7_normal
  proof_of_bubble_sort_alter1_safety_wit_8_zero : bubble_sort_alter1_safety_wit_8_zero
  proof_of_bubble_sort_alter1_safety_wit_9_normal : bubble_sort_alter1_safety_wit_9_normal
  proof_of_bubble_sort_alter1_safety_wit_10_normal : bubble_sort_alter1_safety_wit_10_normal
  proof_of_bubble_sort_alter1_safety_wit_11_normal : bubble_sort_alter1_safety_wit_11_normal
  proof_of_bubble_sort_alter1_safety_wit_12_normal : bubble_sort_alter1_safety_wit_12_normal
  proof_of_bubble_sort_alter1_safety_wit_13_normal : bubble_sort_alter1_safety_wit_13_normal
  proof_of_bubble_sort_alter1_safety_wit_14_normal : bubble_sort_alter1_safety_wit_14_normal
  proof_of_bubble_sort_alter1_safety_wit_15_normal : bubble_sort_alter1_safety_wit_15_normal
  proof_of_bubble_sort_alter1_safety_wit_16_normal : bubble_sort_alter1_safety_wit_16_normal
  proof_of_bubble_sort_alter1_safety_wit_17_normal : bubble_sort_alter1_safety_wit_17_normal
  proof_of_bubble_sort_alter1_safety_wit_18_normal : bubble_sort_alter1_safety_wit_18_normal
  proof_of_bubble_sort_alter1_safety_wit_19_normal : bubble_sort_alter1_safety_wit_19_normal
  proof_of_bubble_sort_alter1_safety_wit_20_normal : bubble_sort_alter1_safety_wit_20_normal
  proof_of_bubble_sort_alter1_safety_wit_21_normal : bubble_sort_alter1_safety_wit_21_normal
  proof_of_bubble_sort_alter1_entail_wit_1_zero : bubble_sort_alter1_entail_wit_1_zero
  proof_of_bubble_sort_alter1_entail_wit_4_2_normal : bubble_sort_alter1_entail_wit_4_2_normal
  proof_of_bubble_sort_alter1_partial_solve_wit_1_normal : bubble_sort_alter1_partial_solve_wit_1_normal
  proof_of_bubble_sort_alter1_partial_solve_wit_2_normal : bubble_sort_alter1_partial_solve_wit_2_normal
  proof_of_bubble_sort_alter1_partial_solve_wit_3_normal : bubble_sort_alter1_partial_solve_wit_3_normal
  proof_of_bubble_sort_alter1_partial_solve_wit_4_normal : bubble_sort_alter1_partial_solve_wit_4_normal
  proof_of_bubble_sort_alter1_partial_solve_wit_5_normal : bubble_sort_alter1_partial_solve_wit_5_normal
  proof_of_bubble_sort_alter1_partial_solve_wit_6_normal : bubble_sort_alter1_partial_solve_wit_6_normal
  proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1
  proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2
  proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1
  proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4
  proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1
  proof_of_bubble_sort_return_wit_2 : bubble_sort_return_wit_2
  proof_of_bubble_sort_alter_entail_wit_2_normal : bubble_sort_alter_entail_wit_2_normal
  proof_of_bubble_sort_alter_entail_wit_3_normal : bubble_sort_alter_entail_wit_3_normal
  proof_of_bubble_sort_alter_entail_wit_4_1_normal : bubble_sort_alter_entail_wit_4_1_normal
  proof_of_bubble_sort_alter_entail_wit_5_normal : bubble_sort_alter_entail_wit_5_normal
  proof_of_bubble_sort_alter_return_wit_1_zero : bubble_sort_alter_return_wit_1_zero
  proof_of_bubble_sort_alter_return_wit_2_normal : bubble_sort_alter_return_wit_2_normal
  proof_of_bubble_sort_alter1_entail_wit_2_normal : bubble_sort_alter1_entail_wit_2_normal
  proof_of_bubble_sort_alter1_entail_wit_3_normal : bubble_sort_alter1_entail_wit_3_normal
  proof_of_bubble_sort_alter1_entail_wit_4_1_normal : bubble_sort_alter1_entail_wit_4_1_normal
  proof_of_bubble_sort_alter1_entail_wit_5_normal : bubble_sort_alter1_entail_wit_5_normal
  proof_of_bubble_sort_alter1_return_wit_1_zero : bubble_sort_alter1_return_wit_1_zero
  proof_of_bubble_sort_alter1_return_wit_2_normal : bubble_sort_alter1_return_wit_2_normal

end SimpleC.EE.QCP_demos_LLM.generated.bubble_sort_goal
