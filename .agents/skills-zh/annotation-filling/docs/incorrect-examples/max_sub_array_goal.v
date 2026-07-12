Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.max_sub_array_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import common_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import common_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function max -----*)

Definition max_return_wit_1 :=
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre > b_pre) |]
  &&  emp
|--
  [| (a_pre = (max_Z (a_pre) (b_pre))) |]
  &&  emp
.

Definition max_return_wit_2 :=
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <= b_pre) |]
  &&  emp
|--
  [| (b_pre = (max_Z (a_pre) (b_pre))) |]
  &&  emp
.

(*----- Function max_sub_array -----*)

Definition max_sub_array_safety_wit_1 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  [| (0 <= INT_MAX) |]
  &&  [| ((INT_MIN) <= 0) |]
.

Definition max_sub_array_safety_wit_2 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  [| (0 <= INT_MAX) |]
  &&  [| ((INT_MIN) <= 0) |]
.

Definition max_sub_array_safety_wit_3 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  [| (0 <= INT_MAX) |]
  &&  [| ((INT_MIN) <= 0) |]
.

Definition max_sub_array_safety_wit_4 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  ((( &( "res" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  [| (0 <= INT_MAX) |]
  &&  [| ((INT_MIN) <= 0) |]
.

Definition max_sub_array_safety_wit_5 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "res" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  [| (1 <= INT_MAX) |]
  &&  [| ((INT_MIN) <= 1) |]
.

Definition max_sub_array_safety_wit_6 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
|--
  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| ((INT_MIN) <= (cur + (Znth i l 0) )) |]
.

Definition max_sub_array_safety_wit_7 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full arr_pre n_pre l )
|--
  [| ((i + 1 ) <= INT_MAX) |]
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition max_sub_array_entail_wit_1 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= 1) |]
  &&  [| (1 <= n_pre) |]
  &&  [| ((Znth 0 l 0) = (max_suffix_sum ((sublist (0) (1) (l))))) |]
  &&  [| ((Znth 0 l 0) = (max_subarray_sum ((sublist (0) (1) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_2 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) ,
  [| (i < n_pre) |]
  &&  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i <= n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_3 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) (retval: Z) ,
  [| (retval = (max_Z ((Znth i l 0)) ((cur + (Znth i l 0) )))) |]
  &&  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (retval = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_4 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) (retval: Z) ,
  [| (retval = (max_Z (res) (cur))) |]
  &&  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (retval = (max_subarray_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_5 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= (i + 1 )) |]
  &&  [| ((i + 1 ) <= n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_entail_wit_6 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (res: Z) (cur: Z) (i: Z) ,
  [| (i >= n_pre) |]
  &&  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i <= n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (cur = (max_suffix_sum (l))) |]
  &&  [| (res = (max_subarray_sum (l))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_return_wit_1 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre = 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  ([| (0 < n_pre) |]
  &&  [| (IntuitiveMaxSubArraySum l 0 ) |]
  &&  (IntArray.full arr_pre n_pre l ))
  ||
  ([| (n_pre = 0) |]
  &&  [| (0 = 0) |]
  &&  (IntArray.full arr_pre n_pre l ))
.

Definition max_sub_array_return_wit_2 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (cur = (max_suffix_sum (l))) |]
  &&  [| (res = (max_subarray_sum (l))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  ([| (0 < n_pre) |]
  &&  [| (IntuitiveMaxSubArraySum l res ) |]
  &&  (IntArray.full arr_pre n_pre l ))
  ||
  ([| (n_pre = 0) |]
  &&  [| (res = 0) |]
  &&  (IntArray.full arr_pre n_pre l ))
.

Definition max_sub_array_partial_solve_wit_1 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  (((arr_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_2 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) ,
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (n_pre <> 0) |]
  &&  [| (0 <= n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  (((arr_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i arr_pre 0 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_3 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_4 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
.

Definition max_sub_array_partial_solve_wit_5 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (INT_MIN <= (cur + (Znth i l 0) )) |]
  &&  [| ((cur + (Znth i l 0) ) <= INT_MAX) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) (i) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Definition max_sub_array_partial_solve_wit_6 :=
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (cur: Z) (res: Z) ,
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
|--
  [| (0 < n_pre) |]
  &&  [| ((Zlength (l)) = n_pre) |]
  &&  [| (kadane_safe l ) |]
  &&  [| (1 <= i) |]
  &&  [| (i < n_pre) |]
  &&  [| (cur = (max_suffix_sum ((sublist (0) ((i + 1 )) (l))))) |]
  &&  [| (res = (max_subarray_sum ((sublist (0) (i) (l))))) |]
  &&  (IntArray.full arr_pre n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_max_return_wit_1 : max_return_wit_1.
Axiom proof_of_max_return_wit_2 : max_return_wit_2.
Axiom proof_of_max_sub_array_safety_wit_1 : max_sub_array_safety_wit_1.
Axiom proof_of_max_sub_array_safety_wit_2 : max_sub_array_safety_wit_2.
Axiom proof_of_max_sub_array_safety_wit_3 : max_sub_array_safety_wit_3.
Axiom proof_of_max_sub_array_safety_wit_4 : max_sub_array_safety_wit_4.
Axiom proof_of_max_sub_array_safety_wit_5 : max_sub_array_safety_wit_5.
Axiom proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6.
Axiom proof_of_max_sub_array_safety_wit_7 : max_sub_array_safety_wit_7.
Axiom proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1.
Axiom proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2.
Axiom proof_of_max_sub_array_entail_wit_3 : max_sub_array_entail_wit_3.
Axiom proof_of_max_sub_array_entail_wit_4 : max_sub_array_entail_wit_4.
Axiom proof_of_max_sub_array_entail_wit_5 : max_sub_array_entail_wit_5.
Axiom proof_of_max_sub_array_entail_wit_6 : max_sub_array_entail_wit_6.
Axiom proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1.
Axiom proof_of_max_sub_array_return_wit_2 : max_sub_array_return_wit_2.
Axiom proof_of_max_sub_array_partial_solve_wit_1 : max_sub_array_partial_solve_wit_1.
Axiom proof_of_max_sub_array_partial_solve_wit_2 : max_sub_array_partial_solve_wit_2.
Axiom proof_of_max_sub_array_partial_solve_wit_3 : max_sub_array_partial_solve_wit_3.
Axiom proof_of_max_sub_array_partial_solve_wit_4 : max_sub_array_partial_solve_wit_4.
Axiom proof_of_max_sub_array_partial_solve_wit_5 : max_sub_array_partial_solve_wit_5.
Axiom proof_of_max_sub_array_partial_solve_wit_6 : max_sub_array_partial_solve_wit_6.

End VC_Correct.
