Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.bst_fp_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import bst_fp_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import bst_fp_strategy_proof.

(*----- Function replace_min -----*)

Definition replace_min_safety_wit_1 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (fa: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (ptr_pre <> 0)) (PreH2 : (tr = (combine_tree (pt0) (tr0)))) (PreH3 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH4 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH5 : (b_v <> 0)) (PreH6 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) ,
  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v fa tr0 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition replace_min_safety_wit_2 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (tr = (combine_tree (pt0) (tr0)))) (PreH3 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH4 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH5 : (b_v <> 0)) (PreH6 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition replace_min_safety_wit_3 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (ptr_pre <> 0)) (PreH3 : (tr = (combine_tree (pt0) (tr0)))) (PreH4 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH5 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH6 : (b_v <> 0)) (PreH7 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (b_v_father = fa)) (PreH11 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition replace_min_entail_wit_1 := 
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (b_pre_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_pre_v <> 0)) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre tr )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (tr0))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_ptb b_pre b_pre ptr_pre ptr_pre pt0 )
  **  (store_tree b_v ptr_pre tr0 )
) \/
(
forall (ptr_pre: Z) (k: Z) (tr: tree) (b_pre_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_pre_v <> 0)) ,
  TT && emp 
|--
  “ ((delete_min (tr)) = (combine_tree (empty_partial_tree) ((delete_min (tr))))) ” 
  &&  “ (tr = (combine_tree (empty_partial_tree) (tr))) ”
  &&  emp
).

Definition replace_min_entail_wit_1_split_goal_1 := 
forall (ptr_pre: Z) (k: Z) (tr: tree) (b_pre_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_pre_v <> 0)) ,
  ((delete_min (tr)) = (combine_tree (empty_partial_tree) ((delete_min (tr)))))
.

Definition replace_min_entail_wit_1_split_goal_2 := 
forall (ptr_pre: Z) (k: Z) (tr: tree) (b_pre_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_pre_v <> 0)) ,
  (tr = (combine_tree (empty_partial_tree) (tr)))
.

Definition replace_min_entail_wit_2 := 
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (fa: Z) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (PreH1 : (ptr_pre <> 0)) (PreH2 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH3 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH4 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  (store_tree b_v_2 fa tr0_2 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_father: Z)  (b_v_key: Z)  (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (tr0))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
) \/
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (fa: Z) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (PreH1 : (ptr_pre <> 0)) (PreH2 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH3 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH4 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) ,
  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  (store_tree b_v_2 fa tr0_2 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_key: Z)  (pt0: partial_tree) ,
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) ((make_tree (l0) (b_v_key) (b_v_value) (r0))))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) ((make_tree (l0) (b_v_key) (b_v_value) (r0))))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) ((make_tree (l0) (b_v_key) (b_v_value) (r0))))) ” 
  &&  “ (b_v_2 <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min ((make_tree (l0) (b_v_key) (b_v_value) (r0))))))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ”
  &&  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
).

Definition replace_min_entail_wit_3 := 
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_right_2 <> 0)) (PreH2 : (b_v_left_2 = 0)) (PreH3 : (ptr_pre <> 0)) (PreH4 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH5 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH6 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH7 : (b_v <> 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) (PreH9 : (INT_MIN <= b_v_key_2)) (PreH10 : (b_v_key_2 <= INT_MAX)) (PreH11 : (b_v_father_2 = fa)) (PreH12 : (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2)))) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (b_v_right_father: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_key: Z)  (b_v_right: Z)  (l1: tree)  (b_v_value: Z)  (tr0: tree)  (b_v_father: Z)  (b_v_key: Z)  (b_v_left: Z)  (b_v_2: Z)  (pt0: partial_tree)  (tr1: tree) ,
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (tr1))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr1))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr1))) ” 
  &&  “ (b_v = b_v_2) ” 
  &&  “ (b_v_2 <> 0) ” 
  &&  “ (b_v_left = 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr1))))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0))) ” 
  &&  “ (b_v_right <> 0) ” 
  &&  “ (INT_MIN <= b_v_right_key) ” 
  &&  “ (b_v_right_key <= INT_MAX) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ” 
  &&  “ (b_v_right_father = b_v_2) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v_2 l1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
) \/
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_right_2 <> 0)) (PreH2 : (b_v_left_2 = 0)) (PreH3 : (ptr_pre <> 0)) (PreH4 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH5 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH6 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH7 : (b_v <> 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) (PreH9 : (INT_MIN <= b_v_key_2)) (PreH10 : (b_v_key_2 <= INT_MAX)) (PreH11 : (b_v_father_2 = fa)) (PreH12 : (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2)))) ,
  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_key: Z)  (l1: tree)  (pt0: partial_tree) ,
  “ (b_v_left_2 = 0) ” 
  &&  “ (b_v_father_2 = fa) ” 
  &&  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) ((make_tree (l1) (b_v_key_2) (b_v_value_2) ((make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))))))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) ((make_tree (l1) (b_v_key_2) (b_v_value_2) ((make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))))))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) ((make_tree (l1) (b_v_key_2) (b_v_value_2) ((make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))))))) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min ((make_tree (l1) (b_v_key_2) (b_v_value_2) ((make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))))))))) ” 
  &&  “ (INT_MIN <= b_v_key_2) ” 
  &&  “ (b_v_key_2 <= INT_MAX) ” 
  &&  “ (b_v_right_2 <> 0) ” 
  &&  “ (INT_MIN <= b_v_right_key) ” 
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree 0 b_v l1 )
  **  ((&((b_v_right_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right_2 l0 )
  **  ((&((b_v_right_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right_2 r0 )
).

Definition replace_min_entail_wit_4 := 
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_left <> 0)) (PreH2 : (ptr_pre <> 0)) (PreH3 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH4 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH5 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH6 : (b_v_2 <> 0)) (PreH7 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (b_v_father = fa)) (PreH11 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (tr0))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 ptr_pre pt0 )
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_left <> 0)) (PreH5 : (ptr_pre <> 0)) (PreH6 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH7 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH8 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) (PreH11 : (INT_MIN <= b_v_key)) (PreH12 : (b_v_key <= INT_MAX)) (PreH13 : (b_v_father = fa)) (PreH14 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (pt0: partial_tree) ,
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (l0))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (l0))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (l0))) ” 
  &&  “ (b_v_left <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (l0))))) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 ptr_pre pt0 )
).

Definition replace_min_return_wit_1 := 
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_value: Z) (b_v_right_father: Z) (b_v_right_left: Z) (b_v_right_right: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (tr = (combine_tree (pt0) (tr1)))) (PreH3 : ((min_key (k) (tr)) = (min_key (k) (tr1)))) (PreH4 : ((min_value (v) (tr)) = (min_value (v) (tr1)))) (PreH5 : (to_free = b_v)) (PreH6 : (b_v <> 0)) (PreH7 : (b_v_left = 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr1)))))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH13 : (b_v_right <> 0)) (PreH14 : (INT_MIN <= b_v_right_key)) (PreH15 : (b_v_right_key <= INT_MAX)) (PreH16 : (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))) (PreH17 : (b_v_right_father = b_v)) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z)  (ptr_pre_value: Z)  (ptr_pre_key: Z) ,
  “ (ptr_pre_key = (min_key (k) (tr))) ” 
  &&  “ (ptr_pre_value = (min_value (v) (tr))) ” 
  &&  “ (INT_MIN <= ptr_pre_key) ” 
  &&  “ (ptr_pre_key <= INT_MAX) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> ptr_pre_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> ptr_pre_value)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre (delete_min (tr)) )
) \/
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_value: Z) (b_v_right_father: Z) (b_v_right_left: Z) (b_v_right_right: Z) (PreH1 : (b_v_right_value <= INT_MAX)) (PreH2 : (b_v_right_value >= INT_MIN)) (PreH3 : (b_v_right_key >= INT_MIN)) (PreH4 : (ptr_pre <> 0)) (PreH5 : (tr = (combine_tree (pt0) (tr1)))) (PreH6 : ((min_key (k) (tr)) = (min_key (k) (tr1)))) (PreH7 : ((min_value (v) (tr)) = (min_value (v) (tr1)))) (PreH8 : (to_free = b_v)) (PreH9 : (b_v <> 0)) (PreH10 : (b_v_left = 0)) (PreH11 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr1)))))) (PreH12 : (INT_MIN <= b_v_key)) (PreH13 : (b_v_key <= INT_MAX)) (PreH14 : (b_v_father = fa)) (PreH15 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH16 : (b_v_right <> 0)) (PreH17 : (INT_MIN <= b_v_right_key)) (PreH18 : (b_v_right_key <= INT_MAX)) (PreH19 : (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))) (PreH20 : (b_v_right_father = b_v)) ,
  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z) ,
  “ (b_v_value = (min_value (v) (tr))) ” 
  &&  “ (b_v_key = (min_key (k) (tr))) ” 
  &&  “ (b_v_value = (min_value (v) (tr))) ” 
  &&  “ (b_v_key = (min_key (k) (tr))) ” 
  &&  “ (INT_MIN <= (min_key (k) (tr))) ” 
  &&  “ ((min_key (k) (tr)) <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre (delete_min (tr)) )
).

Definition replace_min_return_wit_2 := 
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (ptr_pre <> 0)) (PreH4 : (tr = (combine_tree (pt0) (tr0)))) (PreH5 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH6 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH7 : (b_v <> 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
|--
  EX (b_pre_v: Z)  (ptr_pre_value: Z)  (ptr_pre_key: Z) ,
  “ (ptr_pre_key = (min_key (k) (tr))) ” 
  &&  “ (ptr_pre_value = (min_value (v) (tr))) ” 
  &&  “ (INT_MIN <= ptr_pre_key) ” 
  &&  “ (ptr_pre_key <= INT_MAX) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> ptr_pre_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> ptr_pre_value)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre (delete_min (tr)) )
) \/
(
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (ptr_pre <> 0)) (PreH4 : (tr = (combine_tree (pt0) (tr0)))) (PreH5 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH6 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH7 : (b_v <> 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
|--
  EX (b_pre_v: Z) ,
  “ (b_v_value = (min_value (v) (tr))) ” 
  &&  “ (b_v_key = (min_key (k) (tr))) ” 
  &&  “ (b_v_value = (min_value (v) (tr))) ” 
  &&  “ (b_v_key = (min_key (k) (tr))) ” 
  &&  “ (INT_MIN <= (min_key (k) (tr))) ” 
  &&  “ ((min_key (k) (tr)) <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre (delete_min (tr)) )
).

Definition replace_min_partial_solve_wit_1 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_value: Z) (b_v_right_father: Z) (b_v_right_left: Z) (b_v_right_right: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (tr = (combine_tree (pt0) (tr1)))) (PreH3 : ((min_key (k) (tr)) = (min_key (k) (tr1)))) (PreH4 : ((min_value (v) (tr)) = (min_value (v) (tr1)))) (PreH5 : (to_free = b_v)) (PreH6 : (b_v <> 0)) (PreH7 : (b_v_left = 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr1)))))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH13 : (b_v_right <> 0)) (PreH14 : (INT_MIN <= b_v_right_key)) (PreH15 : (b_v_right_key <= INT_MAX)) (PreH16 : (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))) (PreH17 : (b_v_right_father = b_v)) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (tr1))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr1))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr1))) ” 
  &&  “ (to_free = b_v) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ (b_v_left = 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr1))))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0))) ” 
  &&  “ (b_v_right <> 0) ” 
  &&  “ (INT_MIN <= b_v_right_key) ” 
  &&  “ (b_v_right_key <= INT_MAX) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ” 
  &&  “ (b_v_right_father = b_v) ”
  &&  ((&((to_free)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((to_free)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((to_free)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((to_free)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((to_free)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition replace_min_partial_solve_wit_2 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (ptr_pre <> 0)) (PreH4 : (tr = (combine_tree (pt0) (tr0)))) (PreH5 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH6 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH7 : (b_v <> 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (b_v_right = 0) ” 
  &&  “ (b_v_left = 0) ” 
  &&  “ (ptr_pre <> 0) ” 
  &&  “ (tr = (combine_tree (pt0) (tr0))) ” 
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ” 
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
.

(*----- Function Delete -----*)

Definition Delete_safety_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "fa" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Delete_safety_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_4 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_key >= x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (b_v <> 0)) (PreH4 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (b_v_father = fa)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_5 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_key >= x_pre)) (PreH3 : (x_pre >= b_v_key)) (PreH4 : (b_v <> 0)) (PreH5 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (b_v_father = fa)) (PreH9 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_6 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)) (PreH2 : (b_v_key >= x_pre)) (PreH3 : (x_pre >= b_v_key)) (PreH4 : (b_v <> 0)) (PreH5 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (b_v_father = fa)) (PreH9 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_7 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right <> 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (b_v <> 0)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_8 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (b_v_right <> 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (b_v <> 0)) (PreH7 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (b_v_father = fa)) (PreH11 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ False ”
.

Definition Delete_entail_wit_1 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 tr_low_level_spec )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  (store_ptb b_pre b_pre 0 0 pt0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 tr0 )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((combine_tree (empty_partial_tree) ((tree_delete (x_pre) (tr_low_level_spec)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition Delete_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (tr_low_level_spec: tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((combine_tree (empty_partial_tree) ((tree_delete (x_pre) (tr_low_level_spec)))) = (tree_delete (x_pre) (tr_low_level_spec)))
.

Definition Delete_entail_wit_2 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (PreH1 : (b_v_2 <> 0)) (PreH2 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0_2 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_father: Z)  (b_v_key: Z)  (pt0: partial_tree)  (tr0: tree)  (b_v: Z) ,
  “ (b_v <> 0) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (PreH1 : (b_v_2 <> 0)) (PreH2 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa 0 pt0_2 )
  **  (store_tree b_v_2 fa tr0_2 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_key: Z)  (pt0: partial_tree) ,
  “ (b_v_2 <> 0) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) ((make_tree (l0) (b_v_key) (b_v_value) (r0)))))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ”
  &&  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
).

Definition Delete_entail_wit_3 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_left_2 <> 0)) (PreH2 : (b_v_right_2 = 0)) (PreH3 : (b_v_key_2 >= x_pre)) (PreH4 : (x_pre >= b_v_key_2)) (PreH5 : (b_v <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key_2)) (PreH8 : (b_v_key_2 <= INT_MAX)) (PreH9 : (b_v_father_2 = fa)) (PreH10 : (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2)))) ,
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_left_right: Z)  (b_v_left_left: Z)  (l0: tree)  (b_v_left_value: Z)  (r0: tree)  (b_v_left_father: Z)  (b_v_left_key: Z)  (b_v_left: Z)  (tr0: tree)  (b_v_value: Z)  (r1: tree)  (b_v_father: Z)  (pt0: partial_tree)  (tr1: tree)  (b_v_key: Z)  (b_v_right: Z)  (b_v_2: Z) ,
  “ (b_v = b_v_2) ” 
  &&  “ (b_v_2 <> 0) ” 
  &&  “ (b_v_right = 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (tr0) (b_v_key) (b_v_value) (r1))) ” 
  &&  “ (b_v_left <> 0) ” 
  &&  “ (INT_MIN <= b_v_left_key) ” 
  &&  “ (b_v_left_key <= INT_MAX) ” 
  &&  “ (b_v_left_father = b_v_2) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_right b_v_2 r1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_left_father)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_left_2 <> 0)) (PreH2 : (b_v_right_2 = 0)) (PreH3 : (b_v_key_2 >= x_pre)) (PreH4 : (x_pre >= b_v_key_2)) (PreH5 : (b_v <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key_2)) (PreH8 : (b_v_key_2 <= INT_MAX)) (PreH9 : (b_v_father_2 = fa)) (PreH10 : (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2)))) ,
  (store_ptb b b_pre fa 0 pt0_2 )
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_left_right: Z)  (b_v_left_left: Z)  (l0: tree)  (b_v_left_value: Z)  (r0: tree)  (b_v_left_key: Z)  (r1: tree)  (pt0: partial_tree) ,
  “ (b_v_right_2 = 0) ” 
  &&  “ (b_v_father_2 = fa) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ (b_v_key_2 >= x_pre) ” 
  &&  “ (x_pre >= b_v_key_2) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) ((make_tree ((make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) (b_v_key_2) (b_v_value_2) (r1)))))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key_2) ” 
  &&  “ (b_v_key_2 <= INT_MAX) ” 
  &&  “ (b_v_left_2 <> 0) ” 
  &&  “ (INT_MIN <= b_v_left_key) ” 
  &&  “ (b_v_left_key <= INT_MAX) ”
  &&  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree 0 b_v r1 )
  **  ((&((b_v_left_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_left_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left_2 l0 )
  **  ((&((b_v_left_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left_2 r0 )
).

Definition Delete_entail_wit_4 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_right_2 <> 0)) (PreH2 : (b_v_left_2 = 0)) (PreH3 : (b_v_right_2 <> 0)) (PreH4 : (b_v_key_2 >= x_pre)) (PreH5 : (x_pre >= b_v_key_2)) (PreH6 : (b_v <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= b_v_key_2)) (PreH9 : (b_v_key_2 <= INT_MAX)) (PreH10 : (b_v_father_2 = fa)) (PreH11 : (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2)))) ,
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_father: Z)  (b_v_right_key: Z)  (b_v_right: Z)  (l1: tree)  (b_v_value: Z)  (tr0: tree)  (b_v_father: Z)  (pt0: partial_tree)  (tr1: tree)  (b_v_key: Z)  (b_v_left: Z)  (b_v_2: Z) ,
  “ (b_v = b_v_2) ” 
  &&  “ (b_v_2 <> 0) ” 
  &&  “ (b_v_left = 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0))) ” 
  &&  “ (b_v_right <> 0) ” 
  &&  “ (INT_MIN <= b_v_right_key) ” 
  &&  “ (b_v_right_key <= INT_MAX) ” 
  &&  “ (b_v_right_father = b_v_2) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v_2 l1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_right_2 <> 0)) (PreH2 : (b_v_left_2 = 0)) (PreH3 : (b_v_right_2 <> 0)) (PreH4 : (b_v_key_2 >= x_pre)) (PreH5 : (x_pre >= b_v_key_2)) (PreH6 : (b_v <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= b_v_key_2)) (PreH9 : (b_v_key_2 <= INT_MAX)) (PreH10 : (b_v_father_2 = fa)) (PreH11 : (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2)))) ,
  (store_ptb b b_pre fa 0 pt0_2 )
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_key: Z)  (l1: tree)  (pt0: partial_tree) ,
  “ (b_v_left_2 = 0) ” 
  &&  “ (b_v_father_2 = fa) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ (b_v_key_2 >= x_pre) ” 
  &&  “ (x_pre >= b_v_key_2) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) ((make_tree (l1) (b_v_key_2) (b_v_value_2) ((make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))))))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key_2) ” 
  &&  “ (b_v_key_2 <= INT_MAX) ” 
  &&  “ (b_v_right_2 <> 0) ” 
  &&  “ (INT_MIN <= b_v_right_key) ” 
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree 0 b_v l1 )
  **  ((&((b_v_right_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right_2 l0 )
  **  ((&((b_v_right_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right_2 r0 )
).

Definition Delete_entail_wit_5 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_left_2 <> 0)) (PreH2 : (b_v_right_2 <> 0)) (PreH3 : (b_v_key_2 >= x_pre)) (PreH4 : (x_pre >= b_v_key_2)) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key_2)) (PreH8 : (b_v_key_2 <= INT_MAX)) (PreH9 : (b_v_father_2 = fa)) (PreH10 : (tr0_2 = (make_tree (l0) (b_v_key_2) (b_v_value_2) (r0)))) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v_2 r0 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (tr0_left: tree)  (tr0_key: Z)  (tr0_value: Z)  (tr0_right: tree)  (l1_left: tree)  (l1_key: Z)  (l1_value: Z)  (l1_right: tree)  (l1: tree)  (b_v_value: Z)  (tr0: tree)  (b_v_father: Z)  (pt0: partial_tree)  (tr1: tree)  (b_v_key: Z)  (b_v: Z) ,
  “ (b_v <> 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0))) ” 
  &&  “ (l1 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right))) ” 
  &&  “ (tr0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right))) ” 
  &&  “ (b_v_left <> 0) ” 
  &&  “ (b_v_right <> 0) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key_2: Z) (b_v_father_2: Z) (fa: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) (PreH1 : (b_v_left_2 <> 0)) (PreH2 : (b_v_right_2 <> 0)) (PreH3 : (b_v_key_2 >= x_pre)) (PreH4 : (x_pre >= b_v_key_2)) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key_2)) (PreH8 : (b_v_key_2 <= INT_MAX)) (PreH9 : (b_v_father_2 = fa)) (PreH10 : (tr0_2 = (make_tree (l0) (b_v_key_2) (b_v_value_2) (r0)))) ,
  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (tr0_left: tree)  (tr0_key: Z)  (tr0_value: Z)  (tr0_right: tree)  (l1_left: tree)  (l1_key: Z)  (l1_value: Z)  (l1_right: tree)  (pt0: partial_tree) ,
  “ (l0 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right))) ” 
  &&  “ (r0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right))) ” 
  &&  “ (b_v_father_2 = fa) ” 
  &&  “ (b_v_2 <> 0) ” 
  &&  “ (b_v_key_2 >= x_pre) ” 
  &&  “ (x_pre >= b_v_key_2) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) ((make_tree ((make_tree (l1_left) (l1_key) (l1_value) (l1_right))) (b_v_key_2) (b_v_value_2) ((make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right)))))))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key_2) ” 
  &&  “ (b_v_key_2 <= INT_MAX) ” 
  &&  “ (b_v_left_2 <> 0) ” 
  &&  “ (b_v_right_2 <> 0) ”
  &&  (store_ptb b b_pre fa 0 pt0 )
).

Definition Delete_entail_wit_6_1 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (x_pre < b_v_key)) (PreH2 : (b_v_2 <> 0)) (PreH3 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= b_v_key)) (PreH5 : (b_v_key <= INT_MAX)) (PreH6 : (b_v_father = fa)) (PreH7 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (x_pre < b_v_key)) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (pt0: partial_tree) ,
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (l0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
).

Definition Delete_entail_wit_6_2 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_key < x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (b_v_2 <> 0)) (PreH4 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (b_v_father = fa)) (PreH8 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_key < x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (b_v_2 <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (b_v_father = fa)) (PreH11 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
|--
  EX (pt0: partial_tree) ,
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (r0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
).

Definition Delete_return_wit_1 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v = 0)) (PreH2 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v = 0)) (PreH2 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_2 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l1_left: tree) (l1_key: Z) (l1_value: Z) (l1_right: tree) (tr0_left: tree) (tr0_key: Z) (tr0_value: Z) (tr0_right: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (b_callee_v: Z) (ptr_callee_value: Z) (ptr_callee_key: Z) (PreH1 : (ptr_callee_key = (min_key (b_v_key) (tr0)))) (PreH2 : (ptr_callee_value = (min_value (b_v_value) (tr0)))) (PreH3 : (INT_MIN <= ptr_callee_key)) (PreH4 : (ptr_callee_key <= INT_MAX)) (PreH5 : (b_v <> 0)) (PreH6 : (b_v_key >= x_pre)) (PreH7 : (x_pre >= b_v_key)) (PreH8 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH13 : (l1 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right)))) (PreH14 : (tr0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right)))) (PreH15 : (b_v_left <> 0)) (PreH16 : (b_v_right <> 0)) ,
  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> ptr_callee_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> ptr_callee_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v b_v (delete_min (tr0)) )
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l1_left: tree) (l1_key: Z) (l1_value: Z) (l1_right: tree) (tr0_left: tree) (tr0_key: Z) (tr0_value: Z) (tr0_right: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (b_callee_v: Z) (ptr_callee_value: Z) (ptr_callee_key: Z) (PreH1 : (ptr_callee_value <= INT_MAX)) (PreH2 : (ptr_callee_value >= INT_MIN)) (PreH3 : (ptr_callee_key >= INT_MIN)) (PreH4 : (ptr_callee_key = (min_key (b_v_key) (tr0)))) (PreH5 : (ptr_callee_value = (min_value (b_v_value) (tr0)))) (PreH6 : (INT_MIN <= ptr_callee_key)) (PreH7 : (ptr_callee_key <= INT_MAX)) (PreH8 : (b_v <> 0)) (PreH9 : (b_v_key >= x_pre)) (PreH10 : (x_pre >= b_v_key)) (PreH11 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH12 : (INT_MIN <= b_v_key)) (PreH13 : (b_v_key <= INT_MAX)) (PreH14 : (b_v_father = fa)) (PreH15 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH16 : (l1 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right)))) (PreH17 : (tr0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right)))) (PreH18 : (b_v_left <> 0)) (PreH19 : (b_v_right <> 0)) ,
  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> ptr_callee_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> ptr_callee_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v b_v (delete_min (tr0)) )
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_3 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) (PreH1 : (to_free = b_v)) (PreH2 : (b_v <> 0)) (PreH3 : (b_v_left = 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH11 : (b_v_right <> 0)) (PreH12 : (INT_MIN <= b_v_right_key)) (PreH13 : (b_v_right_key <= INT_MAX)) (PreH14 : (b_v_right_father = b_v)) (PreH15 : (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) (PreH1 : (b_v_right_value <= INT_MAX)) (PreH2 : (b_v_right_value >= INT_MIN)) (PreH3 : (b_v_right_key >= INT_MIN)) (PreH4 : (to_free = b_v)) (PreH5 : (b_v <> 0)) (PreH6 : (b_v_left = 0)) (PreH7 : (b_v_key >= x_pre)) (PreH8 : (x_pre >= b_v_key)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= b_v_key)) (PreH11 : (b_v_key <= INT_MAX)) (PreH12 : (b_v_father = fa)) (PreH13 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH14 : (b_v_right <> 0)) (PreH15 : (INT_MIN <= b_v_right_key)) (PreH16 : (b_v_right_key <= INT_MAX)) (PreH17 : (b_v_right_father = b_v)) (PreH18 : (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_4 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (tr0: tree) (r1: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_right: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_left_key: Z) (b_v_left_father: Z) (b_v_left_value: Z) (b_v_left_left: Z) (b_v_left_right: Z) (PreH1 : (to_free = b_v)) (PreH2 : (b_v <> 0)) (PreH3 : (b_v_right = 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr1 = (make_tree (tr0) (b_v_key) (b_v_value) (r1)))) (PreH11 : (b_v_left <> 0)) (PreH12 : (INT_MIN <= b_v_left_key)) (PreH13 : (b_v_left_key <= INT_MAX)) (PreH14 : (b_v_left_father = b_v)) (PreH15 : (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_left)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_right b_v r1 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (tr0: tree) (r1: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_right: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_left_key: Z) (b_v_left_father: Z) (b_v_left_value: Z) (b_v_left_left: Z) (b_v_left_right: Z) (PreH1 : (b_v_left_value <= INT_MAX)) (PreH2 : (b_v_left_value >= INT_MIN)) (PreH3 : (b_v_left_key >= INT_MIN)) (PreH4 : (to_free = b_v)) (PreH5 : (b_v <> 0)) (PreH6 : (b_v_right = 0)) (PreH7 : (b_v_key >= x_pre)) (PreH8 : (x_pre >= b_v_key)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= b_v_key)) (PreH11 : (b_v_key <= INT_MAX)) (PreH12 : (b_v_father = fa)) (PreH13 : (tr1 = (make_tree (tr0) (b_v_key) (b_v_value) (r1)))) (PreH14 : (b_v_left <> 0)) (PreH15 : (INT_MIN <= b_v_left_key)) (PreH16 : (b_v_left_key <= INT_MAX)) (PreH17 : (b_v_left_father = b_v)) (PreH18 : (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_left)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_right b_v r1 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_5 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (b_v <> 0)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_left)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (b_v <> 0)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_left)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_partial_solve_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (tr0: tree) (r1: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_right: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_left_key: Z) (b_v_left_father: Z) (b_v_left_value: Z) (b_v_left_left: Z) (b_v_left_right: Z) (PreH1 : (to_free = b_v)) (PreH2 : (b_v <> 0)) (PreH3 : (b_v_right = 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr1 = (make_tree (tr0) (b_v_key) (b_v_value) (r1)))) (PreH11 : (b_v_left <> 0)) (PreH12 : (INT_MIN <= b_v_left_key)) (PreH13 : (b_v_left_key <= INT_MAX)) (PreH14 : (b_v_left_father = b_v)) (PreH15 : (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_right b_v r1 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
|--
  “ (to_free = b_v) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ (b_v_right = 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (tr0) (b_v_key) (b_v_value) (r1))) ” 
  &&  “ (b_v_left <> 0) ” 
  &&  “ (INT_MIN <= b_v_left_key) ” 
  &&  “ (b_v_left_key <= INT_MAX) ” 
  &&  “ (b_v_left_father = b_v) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) ”
  &&  ((&((to_free)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((to_free)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((to_free)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((to_free)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((to_free)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_left)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_right b_v r1 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
.

Definition Delete_partial_solve_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (b_v <> 0)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  “ (b_v_left = 0) ” 
  &&  “ (b_v_right = 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_left)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
.

Definition Delete_partial_solve_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) (PreH1 : (to_free = b_v)) (PreH2 : (b_v <> 0)) (PreH3 : (b_v_left = 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH11 : (b_v_right <> 0)) (PreH12 : (INT_MIN <= b_v_right_key)) (PreH13 : (b_v_right_key <= INT_MAX)) (PreH14 : (b_v_right_father = b_v)) (PreH15 : (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0)))) ,
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  “ (to_free = b_v) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ (b_v_left = 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0))) ” 
  &&  “ (b_v_right <> 0) ” 
  &&  “ (INT_MIN <= b_v_right_key) ” 
  &&  “ (b_v_right_key <= INT_MAX) ” 
  &&  “ (b_v_right_father = b_v) ” 
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((&((to_free)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((to_free)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((to_free)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((to_free)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((to_free)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition Delete_partial_solve_wit_4_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l1_left: tree) (l1_key: Z) (l1_value: Z) (l1_right: tree) (tr0_left: tree) (tr0_key: Z) (tr0_value: Z) (tr0_right: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v <> 0)) (PreH2 : (b_v_key >= x_pre)) (PreH3 : (x_pre >= b_v_key)) (PreH4 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (b_v_father = fa)) (PreH8 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH9 : (l1 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right)))) (PreH10 : (tr0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right)))) (PreH11 : (b_v_left <> 0)) (PreH12 : (b_v_right <> 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
|--
  “ (b_v <> 0) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_right <> 0) ”
.

Definition Delete_partial_solve_wit_4_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (pt0: partial_tree) (tr1: tree) (l1: tree) (tr0: tree) (l1_left: tree) (l1_key: Z) (l1_value: Z) (l1_right: tree) (tr0_left: tree) (tr0_key: Z) (tr0_value: Z) (tr0_right: tree) (b: Z) (b_v: Z) (b_v_key: Z) (b_v_father: Z) (fa: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (PreH1 : (b_v <> 0)) (PreH2 : (b_v_key >= x_pre)) (PreH3 : (x_pre >= b_v_key)) (PreH4 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (b_v_father = fa)) (PreH8 : (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0)))) (PreH9 : (l1 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right)))) (PreH10 : (tr0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right)))) (PreH11 : (b_v_left <> 0)) (PreH12 : (b_v_right <> 0)) ,
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
|--
  “ (b_v <> 0) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_right <> 0) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ (b_v_key >= x_pre) ” 
  &&  “ (x_pre >= b_v_key) ” 
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr1)))) = (tree_delete (x_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= b_v_key) ” 
  &&  “ (b_v_key <= INT_MAX) ” 
  &&  “ (b_v_father = fa) ” 
  &&  “ (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (tr0))) ” 
  &&  “ (l1 = (make_tree (l1_left) (l1_key) (l1_value) (l1_right))) ” 
  &&  “ (tr0 = (make_tree (tr0_left) (tr0_key) (tr0_value) (tr0_right))) ” 
  &&  “ (b_v_left <> 0) ” 
  &&  “ (b_v_right <> 0) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
.

Definition Delete_partial_solve_wit_4 := Delete_partial_solve_wit_4_pure -> Delete_partial_solve_wit_4_aux.

Definition Delete_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (b_pre: Z) (m_high_level_spec: mapping) ,
  EX b_pre_v,
  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (Bst.store_map b_pre_v m_high_level_spec )
|--
EX (tr_low_level_spec: tree) ,
  (EX b_callee_v,
  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v 0 tr_low_level_spec ))
  **
  ((EX b_callee_v_2,
  ((b_pre) # Ptr  |-> b_callee_v_2)
  **  (store_tree b_callee_v_2 0 (tree_delete (x_pre) (tr_low_level_spec)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (Bst.store_map b_pre_v_2 (map_delete (x_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_fp_Strategy_Correct.

Axiom proof_of_replace_min_safety_wit_1 : replace_min_safety_wit_1.
Axiom proof_of_replace_min_safety_wit_2 : replace_min_safety_wit_2.
Axiom proof_of_replace_min_safety_wit_3 : replace_min_safety_wit_3.
Axiom proof_of_replace_min_entail_wit_1 : replace_min_entail_wit_1.
Axiom proof_of_replace_min_entail_wit_2 : replace_min_entail_wit_2.
Axiom proof_of_replace_min_entail_wit_3 : replace_min_entail_wit_3.
Axiom proof_of_replace_min_entail_wit_4 : replace_min_entail_wit_4.
Axiom proof_of_replace_min_return_wit_1 : replace_min_return_wit_1.
Axiom proof_of_replace_min_return_wit_2 : replace_min_return_wit_2.
Axiom proof_of_replace_min_partial_solve_wit_1 : replace_min_partial_solve_wit_1.
Axiom proof_of_replace_min_partial_solve_wit_2 : replace_min_partial_solve_wit_2.
Axiom proof_of_Delete_safety_wit_1 : Delete_safety_wit_1.
Axiom proof_of_Delete_safety_wit_2 : Delete_safety_wit_2.
Axiom proof_of_Delete_safety_wit_3 : Delete_safety_wit_3.
Axiom proof_of_Delete_safety_wit_4 : Delete_safety_wit_4.
Axiom proof_of_Delete_safety_wit_5 : Delete_safety_wit_5.
Axiom proof_of_Delete_safety_wit_6 : Delete_safety_wit_6.
Axiom proof_of_Delete_safety_wit_7 : Delete_safety_wit_7.
Axiom proof_of_Delete_safety_wit_8 : Delete_safety_wit_8.
Axiom proof_of_Delete_entail_wit_1 : Delete_entail_wit_1.
Axiom proof_of_Delete_entail_wit_2 : Delete_entail_wit_2.
Axiom proof_of_Delete_entail_wit_3 : Delete_entail_wit_3.
Axiom proof_of_Delete_entail_wit_4 : Delete_entail_wit_4.
Axiom proof_of_Delete_entail_wit_5 : Delete_entail_wit_5.
Axiom proof_of_Delete_entail_wit_6_1 : Delete_entail_wit_6_1.
Axiom proof_of_Delete_entail_wit_6_2 : Delete_entail_wit_6_2.
Axiom proof_of_Delete_return_wit_1 : Delete_return_wit_1.
Axiom proof_of_Delete_return_wit_2 : Delete_return_wit_2.
Axiom proof_of_Delete_return_wit_3 : Delete_return_wit_3.
Axiom proof_of_Delete_return_wit_4 : Delete_return_wit_4.
Axiom proof_of_Delete_return_wit_5 : Delete_return_wit_5.
Axiom proof_of_Delete_partial_solve_wit_1 : Delete_partial_solve_wit_1.
Axiom proof_of_Delete_partial_solve_wit_2 : Delete_partial_solve_wit_2.
Axiom proof_of_Delete_partial_solve_wit_3 : Delete_partial_solve_wit_3.
Axiom proof_of_Delete_partial_solve_wit_4_pure : Delete_partial_solve_wit_4_pure.
Axiom proof_of_Delete_partial_solve_wit_4 : Delete_partial_solve_wit_4.
Axiom proof_of_Delete_derive_high_level_spec_by_low_level_spec : Delete_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
