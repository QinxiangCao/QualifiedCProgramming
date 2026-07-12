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
Require Import SimpleC.EE.QCP_demos_LLM.bst_lib.
Import get_right_most.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import bst_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import bst_strategy_proof.

(*----- Function get_pre -----*)

Definition get_pre_safety_wit_1 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v <> 0)) (PreH2 : (INT_MIN <= t_key)) (PreH3 : (t_key <= INT_MAX)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_pre_entail_wit_1 := 
(
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right <> 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  EX (t_v_right_right: Z)  (t_v_right_left: Z)  (t_v_left: Z)  (l0: tree)  (r0: tree)  (t_v: Z)  (t_k: Z)  (t_v_right: Z)  (t_v_2: Z) ,
  “ (t_v_2 <> 0) ” 
  &&  “ (t_v_right <> 0) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ” 
  &&  “ (INT_MIN <= t_k) ” 
  &&  “ (t_k <= INT_MAX) ” 
  &&  “ (t_right = (make_tree (l0) (t_k) (t_v) (r0))) ”
  &&  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
  **  ((&((t_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
) \/
(
forall (t_right: tree) (t_key: Z) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right <> 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  EX (t_v_right_right: Z)  (t_v_right_left: Z)  (l0: tree)  (r0: tree)  (t_v: Z)  (t_k: Z) ,
  “ (t_pre_v <> 0) ” 
  &&  “ (t_pre_v_right <> 0) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ” 
  &&  “ (INT_MIN <= t_k) ” 
  &&  “ (t_k <= INT_MAX) ” 
  &&  “ (t_right = (make_tree (l0) (t_k) (t_v) (r0))) ”
  &&  ((&((t_pre_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_pre_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
).

Definition get_pre_return_wit_1 := 
(
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (retval_v_left_2: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) (PreH1 : (retval_v_2 <> 0)) (PreH2 : (INT_MIN <= retval_v_key_2)) (PreH3 : (retval_v_key_2 <= INT_MAX)) (PreH4 : (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2)) (PreH5 : (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2)) (PreH6 : (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2)) (PreH8 : (retval_v_right_2 = 0)) (PreH9 : (t_v_2 <> 0)) (PreH10 : (t_v_right <> 0)) (PreH11 : (INT_MIN <= t_key)) (PreH12 : (t_key <= INT_MAX)) (PreH13 : (INT_MIN <= t_k)) (PreH14 : (t_k <= INT_MAX)) (PreH15 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  ((retval) # Ptr  |-> retval_v_2)
  **  ((&((retval_v_2)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key_2)
  **  ((&((retval_v_2)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value_2)
  **  ((&((retval_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right_2)
  **  (store_ptb retval &((t_v_2)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((&((retval_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left_2)
  **  (store_tree retval_v_left_2 ret_left_2 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
|--
  EX (retval_v_left: Z)  (retval_v_right: Z)  (ret_left: tree)  (t_pt: partial_tree)  (retval_v_value: Z)  (retval_v_key: Z)  (retval_v: Z) ,
  “ (retval_v <> 0) ” 
  &&  “ (INT_MIN <= retval_v_key) ” 
  &&  “ (retval_v_key <= INT_MAX) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = retval_v_key) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = retval_v_value) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) = t_pt) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = ret_left) ” 
  &&  “ (retval_v_right = 0) ”
  &&  ((retval) # Ptr  |-> retval_v)
  **  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  (store_ptb retval t_pre t_pt )
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  (store_tree retval_v_left ret_left )
) \/
(
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 <> 0)) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2)) (PreH11 : (retval_v_right_2 = 0)) (PreH12 : (t_v_2 <> 0)) (PreH13 : (t_v_right <> 0)) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = ret_left_2) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = retval_v_value_2) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = retval_v_key_2) ”
  &&  (store_ptb retval t_pre ((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) )
).

Definition get_pre_return_wit_1_split_goal_1 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 <> 0)) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2)) (PreH11 : (retval_v_right_2 = 0)) (PreH12 : (t_v_2 <> 0)) (PreH13 : (t_v_right <> 0)) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = ret_left_2) ”
.

Definition get_pre_return_wit_1_split_goal_2 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 <> 0)) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2)) (PreH11 : (retval_v_right_2 = 0)) (PreH12 : (t_v_2 <> 0)) (PreH13 : (t_v_right <> 0)) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = retval_v_value_2) ”
.

Definition get_pre_return_wit_1_split_goal_3 := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 <> 0)) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2)) (PreH11 : (retval_v_right_2 = 0)) (PreH12 : (t_v_2 <> 0)) (PreH13 : (t_v_right <> 0)) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = retval_v_key_2) ”
.

Definition get_pre_return_wit_1_split_goal_spatial := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (retval_v_right_2: Z) (ret_left_2: tree) (t_pt_2: partial_tree) (retval_v_value_2: Z) (retval_v_key_2: Z) (retval_v_2: Z) (retval: Z) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 <> 0)) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).(k) ) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).(v) ) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).(pt) ) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).(l_tree) ) = ret_left_2)) (PreH11 : (retval_v_right_2 = 0)) (PreH12 : (t_v_2 <> 0)) (PreH13 : (t_v_right <> 0)) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2)  # "tree" ->ₛ "right") t_pt_2 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
|--
  (store_ptb retval t_pre ((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) )
.

Definition get_pre_return_wit_2 := 
(
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_left: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  ((t_pre) # Ptr  |-> t_pre_v)
  **  ((&((t_pre_v)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre_v)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> t_pre_v_left)
  **  (store_tree t_pre_v_left t_left )
  **  ((&((t_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> t_pre_v_right)
  **  (store_tree t_pre_v_right t_right )
|--
  EX (retval_v_left: Z)  (retval_v_right: Z)  (ret_left: tree)  (t_pt: partial_tree)  (retval_v_value: Z)  (retval_v_key: Z)  (retval_v: Z) ,
  “ (retval_v <> 0) ” 
  &&  “ (INT_MIN <= retval_v_key) ” 
  &&  “ (retval_v_key <= INT_MAX) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = retval_v_key) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = retval_v_value) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) = t_pt) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = ret_left) ” 
  &&  “ (retval_v_right = 0) ”
  &&  ((t_pre) # Ptr  |-> retval_v)
  **  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  (store_ptb t_pre t_pre t_pt )
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  (store_tree retval_v_left ret_left )
) \/
(
forall (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = t_left) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) = empty_partial_tree) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = t_value) ” 
  &&  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = t_key) ”
  &&  emp
).

Definition get_pre_return_wit_2_split_goal_1 := 
forall (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(l_tree) ) = t_left) ”
.

Definition get_pre_return_wit_2_split_goal_2 := 
forall (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(pt) ) = empty_partial_tree) ”
.

Definition get_pre_return_wit_2_split_goal_3 := 
forall (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(v) ) = t_value) ”
.

Definition get_pre_return_wit_2_split_goal_4 := 
forall (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).(k) ) = t_key) ”
.

Definition get_pre_return_wit_2_split_goal_spatial := 
forall (t_right: tree) (t_key: Z) (t_pre_v: Z) (t_pre_v_right: Z) (PreH1 : (t_pre_v_right = 0)) (PreH2 : (t_pre_v <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right )
|--
  TT && emp 
.

Definition get_pre_partial_solve_wit_1_pure := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (t_v_right_left: Z) (t_v_right_right: Z) (PreH1 : (t_v_2 <> 0)) (PreH2 : (t_v_right <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (INT_MIN <= t_k)) (PreH6 : (t_k <= INT_MAX)) (PreH7 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
  **  ((&((t_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
|--
  “ (t_v_right <> 0) ” 
  &&  “ (INT_MIN <= t_k) ” 
  &&  “ (t_k <= INT_MAX) ”
.

Definition get_pre_partial_solve_wit_1_aux := 
forall (t_pre: Z) (t_right: tree) (t_value: Z) (t_key: Z) (t_left: tree) (l0: tree) (r0: tree) (t_k: Z) (t_v: Z) (t_v_2: Z) (t_v_right: Z) (t_v_left: Z) (t_v_right_left: Z) (t_v_right_right: Z) (PreH1 : (t_v_2 <> 0)) (PreH2 : (t_v_right <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (INT_MIN <= t_k)) (PreH6 : (t_k <= INT_MAX)) (PreH7 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
  **  ((&((t_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
|--
  “ (t_v_right <> 0) ” 
  &&  “ (INT_MIN <= t_k) ” 
  &&  “ (t_k <= INT_MAX) ” 
  &&  “ (t_v_2 <> 0) ” 
  &&  “ (t_v_right <> 0) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ” 
  &&  “ (INT_MIN <= t_k) ” 
  &&  “ (t_k <= INT_MAX) ” 
  &&  “ (t_right = (make_tree (l0) (t_k) (t_v) (r0))) ”
  &&  ((&((t_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right)
  **  ((&((t_v_right)  # "tree" ->ₛ "key")) # Int  |-> t_k)
  **  ((&((t_v_right)  # "tree" ->ₛ "value")) # Int  |-> t_v)
  **  ((&((t_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_right_left)
  **  (store_tree t_v_right_left l0 )
  **  ((&((t_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> t_v_right_right)
  **  (store_tree t_v_right_right r0 )
  **  ((t_pre) # Ptr  |-> t_v_2)
  **  ((&((t_v_2)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_v_2)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> t_v_left)
  **  (store_tree t_v_left t_left )
.

Definition get_pre_partial_solve_wit_1 := get_pre_partial_solve_wit_1_pure -> get_pre_partial_solve_wit_1_aux.

(*----- Function delete -----*)

Definition delete_safety_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition delete_safety_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (x_pre <= p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p <> 0)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition delete_entail_wit_1 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (b_pre_v <> 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr_low_level_spec )
|--
  EX (p_right: Z)  (p_left: Z)  (l0: tree)  (p_value: Z)  (r0: tree)  (p_key: Z)  (b_v: Z) ,
  “ (b_pre_v = b_v) ” 
  &&  “ (b_pre_v <> 0) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (b_pre_v <> 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (store_tree b_pre_v tr_low_level_spec )
|--
  EX (p_right: Z)  (p_left: Z)  (l0: tree)  (p_value: Z)  (r0: tree)  (p_key: Z) ,
  “ (b_pre_v <> 0) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
).

Definition delete_entail_wit_2 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0_2: tree) (r0_2: tree) (p: Z) (b_v_2: Z) (p_key: Z) (p_value_2: Z) (p_left_2: Z) (p_right_2: Z) (PreH1 : (p_left_2 <> 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0_2) (p_key) (p_value_2) (r0_2)))) ,
  ((b_pre) # Ptr  |-> b_v_2)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value_2)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_2)
  **  (store_tree p_left_2 l0_2 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right_2)
  **  (store_tree p_right_2 r0_2 )
|--
  EX (p_left_right: Z)  (p_left_left: Z)  (l0_left: tree)  (r0_left: tree)  (p_l_v: Z)  (p_l_k: Z)  (p_left: Z)  (p_right: Z)  (l0: tree)  (p_value: Z)  (r0: tree)  (p_key_2: Z)  (b_v: Z) ,
  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (x_pre = p_key) ” 
  &&  “ (p_key = p_key_2) ” 
  &&  “ (INT_MIN <= p_key_2) ” 
  &&  “ (p_key_2 <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key_2) (p_value) (r0))) ” 
  &&  “ (p_left <> 0) ” 
  &&  “ (INT_MIN <= p_l_k) ” 
  &&  “ (p_l_k <= INT_MAX) ” 
  &&  “ (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key_2)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0_left )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0_left )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0_2: tree) (r0_2: tree) (p: Z) (b_v_2: Z) (p_key: Z) (p_value_2: Z) (p_left_2: Z) (PreH1 : (p_left_2 <> 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0_2) (p_key) (p_value_2) (r0_2)))) ,
  (store_tree p_left_2 l0_2 )
|--
  EX (p_left_right: Z)  (p_left_left: Z)  (l0_left: tree)  (r0_left: tree)  (p_l_v: Z)  (p_l_k: Z) ,
  “ (p = b_v_2) ” 
  &&  “ (p <> 0) ” 
  &&  “ (x_pre = p_key) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree ((make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) (p_key) (p_value_2) (r0_2))) ” 
  &&  “ (p_left_2 <> 0) ” 
  &&  “ (INT_MIN <= p_l_k) ” 
  &&  “ (p_l_k <= INT_MAX) ”
  &&  ((&((p_left_2)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left_2)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0_left )
  **  ((&((p_left_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0_left )
).

Definition delete_return_wit_1 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) (PreH1 : (b_pre_v_2 = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 tr_low_level_spec )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) (PreH1 : (b_pre_v_2 = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (tr_low_level_spec = (tree_delete' (x_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition delete_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) (PreH1 : (b_pre_v_2 = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (tr_low_level_spec = (tree_delete' (x_pre) (tr_low_level_spec)))
.

Definition delete_return_wit_2 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p <> 0)) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete' (x_pre) (l0)) )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v)) (PreH6 : (p <> 0)) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete' (x_pre) (l0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)) )
).

Definition delete_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v)) (PreH6 : (p <> 0)) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete' (x_pre) (l0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_3 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p <> 0)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete' (x_pre) (r0)) )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v)) (PreH7 : (p <> 0)) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete' (x_pre) (r0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)) )
).

Definition delete_return_wit_3_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v)) (PreH7 : (p <> 0)) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete' (x_pre) (r0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_4 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr  |-> p_right)
  **  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0 )
|--
  “ (r0 = (tree_delete' (x_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition delete_return_wit_4_split_goal_1 := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0 )
|--
  “ (r0 = (tree_delete' (x_pre) (tr_low_level_spec))) ”
.

Definition delete_return_wit_4_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0 )
|--
  TT && emp 
.

Definition delete_return_wit_5 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (l0_left: tree) (r0_left: tree) (p_l_k: Z) (p_l_v: Z) (p: Z) (b_v: Z) (y: Z) (p_key: Z) (p_value: Z) (p_right: Z) (p_left: Z) (retval_v_left: Z) (retval_v_right: Z) (ret_left: tree) (t_pt: partial_tree) (retval_v_value: Z) (retval_v_key: Z) (retval_v: Z) (retval: Z) (PreH1 : (retval_v <> 0)) (PreH2 : (INT_MIN <= retval_v_key)) (PreH3 : (retval_v_key <= INT_MAX)) (PreH4 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(k) ) = retval_v_key)) (PreH5 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(v) ) = retval_v_value)) (PreH6 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(pt) ) = t_pt)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(l_tree) ) = ret_left)) (PreH8 : (retval_v_right = 0)) (PreH9 : (p = b_v)) (PreH10 : (p <> 0)) (PreH11 : (x_pre = y)) (PreH12 : (y = p_key)) (PreH13 : (INT_MIN <= p_key)) (PreH14 : (p_key <= INT_MAX)) (PreH15 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH16 : (p_left <> 0)) (PreH17 : (INT_MIN <= p_l_k)) (PreH18 : (p_l_k <= INT_MAX)) (PreH19 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr  |-> retval_v_left)
  **  (store_ptb retval &((p)  # "tree" ->ₛ "left") t_pt )
  **  (store_tree retval_v_left ret_left )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (l0_left: tree) (r0_left: tree) (p_l_k: Z) (p_l_v: Z) (p: Z) (b_v: Z) (y: Z) (p_key: Z) (p_value: Z) (p_right: Z) (p_left: Z) (retval_v_left: Z) (retval_v_right: Z) (ret_left: tree) (t_pt: partial_tree) (retval_v_value: Z) (retval_v_key: Z) (retval_v: Z) (retval: Z) (PreH1 : (retval_v_value <= INT_MAX)) (PreH2 : (retval_v_value >= INT_MIN)) (PreH3 : (retval_v_key >= INT_MIN)) (PreH4 : (retval_v <> 0)) (PreH5 : (INT_MIN <= retval_v_key)) (PreH6 : (retval_v_key <= INT_MAX)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(k) ) = retval_v_key)) (PreH8 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(v) ) = retval_v_value)) (PreH9 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(pt) ) = t_pt)) (PreH10 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(l_tree) ) = ret_left)) (PreH11 : (retval_v_right = 0)) (PreH12 : (p = b_v)) (PreH13 : (p <> 0)) (PreH14 : (x_pre = y)) (PreH15 : (y = p_key)) (PreH16 : (INT_MIN <= p_key)) (PreH17 : (p_key <= INT_MAX)) (PreH18 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH19 : (p_left <> 0)) (PreH20 : (INT_MIN <= p_l_k)) (PreH21 : (p_l_k <= INT_MAX)) (PreH22 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr  |-> retval_v_left)
  **  (store_ptb retval &((p)  # "tree" ->ₛ "left") t_pt )
  **  (store_tree retval_v_left ret_left )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)) )
).

Definition delete_return_wit_5_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (l0_left: tree) (r0_left: tree) (p_l_k: Z) (p_l_v: Z) (p: Z) (b_v: Z) (y: Z) (p_key: Z) (p_value: Z) (p_right: Z) (p_left: Z) (retval_v_left: Z) (retval_v_right: Z) (ret_left: tree) (t_pt: partial_tree) (retval_v_value: Z) (retval_v_key: Z) (retval_v: Z) (retval: Z) (PreH1 : (retval_v_value <= INT_MAX)) (PreH2 : (retval_v_value >= INT_MIN)) (PreH3 : (retval_v_key >= INT_MIN)) (PreH4 : (retval_v <> 0)) (PreH5 : (INT_MIN <= retval_v_key)) (PreH6 : (retval_v_key <= INT_MAX)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(k) ) = retval_v_key)) (PreH8 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(v) ) = retval_v_value)) (PreH9 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(pt) ) = t_pt)) (PreH10 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(l_tree) ) = ret_left)) (PreH11 : (retval_v_right = 0)) (PreH12 : (p = b_v)) (PreH13 : (p <> 0)) (PreH14 : (x_pre = y)) (PreH15 : (y = p_key)) (PreH16 : (INT_MIN <= p_key)) (PreH17 : (p_key <= INT_MAX)) (PreH18 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH19 : (p_left <> 0)) (PreH20 : (INT_MIN <= p_l_k)) (PreH21 : (p_l_k <= INT_MAX)) (PreH22 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr  |-> retval_v_left)
  **  (store_ptb retval &((p)  # "tree" ->ₛ "left") t_pt )
  **  (store_tree retval_v_left ret_left )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)) )
.

Definition delete_partial_solve_wit_1_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p <> 0)) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (x_pre <= INT_MAX) ” 
  &&  “ (INT_MIN <= x_pre) ”
.

Definition delete_partial_solve_wit_1_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p <> 0)) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (x_pre <= INT_MAX) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre < p_key) ” 
  &&  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_1 := delete_partial_solve_wit_1_pure -> delete_partial_solve_wit_1_aux.

Definition delete_partial_solve_wit_2_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p <> 0)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
.

Definition delete_partial_solve_wit_2_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p <> 0)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (x_pre > p_key) ” 
  &&  “ (x_pre >= p_key) ” 
  &&  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
.

Definition delete_partial_solve_wit_2 := delete_partial_solve_wit_2_pure -> delete_partial_solve_wit_2_aux.

Definition delete_partial_solve_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr  |-> p_right)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (p_left = 0) ” 
  &&  “ (x_pre <= p_key) ” 
  &&  “ (x_pre >= p_key) ” 
  &&  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((b_pre) # Ptr  |-> p_right)
  **  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_4_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (l0_left: tree) (r0_left: tree) (p_l_k: Z) (p_l_v: Z) (p: Z) (b_v: Z) (y: Z) (p_key: Z) (p_value: Z) (p_right: Z) (p_left: Z) (p_left_left: Z) (p_left_right: Z) (PreH1 : (p = b_v)) (PreH2 : (p <> 0)) (PreH3 : (x_pre = y)) (PreH4 : (y = p_key)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH8 : (p_left <> 0)) (PreH9 : (INT_MIN <= p_l_k)) (PreH10 : (p_l_k <= INT_MAX)) (PreH11 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((( &( "pre" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0_left )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0_left )
|--
  “ (p_left <> 0) ” 
  &&  “ (INT_MIN <= p_l_k) ” 
  &&  “ (p_l_k <= INT_MAX) ”
.

Definition delete_partial_solve_wit_4_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (l0_left: tree) (r0_left: tree) (p_l_k: Z) (p_l_v: Z) (p: Z) (b_v: Z) (y: Z) (p_key: Z) (p_value: Z) (p_right: Z) (p_left: Z) (p_left_left: Z) (p_left_right: Z) (PreH1 : (p = b_v)) (PreH2 : (p <> 0)) (PreH3 : (x_pre = y)) (PreH4 : (y = p_key)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH8 : (p_left <> 0)) (PreH9 : (INT_MIN <= p_l_k)) (PreH10 : (p_l_k <= INT_MAX)) (PreH11 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0_left )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0_left )
|--
  “ (p_left <> 0) ” 
  &&  “ (INT_MIN <= p_l_k) ” 
  &&  “ (p_l_k <= INT_MAX) ” 
  &&  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (x_pre = y) ” 
  &&  “ (y = p_key) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ” 
  &&  “ (p_left <> 0) ” 
  &&  “ (INT_MIN <= p_l_k) ” 
  &&  “ (p_l_k <= INT_MAX) ” 
  &&  “ (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) ”
  &&  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p_left)  # "tree" ->ₛ "key")) # Int  |-> p_l_k)
  **  ((&((p_left)  # "tree" ->ₛ "value")) # Int  |-> p_l_v)
  **  ((&((p_left)  # "tree" ->ₛ "left")) # Ptr  |-> p_left_left)
  **  (store_tree p_left_left l0_left )
  **  ((&((p_left)  # "tree" ->ₛ "right")) # Ptr  |-> p_left_right)
  **  (store_tree p_left_right r0_left )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_4 := delete_partial_solve_wit_4_pure -> delete_partial_solve_wit_4_aux.

Definition delete_partial_solve_wit_5 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (l0_left: tree) (r0_left: tree) (p_l_k: Z) (p_l_v: Z) (p: Z) (b_v: Z) (y: Z) (p_key: Z) (p_value: Z) (p_right: Z) (p_left: Z) (retval_v_left: Z) (retval_v_right: Z) (ret_left: tree) (t_pt: partial_tree) (retval_v_value: Z) (retval_v_key: Z) (retval_v: Z) (retval: Z) (PreH1 : (retval_v <> 0)) (PreH2 : (INT_MIN <= retval_v_key)) (PreH3 : (retval_v_key <= INT_MAX)) (PreH4 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(k) ) = retval_v_key)) (PreH5 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(v) ) = retval_v_value)) (PreH6 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(pt) ) = t_pt)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(l_tree) ) = ret_left)) (PreH8 : (retval_v_right = 0)) (PreH9 : (p = b_v)) (PreH10 : (p <> 0)) (PreH11 : (x_pre = y)) (PreH12 : (y = p_key)) (PreH13 : (INT_MIN <= p_key)) (PreH14 : (p_key <= INT_MAX)) (PreH15 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH16 : (p_left <> 0)) (PreH17 : (INT_MIN <= p_l_k)) (PreH18 : (p_l_k <= INT_MAX)) (PreH19 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr  |-> retval_v_left)
  **  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  (store_ptb retval &((p)  # "tree" ->ₛ "left") t_pt )
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  (store_tree retval_v_left ret_left )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (retval_v <> 0) ” 
  &&  “ (INT_MIN <= retval_v_key) ” 
  &&  “ (retval_v_key <= INT_MAX) ” 
  &&  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(k) ) = retval_v_key) ” 
  &&  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(v) ) = retval_v_value) ” 
  &&  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(pt) ) = t_pt) ” 
  &&  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).(l_tree) ) = ret_left) ” 
  &&  “ (retval_v_right = 0) ” 
  &&  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (x_pre = y) ” 
  &&  “ (y = p_key) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ” 
  &&  “ (p_left <> 0) ” 
  &&  “ (INT_MIN <= p_l_k) ” 
  &&  “ (p_l_k <= INT_MAX) ” 
  &&  “ (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) ”
  &&  ((&((retval_v)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((retval_v)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((retval_v)  # "tree" ->ₛ "left")) # Ptr  |-> retval_v_left)
  **  ((&((retval_v)  # "tree" ->ₛ "right")) # Ptr  |-> retval_v_right)
  **  ((retval) # Ptr  |-> retval_v_left)
  **  (store_ptb retval &((p)  # "tree" ->ₛ "left") t_pt )
  **  (store_tree retval_v_left ret_left )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> retval_v_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> retval_v_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_derive_high_level_spec_by_low_level_spec := 
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
  **  (store_tree b_callee_v tr_low_level_spec ))
  **
  ((EX b_callee_v_2,
  ((b_pre) # Ptr  |-> b_callee_v_2)
  **  (store_tree b_callee_v_2 (tree_delete' (x_pre) (tr_low_level_spec)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (Bst.store_map b_pre_v_2 (map_delete (x_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.

Axiom proof_of_get_pre_safety_wit_1 : get_pre_safety_wit_1.
Axiom proof_of_get_pre_entail_wit_1 : get_pre_entail_wit_1.
Axiom proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Axiom proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Axiom proof_of_get_pre_partial_solve_wit_1_pure : get_pre_partial_solve_wit_1_pure.
Axiom proof_of_get_pre_partial_solve_wit_1 : get_pre_partial_solve_wit_1.
Axiom proof_of_delete_safety_wit_1 : delete_safety_wit_1.
Axiom proof_of_delete_safety_wit_2 : delete_safety_wit_2.
Axiom proof_of_delete_entail_wit_1 : delete_entail_wit_1.
Axiom proof_of_delete_entail_wit_2 : delete_entail_wit_2.
Axiom proof_of_delete_return_wit_1 : delete_return_wit_1.
Axiom proof_of_delete_return_wit_2 : delete_return_wit_2.
Axiom proof_of_delete_return_wit_3 : delete_return_wit_3.
Axiom proof_of_delete_return_wit_4 : delete_return_wit_4.
Axiom proof_of_delete_return_wit_5 : delete_return_wit_5.
Axiom proof_of_delete_partial_solve_wit_1_pure : delete_partial_solve_wit_1_pure.
Axiom proof_of_delete_partial_solve_wit_1 : delete_partial_solve_wit_1.
Axiom proof_of_delete_partial_solve_wit_2_pure : delete_partial_solve_wit_2_pure.
Axiom proof_of_delete_partial_solve_wit_2 : delete_partial_solve_wit_2.
Axiom proof_of_delete_partial_solve_wit_3 : delete_partial_solve_wit_3.
Axiom proof_of_delete_partial_solve_wit_4_pure : delete_partial_solve_wit_4_pure.
Axiom proof_of_delete_partial_solve_wit_4 : delete_partial_solve_wit_4.
Axiom proof_of_delete_partial_solve_wit_5 : delete_partial_solve_wit_5.
Axiom proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
