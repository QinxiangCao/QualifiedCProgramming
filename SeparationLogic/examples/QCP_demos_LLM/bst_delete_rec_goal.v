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
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (INT_MIN <= t_key)) (PreH3 : (t_key <= INT_MAX)) (PreH4 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_pre_entail_wit_1 := 
(
forall (t_pre: Z) (tr: tree) (PreH1 : (t_pre <> 0)) ,
  (store_tree t_pre tr )
|--
  EX (t_right: Z)  (t_left: Z)  (l0: tree)  (t_value: Z)  (r0: tree)  (t_key: Z) ,
  “ (t_pre <> 0) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ” 
  &&  “ (tr = (make_tree (l0) (t_key) (t_value) (r0))) ”
  &&  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
) \/
(
forall (t_pre: Z) (tr: tree) (PreH1 : (t_pre <> 0)) ,
  (store_tree t_pre tr )
|--
  EX (t_right: Z)  (t_left: Z)  (l0: tree)  (t_value: Z)  (r0: tree)  (t_key: Z) ,
  “ (t_pre <> 0) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ” 
  &&  “ (tr = (make_tree (l0) (t_key) (t_value) (r0))) ”
  &&  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
).

Definition get_pre_return_wit_1 := 
(
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (retval_left_2: Z) (retval_right_2: Z) (pt_2: partial_tree) (tr_ret_left_2: tree) (retval_key_2: Z) (retval_value_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : forall (tr_ret_right: tree) , ((tree_pre_merge (r0) (tr_ret_right)) = (combine_tree (pt_2) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right)))))) (PreH3 : (retval_right_2 = 0)) (PreH4 : (INT_MIN <= retval_key_2)) (PreH5 : (retval_key_2 <= INT_MAX)) (PreH6 : (t_right <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (INT_MIN <= t_key)) (PreH9 : (t_key <= INT_MAX)) (PreH10 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value_2)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key_2)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right_2)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left_2)
  **  (store_tree retval_left_2 tr_ret_left_2 )
  **  (store_pt retval t_right pt_2 )
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
|--
  EX (retval_left: Z)  (retval_right: Z)  (pt: partial_tree)  (tr_ret_left: tree)  (retval_key: Z)  (retval_value: Z) ,
  “ (retval <> 0) ” 
  &&  “ forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) ” 
  &&  “ (retval_right = 0) ” 
  &&  “ (INT_MIN <= retval_key) ” 
  &&  “ (retval_key <= INT_MAX) ”
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval t_pre pt )
) \/
(
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (retval_right_2: Z) (pt_2: partial_tree) (tr_ret_left_2: tree) (retval_key_2: Z) (retval_value_2: Z) (retval: Z) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : forall (tr_ret_right: tree) , ((tree_pre_merge (r0) (tr_ret_right)) = (combine_tree (pt_2) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right)))))) (PreH6 : (retval_right_2 = 0)) (PreH7 : (INT_MIN <= retval_key_2)) (PreH8 : (retval_key_2 <= INT_MAX)) (PreH9 : (t_right <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (INT_MIN <= t_key)) (PreH12 : (t_key <= INT_MAX)) (PreH13 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  (store_pt retval t_right pt_2 )
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
|--
  EX (pt: partial_tree) ,
  “ (retval_right_2 = 0) ” 
  &&  “ (retval_right_2 = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right))))) ” 
  &&  “ (INT_MIN <= retval_key_2) ” 
  &&  “ (retval_key_2 <= INT_MAX) ”
  &&  (store_pt retval t_pre pt )
).

Definition get_pre_return_wit_2 := 
(
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (PreH1 : (t_right = 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  EX (retval_left: Z)  (retval_right: Z)  (pt: partial_tree)  (tr_ret_left: tree)  (retval_key: Z)  (retval_value: Z) ,
  “ (t_pre <> 0) ” 
  &&  “ forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) ” 
  &&  “ (retval_right = 0) ” 
  &&  “ (INT_MIN <= retval_key) ” 
  &&  “ (retval_key <= INT_MAX) ”
  &&  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt t_pre t_pre pt )
) \/
(
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_right: Z) (PreH1 : (t_right = 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  (store_tree t_right r0 )
|--
  EX (pt: partial_tree) ,
  “ (t_right = 0) ” 
  &&  “ (t_right = 0) ” 
  &&  “ (t_pre <> 0) ” 
  &&  “ forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (l0) (t_key) (t_value) (tr_ret_right))))) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ”
  &&  (store_pt t_pre t_pre pt )
).

Definition get_pre_partial_solve_wit_1_pure := 
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (PreH1 : (t_right <> 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  “ (t_right <> 0) ”
.

Definition get_pre_partial_solve_wit_1_aux := 
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (PreH1 : (t_right <> 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  “ (t_right <> 0) ” 
  &&  “ (t_right <> 0) ” 
  &&  “ (t_pre <> 0) ” 
  &&  “ (INT_MIN <= t_key) ” 
  &&  “ (t_key <= INT_MAX) ” 
  &&  “ (tr = (make_tree (l0) (t_key) (t_value) (r0))) ”
  &&  (store_tree t_right r0 )
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
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

Definition delete_safety_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH3 : (retval_right = 0)) (PreH4 : (INT_MIN <= retval_key)) (PreH5 : (retval_key <= INT_MAX)) (PreH6 : (p_left <> 0)) (PreH7 : (x_pre <= p_key)) (PreH8 : (x_pre >= p_key)) (PreH9 : (p = b_v)) (PreH10 : (p <> 0)) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((( &( "pre" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
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

Definition delete_return_wit_1 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) (PreH1 : (b_pre_v_2 = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 tr_low_level_spec )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) (PreH1 : (b_pre_v_2 = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (tr_low_level_spec = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition delete_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) (PreH1 : (b_pre_v_2 = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (tr_low_level_spec = (tree_delete (x_pre) (tr_low_level_spec)))
.

Definition delete_return_wit_2 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p <> 0)) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (l0)) )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v)) (PreH6 : (p <> 0)) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (l0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition delete_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v)) (PreH6 : (p <> 0)) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (l0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_3 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p <> 0)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (r0)) )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v)) (PreH7 : (p <> 0)) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (r0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition delete_return_wit_3_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v)) (PreH7 : (p <> 0)) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (r0)) )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)) )
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
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0 )
|--
  “ (r0 = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition delete_return_wit_4_split_goal_1 := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0 )
|--
  “ (r0 = (tree_delete (x_pre) (tr_low_level_spec))) ”
.

Definition delete_return_wit_4_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_left = 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0 )
|--
  TT && emp 
.

Definition delete_return_wit_5 := 
(
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH3 : (retval_right = 0)) (PreH4 : (INT_MIN <= retval_key)) (PreH5 : (retval_key <= INT_MAX)) (PreH6 : (p_left <> 0)) (PreH7 : (x_pre <= p_key)) (PreH8 : (x_pre >= p_key)) (PreH9 : (p = b_v)) (PreH10 : (p <> 0)) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((b_pre) # Ptr  |-> p_left)
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) (PreH1 : (retval_value <= INT_MAX)) (PreH2 : (retval_key >= INT_MIN)) (PreH3 : (retval_value >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH6 : (retval_right = 0)) (PreH7 : (INT_MIN <= retval_key)) (PreH8 : (retval_key <= INT_MAX)) (PreH9 : (p_left <> 0)) (PreH10 : (x_pre <= p_key)) (PreH11 : (x_pre >= p_key)) (PreH12 : (p = b_v)) (PreH13 : (p <> 0)) (PreH14 : (INT_MIN <= p_key)) (PreH15 : (p_key <= INT_MAX)) (PreH16 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  (store_tree p_right r0 )
|--
  (store_tree p_left (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition delete_return_wit_5_split_goal_spatial := 
forall (x_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) (PreH1 : (retval_value <= INT_MAX)) (PreH2 : (retval_key >= INT_MIN)) (PreH3 : (retval_value >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH6 : (retval_right = 0)) (PreH7 : (INT_MIN <= retval_key)) (PreH8 : (retval_key <= INT_MAX)) (PreH9 : (p_left <> 0)) (PreH10 : (x_pre <= p_key)) (PreH11 : (x_pre >= p_key)) (PreH12 : (p = b_v)) (PreH13 : (p <> 0)) (PreH14 : (INT_MIN <= p_key)) (PreH15 : (p_key <= INT_MAX)) (PreH16 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  (store_tree p_right r0 )
|--
  (store_tree p_left (tree_delete (x_pre) (tr_low_level_spec)) )
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
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (p_left <> 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "pre" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Int  |-> p_key)
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
  “ (p_left <> 0) ”
.

Definition delete_partial_solve_wit_4_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (p_left <> 0)) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p <> 0)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  “ (p_left <> 0) ” 
  &&  “ (p_left <> 0) ” 
  &&  “ (x_pre <= p_key) ” 
  &&  “ (x_pre >= p_key) ” 
  &&  “ (p = b_v) ” 
  &&  “ (p <> 0) ” 
  &&  “ (INT_MIN <= p_key) ” 
  &&  “ (p_key <= INT_MAX) ” 
  &&  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_4 := delete_partial_solve_wit_4_pure -> delete_partial_solve_wit_4_aux.

Definition delete_partial_solve_wit_5 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH3 : (retval_right = 0)) (PreH4 : (INT_MIN <= retval_key)) (PreH5 : (retval_key <= INT_MAX)) (PreH6 : (p_left <> 0)) (PreH7 : (x_pre <= p_key)) (PreH8 : (x_pre >= p_key)) (PreH9 : (p = b_v)) (PreH10 : (p <> 0)) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((b_pre) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree p_right r0 )
|--
  “ (retval <> 0) ” 
  &&  “ forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) ” 
  &&  “ (retval_right = 0) ” 
  &&  “ (INT_MIN <= retval_key) ” 
  &&  “ (retval_key <= INT_MAX) ” 
  &&  “ (p_left <> 0) ” 
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
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((b_pre) # Ptr  |-> p_left)
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
  **  (store_tree b_callee_v_2 (tree_delete (x_pre) (tr_low_level_spec)) ))
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
Axiom proof_of_delete_safety_wit_3 : delete_safety_wit_3.
Axiom proof_of_delete_entail_wit_1 : delete_entail_wit_1.
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
