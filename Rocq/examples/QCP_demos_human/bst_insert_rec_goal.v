From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.bst_lib.
Import get_right_most.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import bst_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import bst_strategy_proof.

(*----- Function insert -----*)

Definition insert_safety_wit_1 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  (store_tree b_pre tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_2 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  (store_tree b_pre tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_3 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  (store_tree b_pre tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_return_wit_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (b_key >= x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (INT_MIN <= b_key)) (PreH4 : (b_key <= INT_MAX)) (PreH5 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key >= x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (INT_MIN <= b_key)) (PreH7 : (b_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH9 : (b_pre <> 0)) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_1_split_goal_spatial :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key >= x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (INT_MIN <= b_key)) (PreH7 : (b_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH9 : (b_pre <> 0)) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
.

Definition insert_return_wit_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) (PreH1 : (b_key < x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (INT_MIN <= b_key)) (PreH4 : (b_key <= INT_MAX)) (PreH5 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> retval)
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key < x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (INT_MIN <= b_key)) (PreH7 : (b_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH9 : (b_pre <> 0)) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> retval)
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_2_split_goal_spatial :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key < x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (INT_MIN <= b_key)) (PreH7 : (b_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH9 : (b_pre <> 0)) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> retval)
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
.

Definition insert_return_wit_3 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) (PreH1 : (x_pre < b_key)) (PreH2 : (INT_MIN <= b_key)) (PreH3 : (b_key <= INT_MAX)) (PreH4 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH5 : (b_pre <> 0)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)),
  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (x_pre < b_key)) (PreH5 : (INT_MIN <= b_key)) (PreH6 : (b_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH8 : (b_pre <> 0)) (PreH9 : (INT_MIN <= x_pre)) (PreH10 : (x_pre <= INT_MAX)),
  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_3_split_goal_spatial :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (retval: Z) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (x_pre < b_key)) (PreH5 : (INT_MIN <= b_key)) (PreH6 : (b_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH8 : (b_pre <> 0)) (PreH9 : (INT_MIN <= x_pre)) (PreH10 : (x_pre <= INT_MAX)),
  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)) )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  (store_tree b_pre (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
.

Definition insert_return_wit_4 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_pre = 0)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree b_pre tr_low_level_spec )
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : (b_pre = 0)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree b_pre tr_low_level_spec )
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_4_split_goal_spatial :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : (b_pre = 0)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree b_pre tr_low_level_spec )
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
.

Definition insert_partial_solve_wit_1 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (PreH1 : (b_pre = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  (store_tree b_pre tr_low_level_spec )
|--
  “ (b_pre = 0) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_pre tr_low_level_spec )
.

Definition insert_partial_solve_wit_2_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  (store_tree b_pre tr_low_level_spec )
|--
  “ (b_pre <> 0) ”
.

Definition insert_partial_solve_wit_2_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (PreH1 : (b_pre <> 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  (store_tree b_pre tr_low_level_spec )
|--
  “ (b_pre <> 0) ”
  &&  “ (b_pre <> 0) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_pre tr_low_level_spec )
.

Definition insert_partial_solve_wit_2 := insert_partial_solve_wit_2_pure -> insert_partial_solve_wit_2_aux.

Definition insert_partial_solve_wit_3_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (x_pre < b_key)) (PreH2 : (INT_MIN <= b_key)) (PreH3 : (b_key <= INT_MAX)) (PreH4 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH5 : (b_pre <> 0)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
.

Definition insert_partial_solve_wit_3_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (x_pre < b_key)) (PreH2 : (INT_MIN <= b_key)) (PreH3 : (b_key <= INT_MAX)) (PreH4 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH5 : (b_pre <> 0)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)),
  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (x_pre < b_key) ”
  &&  “ (INT_MIN <= b_key) ”
  &&  “ (b_key <= INT_MAX) ”
  &&  “ (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
.

Definition insert_partial_solve_wit_3 := insert_partial_solve_wit_3_pure -> insert_partial_solve_wit_3_aux.

Definition insert_partial_solve_wit_4_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (b_key < x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (INT_MIN <= b_key)) (PreH4 : (b_key <= INT_MAX)) (PreH5 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
.

Definition insert_partial_solve_wit_4_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z) (PreH1 : (b_key < x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (INT_MIN <= b_key)) (PreH4 : (b_key <= INT_MAX)) (PreH5 : (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0)))) (PreH6 : (b_pre <> 0)) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
|--
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (b_key < x_pre) ”
  &&  “ (x_pre >= b_key) ”
  &&  “ (INT_MIN <= b_key) ”
  &&  “ (b_key <= INT_MAX) ”
  &&  “ (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  “ (b_pre <> 0) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_right r0 )
  **  ((&((b_pre)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b_pre)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b_pre)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b_pre)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
.

Definition insert_partial_solve_wit_4 := insert_partial_solve_wit_4_pure -> insert_partial_solve_wit_4_aux.

Definition insert_which_implies_wit_1 :=
(
forall (tr0: tree) (b: Z) (PreH1 : (b <> 0)),
  (store_tree b tr0 )
|--
  EX (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z),
  “ (INT_MIN <= b_key) ”
  &&  “ (b_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  ((&((b)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
) \/
(
forall (tr0: tree) (b: Z) (PreH1 : (b <> 0)),
  (store_tree b tr0 )
|--
  EX (b_right: Z) (b_left: Z) (l0: tree) (b_value: Z) (r0: tree) (b_key: Z),
  “ (INT_MIN <= b_key) ”
  &&  “ (b_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  ((&((b)  # "tree" ->ₛ "key")) # Int  |-> b_key)
  **  ((&((b)  # "tree" ->ₛ "value")) # Int  |-> b_value)
  **  ((&((b)  # "tree" ->ₛ "left")) # Ptr  |-> b_left)
  **  (store_tree b_left l0 )
  **  ((&((b)  # "tree" ->ₛ "right")) # Ptr  |-> b_right)
  **  (store_tree b_right r0 )
).

(* Shallow FunAssertion specs for insert. *)
Definition insert_sig : FuncSig := ([ * struct "tree"; i32; i32],  * struct "tree")%ctype.

Definition insert_low_level_spec : Spec insert_sig :=
  fun F =>
ALL (tr: tree),
HoareFun ([ * struct "tree"; i32; i32],  * struct "tree")%ctype
  (fun '(b_pre, (x_pre, value_pre)) =>
  (“ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_pre tr )))
  (fun '(b_pre, (x_pre, value_pre)) retval =>
  ((store_tree retval (tree_insert (x_pre) (value_pre) (tr)) )))
  F.

Definition insert_high_level_spec : Spec insert_sig :=
  fun F =>
ALL (m: mapping),
HoareFun ([ * struct "tree"; i32; i32],  * struct "tree")%ctype
  (fun '(b_pre, (x_pre, value_pre)) =>
  (“ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (Bst.store_map b_pre m )))
  (fun '(b_pre, (x_pre, value_pre)) retval =>
  ((Bst.store_map retval (map_insert (x_pre) (value_pre) (m)) )))
  F.

Definition insert_low_level_spec_entail_high_level_spec :=
forall (b_pre: Z) (x_pre: Z) (value_pre: Z) (m_high_level_spec: mapping),
  (“ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (Bst.store_map b_pre m_high_level_spec ))
|--
EX (tr_low_level_spec: tree),
  (“ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_pre tr_low_level_spec ))
  **
  (ALL (retval: Z),
  ((store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) ))
  -*
  ((Bst.store_map retval (map_insert (x_pre) (value_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.

Axiom proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Axiom proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Axiom proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_return_wit_3 : insert_return_wit_3.
Axiom proof_of_insert_return_wit_4 : insert_return_wit_4.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure.
Axiom proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Axiom proof_of_insert_partial_solve_wit_3_pure : insert_partial_solve_wit_3_pure.
Axiom proof_of_insert_partial_solve_wit_3 : insert_partial_solve_wit_3.
Axiom proof_of_insert_partial_solve_wit_4_pure : insert_partial_solve_wit_4_pure.
Axiom proof_of_insert_partial_solve_wit_4 : insert_partial_solve_wit_4.
Axiom proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Axiom proof_of_insert_low_level_spec_entail_high_level_spec : insert_low_level_spec_entail_high_level_spec.

End VC_Correct.
