From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.bst_lib.
Import get_right_most.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import bst_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import bst_strategy_proof.

(*----- Function insert -----*)

Definition insert_safety_wit_1 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition insert_safety_wit_2 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((( &( "p" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_3 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= x_pre)) (PreH5 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_4 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= x_pre)) (PreH5 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_entail_wit_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 tr_low_level_spec )
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb b_pre b_pre pt0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
) \/
(
forall (tr_low_level_spec: tree) (x_pre: Z) (value_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((combine_tree (empty_partial_tree) ((tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition insert_entail_wit_1_split_goal_1 :=
forall (tr_low_level_spec: tree) (x_pre: Z) (value_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((combine_tree (empty_partial_tree) ((tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
.

Definition insert_entail_wit_2_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (PreH1 : (x_pre < p_key)) (PreH2 : (INT_MIN <= p_key)) (PreH3 : (p_key <= INT_MAX)) (PreH4 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (p_right: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH8 : (b_v_2 <> 0)) (PreH9 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (pt0: partial_tree),
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (l0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre pt0 )
).

Definition insert_entail_wit_2_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (PreH1 : (p_key < x_pre)) (PreH2 : (x_pre >= p_key)) (PreH3 : (INT_MIN <= p_key)) (PreH4 : (p_key <= INT_MAX)) (PreH5 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH6 : (b_v_2 <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= x_pre)) (PreH9 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (p_key < x_pre)) (PreH5 : (x_pre >= p_key)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (pt0: partial_tree),
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (r0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre pt0 )
).

Definition insert_return_wit_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (PreH1 : (p_key >= x_pre)) (PreH2 : (x_pre >= p_key)) (PreH3 : (INT_MIN <= p_key)) (PreH4 : (p_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH6 : (b_v_2 <> 0)) (PreH7 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= x_pre)) (PreH9 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (p_key >= x_pre)) (PreH5 : (x_pre >= p_key)) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v_2 = 0)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= x_pre)) (PreH5 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v_2 tr0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : (b_v_2 = 0)) (PreH6 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v_2 tr0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_partial_solve_wit_1 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v = 0)) (PreH2 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  “ (b_v = 0) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
.

Definition insert_partial_solve_wit_2_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v <> 0)) (PreH2 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  ((( &( "p" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (b_v <> 0) ”
.

Definition insert_partial_solve_wit_2_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v <> 0)) (PreH2 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  “ (b_v <> 0) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_v tr0 )
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
.

Definition insert_partial_solve_wit_2 := insert_partial_solve_wit_2_pure -> insert_partial_solve_wit_2_aux.

Definition insert_which_implies_wit_1 :=
(
forall (tr0: tree) (p: Z) (PreH1 : (p <> 0)),
  (store_tree p tr0 )
|--
  EX (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z),
  “ (INT_MIN <= p_key) ”
  &&  “ (p_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
) \/
(
forall (tr0: tree) (p: Z) (PreH1 : (p <> 0)),
  (store_tree p tr0 )
|--
  EX (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z),
  “ (INT_MIN <= p_key) ”
  &&  “ (p_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
).

(* Shallow FunAssertion specs for insert. *)
Definition insert_sig : FuncSig := ([ *  * struct "tree"; i32; i32], void)%ctype.

Definition insert_low_level_spec : Spec insert_sig :=
  fun F =>
ALL (tr: tree),
HoareFun ([ *  * struct "tree"; i32; i32], void)%ctype
  (fun '(b_pre, (x_pre, value_pre)) =>
  (EX (b_v: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v tr )))
  (fun '(b_pre, (x_pre, value_pre)) (_retval : unit) =>
  (EX (b_v_2: Z),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 (tree_insert (x_pre) (value_pre) (tr)) )))
  F.

Definition insert_high_level_spec : Spec insert_sig :=
  fun F =>
ALL (m: mapping),
HoareFun ([ *  * struct "tree"; i32; i32], void)%ctype
  (fun '(b_pre, (x_pre, value_pre)) =>
  (EX (b_v: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (Bst.store_map b_v m )))
  (fun '(b_pre, (x_pre, value_pre)) (_retval : unit) =>
  (EX (b_v_2: Z),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (Bst.store_map b_v_2 (map_insert (x_pre) (value_pre) (m)) )))
  F.

Definition insert_low_level_spec_entail_high_level_spec :=
forall (b_pre: Z) (x_pre: Z) (value_pre: Z) (m_high_level_spec: mapping),
  (EX (b_v: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (Bst.store_map b_v m_high_level_spec ))
|--
EX (tr_low_level_spec: tree),
  (EX (b_v_3: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v_3)
  **  (store_tree b_v_3 tr_low_level_spec ))
  **
  (  (EX (b_v_4: Z),
  ((b_pre) # Ptr  |-> b_v_4)
  **  (store_tree b_v_4 (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) ))
  -*
  (EX (b_v_2: Z),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (Bst.store_map b_v_2 (map_insert (x_pre) (value_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.

Axiom proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Axiom proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Axiom proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Axiom proof_of_insert_safety_wit_4 : insert_safety_wit_4.
Axiom proof_of_insert_entail_wit_1 : insert_entail_wit_1.
Axiom proof_of_insert_entail_wit_2_1 : insert_entail_wit_2_1.
Axiom proof_of_insert_entail_wit_2_2 : insert_entail_wit_2_2.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure.
Axiom proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Axiom proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Axiom proof_of_insert_low_level_spec_entail_high_level_spec : insert_low_level_spec_entail_high_level_spec.

End VC_Correct.
