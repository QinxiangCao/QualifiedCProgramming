From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.bst_lib.
Import get_right_most.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import bst_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import bst_strategy_proof.

(*----- Function insert -----*)

Definition insert_safety_wit_1 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition insert_safety_wit_2 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  ((( &( "p" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_3 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_4 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
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
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
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

Definition insert_entail_wit_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (PreH1 : (b_v <> 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0_2 )
|--
  EX (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (pt0: partial_tree) (tr0: tree) (b_v_2: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (b_v = b_v_2) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= p_key) ”
  &&  “ (p_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
) \/
(
forall (tr_low_level_spec: tree) (x_pre: Z) (value_pre: Z) (b_v: Z) (pt0_2: partial_tree) (tr0_2: tree) (PreH1 : (b_v <> 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  (store_tree b_v tr0_2 )
|--
  EX (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) ((make_tree (l0) (p_key) (p_value) (r0)))))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= p_key) ”
  &&  “ (p_key <= INT_MAX) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
).

Definition insert_entail_wit_3_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (p: Z) (b: Z) (b_v_2: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (x_pre < p_key)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (p = b_v_2)) (PreH5 : (p <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))),
  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0_2 )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p)  # "tree" ->ₛ "left") b_pre pt0 )
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (p: Z) (b: Z) (b_v_2: Z) (p_key: Z) (p_value: Z) (p_right: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (INT_MIN <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : (p = b_v_2)) (PreH8 : (p <> 0)) (PreH9 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= p_key)) (PreH11 : (p_key <= INT_MAX)) (PreH12 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))),
  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0_2 )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (pt0: partial_tree),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (l0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p)  # "tree" ->ₛ "left") b_pre pt0 )
).

Definition insert_entail_wit_3_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (p: Z) (b: Z) (b_v_2: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (p_key < x_pre)) (PreH2 : (x_pre >= p_key)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (p = b_v_2)) (PreH6 : (p <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))),
  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0_2 )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p)  # "tree" ->ₛ "right") b_pre pt0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (pt0_2: partial_tree) (tr0_2: tree) (l0: tree) (r0: tree) (p: Z) (b: Z) (b_v_2: Z) (p_key: Z) (p_value: Z) (p_left: Z) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (p_key < x_pre)) (PreH5 : (x_pre >= p_key)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : (p = b_v_2)) (PreH9 : (p <> 0)) (PreH10 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))),
  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0_2 )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  EX (pt0: partial_tree),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (r0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p)  # "tree" ->ₛ "right") b_pre pt0 )
).

Definition insert_return_wit_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (p: Z) (b: Z) (b_v_2: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (p_key >= x_pre)) (PreH2 : (x_pre >= p_key)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (p = b_v_2)) (PreH6 : (p <> 0)) (PreH7 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (p_key) (p_value) (r0)))),
  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0 )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (pt0: partial_tree) (tr0: tree) (l0: tree) (r0: tree) (p: Z) (b: Z) (b_v_2: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (p_key >= x_pre)) (PreH5 : (x_pre >= p_key)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : (p = b_v_2)) (PreH9 : (p <> 0)) (PreH10 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr0 = (make_tree (l0) (p_key) (p_value) (r0)))),
  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre pt0 )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v_2 = 0)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
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
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : (b_v_2 = 0)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
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
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (value_pre: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v = 0)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))),
  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  “ (b_v = 0) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
.

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
Axiom proof_of_insert_entail_wit_2 : insert_entail_wit_2.
Axiom proof_of_insert_entail_wit_3_1 : insert_entail_wit_3_1.
Axiom proof_of_insert_entail_wit_3_2 : insert_entail_wit_3_2.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_low_level_spec_entail_high_level_spec : insert_low_level_spec_entail_high_level_spec.

End VC_Correct.
