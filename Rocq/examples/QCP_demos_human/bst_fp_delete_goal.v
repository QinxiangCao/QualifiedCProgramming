From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.bst_fp_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_strategy_proof.

(*----- Function replace_min -----*)

Definition replace_min_safety_wit_1 :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (tr = (combine_tree (pt0) (tr0)))) (PreH2 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH3 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH4 : (b_v_2 <> 0)) (PreH5 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH6 : (ptr_pre <> 0)) (PreH7 : (INT_MIN <= k)) (PreH8 : (k <= INT_MAX)) (PreH9 : (b_v <> 0)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_2 fa tr0 )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition replace_min_safety_wit_2 :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (INT_MIN <= b_v_key)) (PreH2 : (b_v_key <= INT_MAX)) (PreH3 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH4 : (tr = (combine_tree (pt0) (tr0)))) (PreH5 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH6 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH7 : (b_v_2 <> 0)) (PreH8 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH9 : (ptr_pre <> 0)) (PreH10 : (INT_MIN <= k)) (PreH11 : (k <= INT_MAX)) (PreH12 : (b_v <> 0)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition replace_min_safety_wit_3 :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (INT_MIN <= b_v_key)) (PreH3 : (b_v_key <= INT_MAX)) (PreH4 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH5 : (tr = (combine_tree (pt0) (tr0)))) (PreH6 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH7 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH8 : (b_v_2 <> 0)) (PreH9 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH10 : (ptr_pre <> 0)) (PreH11 : (INT_MIN <= k)) (PreH12 : (k <= INT_MAX)) (PreH13 : (b_v <> 0)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v_2)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition replace_min_entail_wit_1 :=
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_v <> 0)),
  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v ptr_pre tr )
|--
  EX (b_v_2: Z) (pt0: partial_tree) (tr0: tree),
  “ (tr = (combine_tree (pt0) (tr0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ”
  &&  “ (b_v_2 <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  ((b_pre) # Ptr  |-> b_v_2)
  **  (store_ptb b_pre b_pre ptr_pre ptr_pre pt0 )
  **  (store_tree b_v_2 ptr_pre tr0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
) \/
(
forall (k: Z) (tr: tree) (ptr_pre: Z) (b_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_v <> 0)),
  TT && emp 
|--
  “ ((delete_min (tr)) = (combine_tree (empty_partial_tree) ((delete_min (tr))))) ”
  &&  “ (tr = (combine_tree (empty_partial_tree) (tr))) ”
  &&  emp
).

Definition replace_min_entail_wit_1_split_goal_1 :=
forall (k: Z) (tr: tree) (ptr_pre: Z) (b_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_v <> 0)),
  ((delete_min (tr)) = (combine_tree (empty_partial_tree) ((delete_min (tr)))))
.

Definition replace_min_entail_wit_1_split_goal_2 :=
forall (k: Z) (tr: tree) (ptr_pre: Z) (b_v: Z) (PreH1 : (ptr_pre <> 0)) (PreH2 : (INT_MIN <= k)) (PreH3 : (k <= INT_MAX)) (PreH4 : (b_v <> 0)),
  (tr = (combine_tree (empty_partial_tree) (tr)))
.

Definition replace_min_entail_wit_2 :=
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_3: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left <> 0)) (PreH2 : (INT_MIN <= b_v_key)) (PreH3 : (b_v_key <= INT_MAX)) (PreH4 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH5 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH6 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH7 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH8 : (b_v_3 <> 0)) (PreH9 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) (PreH10 : (ptr_pre <> 0)) (PreH11 : (INT_MIN <= k)) (PreH12 : (k <= INT_MAX)) (PreH13 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v_3)
  **  ((&((b_v_3)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_3)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_3)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_3)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_3 l0 )
  **  ((&((b_v_3)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_3 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0_2 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  EX (b_v_2: Z) (pt0: partial_tree) (tr0: tree),
  “ (tr = (combine_tree (pt0) (tr0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ”
  &&  “ (b_v_2 <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  ((&((b_v_3)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_2)
  **  (store_ptb &((b_v_3)  # "tree" ->ₛ "left") b_pre b_v_3 ptr_pre pt0 )
  **  (store_tree b_v_2 b_v_3 tr0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
) \/
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_3: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_left <> 0)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (tr = (combine_tree (pt0_2) (tr0_2)))) (PreH9 : ((min_key (k) (tr)) = (min_key (k) (tr0_2)))) (PreH10 : ((min_value (v) (tr)) = (min_value (v) (tr0_2)))) (PreH11 : (b_v_3 <> 0)) (PreH12 : ((delete_min (tr)) = (combine_tree (pt0_2) ((delete_min (tr0_2)))))) (PreH13 : (ptr_pre <> 0)) (PreH14 : (INT_MIN <= k)) (PreH15 : (k <= INT_MAX)) (PreH16 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v_3)
  **  ((&((b_v_3)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_3)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_3)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_3)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_3 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0_2 )
|--
  EX (pt0: partial_tree),
  “ (tr = (combine_tree (pt0) (l0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (l0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (l0))) ”
  &&  “ (b_v_left <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (l0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  (store_ptb &((b_v_3)  # "tree" ->ₛ "left") b_pre b_v_3 ptr_pre pt0 )
).

Definition replace_min_return_wit_1 :=
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v_2: Z) (fa: Z) (b_v_3: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (INT_MIN <= b_v_right_key)) (PreH2 : (b_v_right_key <= INT_MAX)) (PreH3 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH4 : (b_v_right <> 0)) (PreH5 : (b_v_left = 0)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (tr = (combine_tree (pt0) (tr0)))) (PreH10 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH11 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH12 : (b_v_3 <> 0)) (PreH13 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH14 : (ptr_pre <> 0)) (PreH15 : (INT_MIN <= k)) (PreH16 : (k <= INT_MAX)) (PreH17 : (b_v_2 <> 0)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  (store_tree b_v_left b_v_3 l0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
|--
  EX (b_v: Z) (ptr_value: Z) (ptr_key: Z),
  “ (ptr_key = (min_key (k) (tr))) ”
  &&  “ (ptr_value = (min_value (v) (tr))) ”
  &&  “ (INT_MIN <= ptr_key) ”
  &&  “ (ptr_key <= INT_MAX) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> ptr_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> ptr_value)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v ptr_pre (delete_min (tr)) )
) \/
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v_2: Z) (fa: Z) (b_v_3: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (b_v_right_value <= INT_MAX)) (PreH2 : (b_v_right_value >= INT_MIN)) (PreH3 : (b_v_right_key >= INT_MIN)) (PreH4 : (INT_MIN <= b_v_right_key)) (PreH5 : (b_v_right_key <= INT_MAX)) (PreH6 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH7 : (b_v_right <> 0)) (PreH8 : (b_v_left = 0)) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH12 : (tr = (combine_tree (pt0) (tr0)))) (PreH13 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH14 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH15 : (b_v_3 <> 0)) (PreH16 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH17 : (ptr_pre <> 0)) (PreH18 : (INT_MIN <= k)) (PreH19 : (k <= INT_MAX)) (PreH20 : (b_v_2 <> 0)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  (store_tree b_v_left b_v_3 l0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
|--
  EX (b_v: Z),
  “ (b_v_value = (min_value (v) (tr))) ”
  &&  “ (b_v_key = (min_key (k) (tr))) ”
  &&  “ (b_v_value = (min_value (v) (tr))) ”
  &&  “ (b_v_key = (min_key (k) (tr))) ”
  &&  “ (INT_MIN <= (min_key (k) (tr))) ”
  &&  “ ((min_key (k) (tr)) <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v ptr_pre (delete_min (tr)) )
).

Definition replace_min_return_wit_2 :=
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v_2: Z) (fa: Z) (b_v_3: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (tr = (combine_tree (pt0) (tr0)))) (PreH7 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH8 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH9 : (b_v_3 <> 0)) (PreH10 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH11 : (ptr_pre <> 0)) (PreH12 : (INT_MIN <= k)) (PreH13 : (k <= INT_MAX)) (PreH14 : (b_v_2 <> 0)),
  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v_left b_v_3 l0 )
  **  (store_tree b_v_right b_v_3 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
|--
  EX (b_v: Z) (ptr_value: Z) (ptr_key: Z),
  “ (ptr_key = (min_key (k) (tr))) ”
  &&  “ (ptr_value = (min_value (v) (tr))) ”
  &&  “ (INT_MIN <= ptr_key) ”
  &&  “ (ptr_key <= INT_MAX) ”
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> ptr_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> ptr_value)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v ptr_pre (delete_min (tr)) )
) \/
(
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v_2: Z) (fa: Z) (b_v_3: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (tr = (combine_tree (pt0) (tr0)))) (PreH7 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH8 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH9 : (b_v_3 <> 0)) (PreH10 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH11 : (ptr_pre <> 0)) (PreH12 : (INT_MIN <= k)) (PreH13 : (k <= INT_MAX)) (PreH14 : (b_v_2 <> 0)),
  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v_left b_v_3 l0 )
  **  (store_tree b_v_right b_v_3 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
|--
  EX (b_v: Z),
  “ (b_v_value = (min_value (v) (tr))) ”
  &&  “ (b_v_key = (min_key (k) (tr))) ”
  &&  “ (b_v_value = (min_value (v) (tr))) ”
  &&  “ (b_v_key = (min_key (k) (tr))) ”
  &&  “ (INT_MIN <= (min_key (k) (tr))) ”
  &&  “ ((min_key (k) (tr)) <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v ptr_pre (delete_min (tr)) )
).

Definition replace_min_partial_solve_wit_1_pure :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v_2: Z) (fa: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (tr = (combine_tree (pt0) (tr0)))) (PreH2 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH3 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH4 : (b_v <> 0)) (PreH5 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH6 : (ptr_pre <> 0)) (PreH7 : (INT_MIN <= k)) (PreH8 : (k <= INT_MAX)) (PreH9 : (b_v_2 <> 0)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v fa tr0 )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (b_v <> 0) ”
.

Definition replace_min_partial_solve_wit_1_aux :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v_2: Z) (fa: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (tr = (combine_tree (pt0) (tr0)))) (PreH2 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH3 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH4 : (b_v <> 0)) (PreH5 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH6 : (ptr_pre <> 0)) (PreH7 : (INT_MIN <= k)) (PreH8 : (k <= INT_MAX)) (PreH9 : (b_v_2 <> 0)),
  ((b) # Ptr  |-> b_v)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v fa tr0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (b_v <> 0) ”
  &&  “ (tr = (combine_tree (pt0) (tr0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v_2 <> 0) ”
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
.

Definition replace_min_partial_solve_wit_1 := replace_min_partial_solve_wit_1_pure -> replace_min_partial_solve_wit_1_aux.

Definition replace_min_partial_solve_wit_2_pure :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right <> 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (tr = (combine_tree (pt0) (tr0)))) (PreH7 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH8 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH11 : (ptr_pre <> 0)) (PreH12 : (INT_MIN <= k)) (PreH13 : (k <= INT_MAX)) (PreH14 : (b_v <> 0)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v_2)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (b_v_right <> 0) ”
.

Definition replace_min_partial_solve_wit_2_aux :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right <> 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (tr = (combine_tree (pt0) (tr0)))) (PreH7 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH8 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH11 : (ptr_pre <> 0)) (PreH12 : (INT_MIN <= k)) (PreH13 : (k <= INT_MAX)) (PreH14 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
|--
  “ (b_v_right <> 0) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_left = 0) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (tr = (combine_tree (pt0) (tr0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ”
  &&  “ (b_v_2 <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
.

Definition replace_min_partial_solve_wit_2 := replace_min_partial_solve_wit_2_pure -> replace_min_partial_solve_wit_2_aux.

Definition replace_min_partial_solve_wit_3 :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (INT_MIN <= b_v_right_key)) (PreH2 : (b_v_right_key <= INT_MAX)) (PreH3 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH4 : (b_v_right <> 0)) (PreH5 : (b_v_left = 0)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (tr = (combine_tree (pt0) (tr0)))) (PreH10 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH11 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH12 : (b_v_2 <> 0)) (PreH13 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH14 : (ptr_pre <> 0)) (PreH15 : (INT_MIN <= k)) (PreH16 : (k <= INT_MAX)) (PreH17 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
|--
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2))) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_left = 0) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (tr = (combine_tree (pt0) (tr0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ”
  &&  “ (b_v_2 <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
.

Definition replace_min_partial_solve_wit_4 :=
forall (v: Z) (k: Z) (tr: tree) (b_pre: Z) (ptr_pre: Z) (b_v: Z) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (tr = (combine_tree (pt0) (tr0)))) (PreH7 : ((min_key (k) (tr)) = (min_key (k) (tr0)))) (PreH8 : ((min_value (v) (tr)) = (min_value (v) (tr0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0)))))) (PreH11 : (ptr_pre <> 0)) (PreH12 : (INT_MIN <= k)) (PreH13 : (k <= INT_MAX)) (PreH14 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
|--
  “ (b_v_right = 0) ”
  &&  “ (b_v_left = 0) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (tr = (combine_tree (pt0) (tr0))) ”
  &&  “ ((min_key (k) (tr)) = (min_key (k) (tr0))) ”
  &&  “ ((min_value (v) (tr)) = (min_value (v) (tr0))) ”
  &&  “ (b_v_2 <> 0) ”
  &&  “ ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) ”
  &&  “ (ptr_pre <> 0) ”
  &&  “ (INT_MIN <= k) ”
  &&  “ (k <= INT_MAX) ”
  &&  “ (b_v <> 0) ”
  &&  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
.

Definition replace_min_which_implies_wit_1 :=
(
forall (tr0: tree) (b: Z) (b_v: Z) (fa: Z) (PreH1 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z),
  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
) \/
(
forall (tr0: tree) (b_v: Z) (fa: Z) (PreH1 : (b_v <> 0)),
  (store_tree b_v fa tr0 )
|--
  EX (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z),
  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
).

Definition replace_min_which_implies_wit_2 :=
(
forall (tr0: tree) (b: Z) (b_v: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
|--
  EX (b_v_right_right: Z) (b_v_right_left: Z) (l0: tree) (b_v_right_value: Z) (r0: tree) (b_v_right_key: Z),
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
) \/
(
forall (tr0: tree) (b_v: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)),
  (store_tree b_v_right b_v tr0 )
|--
  EX (b_v_right_right: Z) (b_v_right_left: Z) (l0: tree) (b_v_right_value: Z) (r0: tree) (b_v_right_key: Z),
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
).

(*----- Function Delete -----*)

Definition Delete_safety_wit_1 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((( &( "fa" ) )) # Ptr  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_2 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Delete_safety_wit_3 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_4 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_key >= x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (b_v <> 0)) (PreH7 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= x_pre)) (PreH9 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_5 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_key >= x_pre)) (PreH3 : (x_pre >= b_v_key)) (PreH4 : (INT_MIN <= b_v_key)) (PreH5 : (b_v_key <= INT_MAX)) (PreH6 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH7 : (b_v <> 0)) (PreH8 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH9 : (INT_MIN <= x_pre)) (PreH10 : (x_pre <= INT_MAX)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_6 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right <> 0)) (PreH2 : (b_v_key >= x_pre)) (PreH3 : (x_pre >= b_v_key)) (PreH4 : (INT_MIN <= b_v_key)) (PreH5 : (b_v_key <= INT_MAX)) (PreH6 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH7 : (b_v <> 0)) (PreH8 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH9 : (INT_MIN <= x_pre)) (PreH10 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_7 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right <> 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Delete_safety_wit_8 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right = 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (b_v_right <> 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (b_v <> 0)) (PreH10 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ False ”
.

Definition Delete_entail_wit_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 0 tr_low_level_spec )
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb b_pre b_pre 0 0 pt0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 tr0 )
) \/
(
forall (tr_low_level_spec: tree) (x_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((combine_tree (empty_partial_tree) ((tree_delete (x_pre) (tr_low_level_spec)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition Delete_entail_wit_1_split_goal_1 :=
forall (tr_low_level_spec: tree) (x_pre: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((combine_tree (empty_partial_tree) ((tree_delete (x_pre) (tr_low_level_spec)))) = (tree_delete (x_pre) (tr_low_level_spec)))
.

Definition Delete_entail_wit_2_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (x_pre < b_v_key)) (PreH2 : (INT_MIN <= b_v_key)) (PreH3 : (b_v_key <= INT_MAX)) (PreH4 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (x_pre < b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v_2 <> 0)) (PreH9 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (pt0: partial_tree),
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (l0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
).

Definition Delete_entail_wit_2_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_key < x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (b_v_2 <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= x_pre)) (PreH9 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (b_v: Z) (pt0: partial_tree) (tr0: tree),
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_key < x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((combine_tree (pt0_2) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (pt0: partial_tree),
  “ ((combine_tree (pt0) ((tree_delete (x_pre) (r0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
).

Definition Delete_return_wit_1 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v_2 = 0)) (PreH2 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v_2 = 0)) (PreH2 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_2 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (b_v_3: Z) (ptr_value: Z) (ptr_key: Z) (PreH1 : (ptr_key = (min_key (b_v_key) ((make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))))) (PreH2 : (ptr_value = (min_value (b_v_value) ((make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))))) (PreH3 : (INT_MIN <= ptr_key)) (PreH4 : (ptr_key <= INT_MAX)) (PreH5 : (INT_MIN <= b_v_right_key)) (PreH6 : (b_v_right_key <= INT_MAX)) (PreH7 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH8 : (b_v_left <> 0)) (PreH9 : (b_v_right <> 0)) (PreH10 : (b_v_key >= x_pre)) (PreH11 : (x_pre >= b_v_key)) (PreH12 : (INT_MIN <= b_v_key)) (PreH13 : (b_v_key <= INT_MAX)) (PreH14 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH15 : (b_v_2 <> 0)) (PreH16 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH17 : (INT_MIN <= x_pre)) (PreH18 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> ptr_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> ptr_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_3)
  **  (store_tree b_v_3 b_v_2 (delete_min ((make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) )
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (b_v_3: Z) (ptr_value: Z) (ptr_key: Z) (PreH1 : (ptr_value <= INT_MAX)) (PreH2 : (ptr_value >= INT_MIN)) (PreH3 : (ptr_key >= INT_MIN)) (PreH4 : (ptr_key = (min_key (b_v_key) ((make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))))) (PreH5 : (ptr_value = (min_value (b_v_value) ((make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))))) (PreH6 : (INT_MIN <= ptr_key)) (PreH7 : (ptr_key <= INT_MAX)) (PreH8 : (INT_MIN <= b_v_right_key)) (PreH9 : (b_v_right_key <= INT_MAX)) (PreH10 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH11 : (b_v_left <> 0)) (PreH12 : (b_v_right <> 0)) (PreH13 : (b_v_key >= x_pre)) (PreH14 : (x_pre >= b_v_key)) (PreH15 : (INT_MIN <= b_v_key)) (PreH16 : (b_v_key <= INT_MAX)) (PreH17 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH18 : (b_v_2 <> 0)) (PreH19 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH20 : (INT_MIN <= x_pre)) (PreH21 : (x_pre <= INT_MAX)),
  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> ptr_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> ptr_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_3)
  **  (store_tree b_v_3 b_v_2 (delete_min ((make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) )
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_3 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (INT_MIN <= b_v_right_key)) (PreH2 : (b_v_right_key <= INT_MAX)) (PreH3 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH4 : (b_v_right <> 0)) (PreH5 : (b_v_left = 0)) (PreH6 : (b_v_right <> 0)) (PreH7 : (b_v_key >= x_pre)) (PreH8 : (x_pre >= b_v_key)) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH12 : (b_v_2 <> 0)) (PreH13 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH14 : (INT_MIN <= x_pre)) (PreH15 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (b_v_right_value <= INT_MAX)) (PreH2 : (b_v_right_value >= INT_MIN)) (PreH3 : (b_v_right_key >= INT_MIN)) (PreH4 : (INT_MIN <= b_v_right_key)) (PreH5 : (b_v_right_key <= INT_MAX)) (PreH6 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH7 : (b_v_right <> 0)) (PreH8 : (b_v_left = 0)) (PreH9 : (b_v_right <> 0)) (PreH10 : (b_v_key >= x_pre)) (PreH11 : (x_pre >= b_v_key)) (PreH12 : (INT_MIN <= b_v_key)) (PreH13 : (b_v_key <= INT_MAX)) (PreH14 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH15 : (b_v_2 <> 0)) (PreH16 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH17 : (INT_MIN <= x_pre)) (PreH18 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_4 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_left_right: Z) (b_v_left_left: Z) (l0_2: tree) (b_v_left_value: Z) (r0_2: tree) (b_v_left_key: Z) (PreH1 : (INT_MIN <= b_v_left_key)) (PreH2 : (b_v_left_key <= INT_MAX)) (PreH3 : (l0 = (make_tree (l0_2) (b_v_left_key) (b_v_left_value) (r0_2)))) (PreH4 : (b_v_left <> 0)) (PreH5 : (b_v_right = 0)) (PreH6 : (b_v_key >= x_pre)) (PreH7 : (x_pre >= b_v_key)) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH11 : (b_v_2 <> 0)) (PreH12 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH13 : (INT_MIN <= x_pre)) (PreH14 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0_2 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0_2 )
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_left_right: Z) (b_v_left_left: Z) (l0_2: tree) (b_v_left_value: Z) (r0_2: tree) (b_v_left_key: Z) (PreH1 : (b_v_left_value <= INT_MAX)) (PreH2 : (b_v_left_value >= INT_MIN)) (PreH3 : (b_v_left_key >= INT_MIN)) (PreH4 : (INT_MIN <= b_v_left_key)) (PreH5 : (b_v_left_key <= INT_MAX)) (PreH6 : (l0 = (make_tree (l0_2) (b_v_left_key) (b_v_left_value) (r0_2)))) (PreH7 : (b_v_left <> 0)) (PreH8 : (b_v_right = 0)) (PreH9 : (b_v_key >= x_pre)) (PreH10 : (x_pre >= b_v_key)) (PreH11 : (INT_MIN <= b_v_key)) (PreH12 : (b_v_key <= INT_MAX)) (PreH13 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH14 : (b_v_2 <> 0)) (PreH15 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH16 : (INT_MIN <= x_pre)) (PreH17 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0_2 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0_2 )
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_return_wit_5 :=
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v_2 <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
) \/
(
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v_2 <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_v: Z),
  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
).

Definition Delete_partial_solve_wit_1_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v <> 0)) (PreH2 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (b_v <> 0) ”
.

Definition Delete_partial_solve_wit_1_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v <> 0)) (PreH2 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)),
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  “ (b_v <> 0) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_1 := Delete_partial_solve_wit_1_pure -> Delete_partial_solve_wit_1_aux.

Definition Delete_partial_solve_wit_2_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left <> 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (b_v_left <> 0) ”
.

Definition Delete_partial_solve_wit_2_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left <> 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (b_v_left <> 0) ”
  &&  “ (b_v_left <> 0) ”
  &&  “ (b_v_right = 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_2 := Delete_partial_solve_wit_2_pure -> Delete_partial_solve_wit_2_aux.

Definition Delete_partial_solve_wit_3 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_left_right: Z) (b_v_left_left: Z) (l0_2: tree) (b_v_left_value: Z) (r0_2: tree) (b_v_left_key: Z) (PreH1 : (INT_MIN <= b_v_left_key)) (PreH2 : (b_v_left_key <= INT_MAX)) (PreH3 : (l0 = (make_tree (l0_2) (b_v_left_key) (b_v_left_value) (r0_2)))) (PreH4 : (b_v_left <> 0)) (PreH5 : (b_v_right = 0)) (PreH6 : (b_v_key >= x_pre)) (PreH7 : (x_pre >= b_v_key)) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH11 : (b_v <> 0)) (PreH12 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH13 : (INT_MIN <= x_pre)) (PreH14 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0_2 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (INT_MIN <= b_v_left_key) ”
  &&  “ (b_v_left_key <= INT_MAX) ”
  &&  “ (l0 = (make_tree (l0_2) (b_v_left_key) (b_v_left_value) (r0_2))) ”
  &&  “ (b_v_left <> 0) ”
  &&  “ (b_v_right = 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0_2 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0_2 )
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_4 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left = 0)) (PreH2 : (b_v_right = 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (b_v_left = 0) ”
  &&  “ (b_v_right = 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_5_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right <> 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (b_v_right <> 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (b_v <> 0)) (PreH10 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)),
  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (b_v_right <> 0) ”
.

Definition Delete_partial_solve_wit_5_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_right <> 0)) (PreH2 : (b_v_left = 0)) (PreH3 : (b_v_right <> 0)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (b_v <> 0)) (PreH10 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (b_v_right <> 0) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_left = 0) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_5 := Delete_partial_solve_wit_5_pure -> Delete_partial_solve_wit_5_aux.

Definition Delete_partial_solve_wit_6 :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (INT_MIN <= b_v_right_key)) (PreH2 : (b_v_right_key <= INT_MAX)) (PreH3 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH4 : (b_v_right <> 0)) (PreH5 : (b_v_left = 0)) (PreH6 : (b_v_right <> 0)) (PreH7 : (b_v_key >= x_pre)) (PreH8 : (x_pre >= b_v_key)) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH12 : (b_v <> 0)) (PreH13 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH14 : (INT_MIN <= x_pre)) (PreH15 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2))) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_left = 0) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_7_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left <> 0)) (PreH2 : (b_v_right <> 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (b_v_right <> 0) ”
.

Definition Delete_partial_solve_wit_7_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_left <> 0)) (PreH2 : (b_v_right <> 0)) (PreH3 : (b_v_key >= x_pre)) (PreH4 : (x_pre >= b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v <> 0)) (PreH9 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (b_v_right <> 0) ”
  &&  “ (b_v_left <> 0) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_7 := Delete_partial_solve_wit_7_pure -> Delete_partial_solve_wit_7_aux.

Definition Delete_partial_solve_wit_8_pure :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (INT_MIN <= b_v_right_key)) (PreH2 : (b_v_right_key <= INT_MAX)) (PreH3 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH4 : (b_v_left <> 0)) (PreH5 : (b_v_right <> 0)) (PreH6 : (b_v_key >= x_pre)) (PreH7 : (x_pre >= b_v_key)) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH11 : (b_v <> 0)) (PreH12 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH13 : (INT_MIN <= x_pre)) (PreH14 : (x_pre <= INT_MAX)),
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (b_v <> 0) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (b_v_right <> 0) ”
.

Definition Delete_partial_solve_wit_8_aux :=
forall (tr_low_level_spec: tree) (b_pre: Z) (x_pre: Z) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (b_v_right_right: Z) (b_v_right_left: Z) (l0_2: tree) (b_v_right_value: Z) (r0_2: tree) (b_v_right_key: Z) (PreH1 : (INT_MIN <= b_v_right_key)) (PreH2 : (b_v_right_key <= INT_MAX)) (PreH3 : (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)))) (PreH4 : (b_v_left <> 0)) (PreH5 : (b_v_right <> 0)) (PreH6 : (b_v_key >= x_pre)) (PreH7 : (x_pre >= b_v_key)) (PreH8 : (INT_MIN <= b_v_key)) (PreH9 : (b_v_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH11 : (b_v <> 0)) (PreH12 : ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec)))) (PreH13 : (INT_MIN <= x_pre)) (PreH14 : (x_pre <= INT_MAX)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0_2 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  “ (b_v <> 0) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (r0 = (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2))) ”
  &&  “ (b_v_left <> 0) ”
  &&  “ (b_v_right <> 0) ”
  &&  “ (b_v_key >= x_pre) ”
  &&  “ (x_pre >= b_v_key) ”
  &&  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  “ (b_v <> 0) ”
  &&  “ ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v (make_tree (l0_2) (b_v_right_key) (b_v_right_value) (r0_2)) )
  **  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition Delete_partial_solve_wit_8 := Delete_partial_solve_wit_8_pure -> Delete_partial_solve_wit_8_aux.

Definition Delete_which_implies_wit_1 :=
(
forall (tr0: tree) (b: Z) (b_v: Z) (fa: Z) (PreH1 : (b_v <> 0)),
  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z),
  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
) \/
(
forall (tr0: tree) (b_v: Z) (fa: Z) (PreH1 : (b_v <> 0)),
  (store_tree b_v fa tr0 )
|--
  EX (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z),
  “ (INT_MIN <= b_v_key) ”
  &&  “ (b_v_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
).

Definition Delete_which_implies_wit_2 :=
(
forall (tr0: tree) (b: Z) (b_v: Z) (b_v_left: Z) (PreH1 : (b_v_left <> 0)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v tr0 )
|--
  EX (b_v_left_right: Z) (b_v_left_left: Z) (l0: tree) (b_v_left_value: Z) (r0: tree) (b_v_left_key: Z),
  “ (INT_MIN <= b_v_left_key) ”
  &&  “ (b_v_left_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
) \/
(
forall (tr0: tree) (b_v: Z) (b_v_left: Z) (PreH1 : (b_v_left <> 0)),
  (store_tree b_v_left b_v tr0 )
|--
  EX (b_v_left_right: Z) (b_v_left_left: Z) (l0: tree) (b_v_left_value: Z) (r0: tree) (b_v_left_key: Z),
  “ (INT_MIN <= b_v_left_key) ”
  &&  “ (b_v_left_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) ”
  &&  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
).

Definition Delete_which_implies_wit_3 :=
(
forall (tr0: tree) (b: Z) (b_v: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
|--
  EX (b_v_right_right: Z) (b_v_right_left: Z) (l0: tree) (b_v_right_value: Z) (r0: tree) (b_v_right_key: Z),
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
) \/
(
forall (tr0: tree) (b_v: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)),
  (store_tree b_v_right b_v tr0 )
|--
  EX (b_v_right_right: Z) (b_v_right_left: Z) (l0: tree) (b_v_right_value: Z) (r0: tree) (b_v_right_key: Z),
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
).

Definition Delete_which_implies_wit_4 :=
(
forall (tr0: tree) (b: Z) (b_v: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)),
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v tr0 )
|--
  EX (b_v_right_right: Z) (b_v_right_left: Z) (l0: tree) (b_v_right_value: Z) (r0: tree) (b_v_right_key: Z),
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
) \/
(
forall (tr0: tree) (b_v: Z) (b_v_right: Z) (PreH1 : (b_v_right <> 0)),
  (store_tree b_v_right b_v tr0 )
|--
  EX (b_v_right_right: Z) (b_v_right_left: Z) (l0: tree) (b_v_right_value: Z) (r0: tree) (b_v_right_key: Z),
  “ (INT_MIN <= b_v_right_key) ”
  &&  “ (b_v_right_key <= INT_MAX) ”
  &&  “ (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) ”
  &&  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
).

(* Shallow FunAssertion specs for Delete. *)
Definition Delete_sig : FuncSig := ([ *  * struct "tree"; i32], void)%ctype.

Definition Delete_low_level_spec : Spec Delete_sig :=
  fun F =>
ALL (tr: tree),
HoareFun ([ *  * struct "tree"; i32], void)%ctype
  (fun '(b_pre, x_pre) =>
  (EX (b_v: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 tr )))
  (fun '(b_pre, x_pre) (_retval : unit) =>
  (EX (b_v_2: Z),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 0 (tree_delete (x_pre) (tr)) )))
  F.

Definition Delete_high_level_spec : Spec Delete_sig :=
  fun F =>
ALL (m: mapping),
HoareFun ([ *  * struct "tree"; i32], void)%ctype
  (fun '(b_pre, x_pre) =>
  (EX (b_v: Z),
  “ (INT_MIN <= x_pre) ”
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (Bst.store_map b_v m )))
  (fun '(b_pre, x_pre) (_retval : unit) =>
  (EX (b_v_2: Z),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (Bst.store_map b_v_2 (map_delete (x_pre) (m)) )))
  F.

Definition Delete_low_level_spec_entail_high_level_spec :=
forall (b_pre: Z) (x_pre: Z) (m_high_level_spec: mapping),
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
  **  (store_tree b_v_3 0 tr_low_level_spec ))
  **
  (  (EX (b_v_4: Z),
  ((b_pre) # Ptr  |-> b_v_4)
  **  (store_tree b_v_4 0 (tree_delete (x_pre) (tr_low_level_spec)) ))
  -*
  (EX (b_v_2: Z),
  ((b_pre) # Ptr  |-> b_v_2)
  **  (Bst.store_map b_v_2 (map_delete (x_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_fp_Strategy_Correct.

Axiom proof_of_replace_min_safety_wit_1 : replace_min_safety_wit_1.
Axiom proof_of_replace_min_safety_wit_2 : replace_min_safety_wit_2.
Axiom proof_of_replace_min_safety_wit_3 : replace_min_safety_wit_3.
Axiom proof_of_replace_min_entail_wit_1 : replace_min_entail_wit_1.
Axiom proof_of_replace_min_entail_wit_2 : replace_min_entail_wit_2.
Axiom proof_of_replace_min_return_wit_1 : replace_min_return_wit_1.
Axiom proof_of_replace_min_return_wit_2 : replace_min_return_wit_2.
Axiom proof_of_replace_min_partial_solve_wit_1_pure : replace_min_partial_solve_wit_1_pure.
Axiom proof_of_replace_min_partial_solve_wit_1 : replace_min_partial_solve_wit_1.
Axiom proof_of_replace_min_partial_solve_wit_2_pure : replace_min_partial_solve_wit_2_pure.
Axiom proof_of_replace_min_partial_solve_wit_2 : replace_min_partial_solve_wit_2.
Axiom proof_of_replace_min_partial_solve_wit_3 : replace_min_partial_solve_wit_3.
Axiom proof_of_replace_min_partial_solve_wit_4 : replace_min_partial_solve_wit_4.
Axiom proof_of_replace_min_which_implies_wit_1 : replace_min_which_implies_wit_1.
Axiom proof_of_replace_min_which_implies_wit_2 : replace_min_which_implies_wit_2.
Axiom proof_of_Delete_safety_wit_1 : Delete_safety_wit_1.
Axiom proof_of_Delete_safety_wit_2 : Delete_safety_wit_2.
Axiom proof_of_Delete_safety_wit_3 : Delete_safety_wit_3.
Axiom proof_of_Delete_safety_wit_4 : Delete_safety_wit_4.
Axiom proof_of_Delete_safety_wit_5 : Delete_safety_wit_5.
Axiom proof_of_Delete_safety_wit_6 : Delete_safety_wit_6.
Axiom proof_of_Delete_safety_wit_7 : Delete_safety_wit_7.
Axiom proof_of_Delete_safety_wit_8 : Delete_safety_wit_8.
Axiom proof_of_Delete_entail_wit_1 : Delete_entail_wit_1.
Axiom proof_of_Delete_entail_wit_2_1 : Delete_entail_wit_2_1.
Axiom proof_of_Delete_entail_wit_2_2 : Delete_entail_wit_2_2.
Axiom proof_of_Delete_return_wit_1 : Delete_return_wit_1.
Axiom proof_of_Delete_return_wit_2 : Delete_return_wit_2.
Axiom proof_of_Delete_return_wit_3 : Delete_return_wit_3.
Axiom proof_of_Delete_return_wit_4 : Delete_return_wit_4.
Axiom proof_of_Delete_return_wit_5 : Delete_return_wit_5.
Axiom proof_of_Delete_partial_solve_wit_1_pure : Delete_partial_solve_wit_1_pure.
Axiom proof_of_Delete_partial_solve_wit_1 : Delete_partial_solve_wit_1.
Axiom proof_of_Delete_partial_solve_wit_2_pure : Delete_partial_solve_wit_2_pure.
Axiom proof_of_Delete_partial_solve_wit_2 : Delete_partial_solve_wit_2.
Axiom proof_of_Delete_partial_solve_wit_3 : Delete_partial_solve_wit_3.
Axiom proof_of_Delete_partial_solve_wit_4 : Delete_partial_solve_wit_4.
Axiom proof_of_Delete_partial_solve_wit_5_pure : Delete_partial_solve_wit_5_pure.
Axiom proof_of_Delete_partial_solve_wit_5 : Delete_partial_solve_wit_5.
Axiom proof_of_Delete_partial_solve_wit_6 : Delete_partial_solve_wit_6.
Axiom proof_of_Delete_partial_solve_wit_7_pure : Delete_partial_solve_wit_7_pure.
Axiom proof_of_Delete_partial_solve_wit_7 : Delete_partial_solve_wit_7.
Axiom proof_of_Delete_partial_solve_wit_8_pure : Delete_partial_solve_wit_8_pure.
Axiom proof_of_Delete_partial_solve_wit_8 : Delete_partial_solve_wit_8.
Axiom proof_of_Delete_which_implies_wit_1 : Delete_which_implies_wit_1.
Axiom proof_of_Delete_which_implies_wit_2 : Delete_which_implies_wit_2.
Axiom proof_of_Delete_which_implies_wit_3 : Delete_which_implies_wit_3.
Axiom proof_of_Delete_which_implies_wit_4 : Delete_which_implies_wit_4.
Axiom proof_of_Delete_low_level_spec_entail_high_level_spec : Delete_low_level_spec_entail_high_level_spec.

End VC_Correct.
