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
Require Import SimpleC.EE.QCP_demos_human.bst_fp_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import bst_fp_strategy_proof.

(*----- Function insert -----*)

Definition insert_safety_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "fa" ) )) # Ptr  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 tr_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_2 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition insert_safety_wit_3 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_4 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "father")) # Ptr  |->_)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_5 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "father")) # Ptr  |->_)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_entail_wit_1 := 
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 tr_low_level_spec )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb b_pre b_pre 0 0 pt0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 tr0 )
) \/
(
forall (value_pre: Z) (x_pre: Z) (tr_low_level_spec: tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((combine_tree (empty_partial_tree) ((tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  emp
).

Definition insert_entail_wit_1_split_goal_1 := 
forall (value_pre: Z) (x_pre: Z) (tr_low_level_spec: tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((combine_tree (empty_partial_tree) ((tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
.

Definition insert_entail_wit_2_1 := 
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (x_pre < b_v_key)) (PreH2 : (INT_MIN <= b_v_key)) (PreH3 : (b_v_key <= INT_MAX)) (PreH4 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH5 : (b_v_2 <> 0)) (PreH6 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) ,
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
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (x_pre < b_v_key)) (PreH5 : (INT_MIN <= b_v_key)) (PreH6 : (b_v_key <= INT_MAX)) (PreH7 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH8 : (b_v_2 <> 0)) (PreH9 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= x_pre)) (PreH11 : (x_pre <= INT_MAX)) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
  **  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (pt0: partial_tree) ,
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (l0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
).

Definition insert_entail_wit_2_2 := 
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_key < x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (b_v_2 <> 0)) (PreH7 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) ,
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
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
) \/
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0_2: partial_tree) (tr0_2: tree) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_key < x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (b_v_2 <> 0)) (PreH10 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)) ,
  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  (store_ptb b b_pre fa 0 pt0_2 )
|--
  EX (pt0: partial_tree) ,
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (r0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
).

Definition insert_return_wit_1 := 
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (b_v_key >= x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (INT_MIN <= b_v_key)) (PreH4 : (b_v_key <= INT_MAX)) (PreH5 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH6 : (b_v <> 0)) (PreH7 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) ,
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (b_v_right: Z) (b_v_left: Z) (l0: tree) (b_v_value: Z) (r0: tree) (b_v_key: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) (PreH9 : (b_v <> 0)) (PreH10 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= x_pre)) (PreH12 : (x_pre <= INT_MAX)) ,
  ((b) # Ptr  |-> b_v)
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
  **  (store_ptb b b_pre fa 0 pt0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_return_wit_2 := 
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (b_v = 0)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH4 : (INT_MIN <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
) \/
(
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval <> 0)) (PreH5 : (b_v = 0)) (PreH6 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) )
).

Definition insert_partial_solve_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v = 0)) (PreH2 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) ,
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  “ (b_v = 0) ” 
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
.

Definition insert_partial_solve_wit_2_pure := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v <> 0)) (PreH2 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) ,
  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (b_v <> 0) ”
.

Definition insert_partial_solve_wit_2_aux := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) (PreH1 : (b_v <> 0)) (PreH2 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) ,
  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  “ (b_v <> 0) ” 
  &&  “ (b_v <> 0) ” 
  &&  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” 
  &&  “ (INT_MIN <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ”
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  (store_ptb b b_pre fa 0 pt0 )
.

Definition insert_partial_solve_wit_2 := insert_partial_solve_wit_2_pure -> insert_partial_solve_wit_2_aux.

Definition insert_which_implies_wit_1 := 
(
forall (tr0: tree) (b: Z) (b_v: Z) (fa: Z) (PreH1 : (b_v <> 0)) ,
  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_key: Z) ,
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
forall (tr0: tree) (b_v: Z) (fa: Z) (PreH1 : (b_v <> 0)) ,
  (store_tree b_v fa tr0 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_key: Z) ,
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

Definition insert_derive_high_level_spec_by_low_level_spec := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (m_high_level_spec: mapping) ,
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
  **  (store_tree b_callee_v_2 0 (tree_insert (x_pre) (value_pre) (tr_low_level_spec)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (Bst.store_map b_pre_v_2 (map_insert (x_pre) (value_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_fp_Strategy_Correct.

Axiom proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Axiom proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Axiom proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Axiom proof_of_insert_safety_wit_4 : insert_safety_wit_4.
Axiom proof_of_insert_safety_wit_5 : insert_safety_wit_5.
Axiom proof_of_insert_entail_wit_1 : insert_entail_wit_1.
Axiom proof_of_insert_entail_wit_2_1 : insert_entail_wit_2_1.
Axiom proof_of_insert_entail_wit_2_2 : insert_entail_wit_2_2.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure.
Axiom proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Axiom proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Axiom proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
