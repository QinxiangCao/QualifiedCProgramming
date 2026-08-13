import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.bst_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_insert_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open SimpleC.EE.QCP_demos_LLM.Bst
open scoped SimpleC.SL.SAC

local instance bst_insert_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def insert_safety_wit_1 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def insert_safety_wit_2 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((( &( "p" ) )) # Ptr |-> (b_v))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_3 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_v = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |->_)
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (retval))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_4 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_v = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (retval))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_entail_wit_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_pre_v : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v tr_low_level_spec)
|--
  EX b_v : Int, EX pt0 : partial_tree, EX tr0 : tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb b_pre b_pre pt0)
  ** ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((combine_tree (empty_partial_tree) ((tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  emp
)

noncomputable def insert_entail_wit_1_split_goal_1 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((combine_tree (empty_partial_tree) ((tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))

noncomputable def insert_entail_wit_2 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0_2 : partial_tree) (tr0_2 : tree) (PreH1 : (b_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre pt0_2)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0_2)
|--
  EX p_right : Int, EX p_left : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key : Int, EX pt0 : partial_tree, EX tr0 : tree, EX b_v_2 : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (b_v = b_v_2) ” &&
  “ (b_v ≠ (0 : Int)) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr0 = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre pt0)
  ** ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (pt0_2 : partial_tree) (tr0_2 : tree) (PreH1 : (b_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  (store_tree b_v tr0_2)
|--
  EX p_right : Int, EX p_left : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (b_v ≠ (0 : Int)) ” &&
  “ ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) ((make_tree (l0) (p_key) (p_value) (r0)))))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ”
  &&  ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
)

noncomputable def insert_entail_wit_3_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (p : Int) (b : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre pt0_2)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_v : Int, EX pt0 : partial_tree, EX tr0 : tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p # "tree")  ->ₛ "left") b_pre pt0)
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (p : Int) (b : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_right : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (INT_MIN <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : (p = b_v_2)) (PreH8 : (p ≠ (0 : Int))) (PreH9 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= p_key)) (PreH11 : (p_key <= INT_MAX)) (PreH12 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre pt0_2)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX pt0 : partial_tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (l0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p # "tree")  ->ₛ "left") b_pre pt0)
)

noncomputable def insert_entail_wit_3_2 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (p : Int) (b : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_key < x_pre)) (PreH2 : (x_pre >= p_key)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (p = b_v_2)) (PreH6 : (p ≠ (0 : Int))) (PreH7 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre pt0_2)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_v : Int, EX pt0 : partial_tree, EX tr0 : tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p # "tree")  ->ₛ "right") b_pre pt0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (p : Int) (b : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (p_key < x_pre)) (PreH5 : (x_pre >= p_key)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : (p = b_v_2)) (PreH9 : (p ≠ (0 : Int))) (PreH10 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre pt0_2)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  EX pt0 : partial_tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (r0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((p # "tree")  ->ₛ "right") b_pre pt0)
)

noncomputable def insert_return_wit_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0 : partial_tree) (tr0 : tree) (l0 : tree) (r0 : tree) (p : Int) (b : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_key >= x_pre)) (PreH2 : (x_pre >= p_key)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (p = b_v)) (PreH6 : (p ≠ (0 : Int))) (PreH7 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b) # Ptr |-> (b_v))
  ** (store_ptb b b_pre pt0)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0 : partial_tree) (tr0 : tree) (l0 : tree) (r0 : tree) (p : Int) (b : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (p_key >= x_pre)) (PreH5 : (x_pre >= p_key)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : (p = b_v)) (PreH9 : (p ≠ (0 : Int))) (PreH10 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr0 = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b) # Ptr |-> (b_v))
  ** (store_ptb b b_pre pt0)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_return_wit_2 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_v = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (retval))
  ** (store_tree b_v tr0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : (b_v = (0 : Int))) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (retval))
  ** (store_tree b_v tr0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_partial_solve_wit_1 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (pt0 : partial_tree) (tr0 : tree) (PreH1 : (b_v = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)
|--
  “ (b_v = (0 : Int)) ” &&
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb b b_pre pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v tr0)

noncomputable def insert_derive_high_level_spec_by_low_level_spec : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (m_high_level_spec : mapping) ,
  (EX b_pre_v : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr |-> (b_pre_v))
  ** (Bst.store_map b_pre_v m_high_level_spec))
|--
  EX tr_low_level_spec : tree,
  (EX b_callee_v : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v tr_low_level_spec))
  **
  ((EX b_callee_v_2 : Int,
  ((b_pre) # Ptr |-> (b_callee_v_2))
  ** (store_tree b_callee_v_2 (tree_insert (x_pre) (value_pre) (tr_low_level_spec))))
  -*
  (EX b_pre_v_2 : Int,
  ((b_pre) # Ptr |-> (b_pre_v_2))
  ** (Bst.store_map b_pre_v_2 (map_insert (x_pre) (value_pre) (m_high_level_spec)))))


structure VC_Correct : Type where
  proof_of_insert_safety_wit_1 : insert_safety_wit_1
  proof_of_insert_safety_wit_2 : insert_safety_wit_2
  proof_of_insert_safety_wit_3 : insert_safety_wit_3
  proof_of_insert_safety_wit_4 : insert_safety_wit_4
  proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1
  proof_of_insert_entail_wit_1 : insert_entail_wit_1
  proof_of_insert_entail_wit_2 : insert_entail_wit_2
  proof_of_insert_entail_wit_3_1 : insert_entail_wit_3_1
  proof_of_insert_entail_wit_3_2 : insert_entail_wit_3_2
  proof_of_insert_return_wit_1 : insert_return_wit_1
  proof_of_insert_return_wit_2 : insert_return_wit_2
  proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec

end SimpleC.EE.QCP_demos_LLM.generated.bst_insert_goal
