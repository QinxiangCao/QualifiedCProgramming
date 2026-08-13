import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.bst_fp_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_fp_insert_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bst_fp_insert_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_pre_v : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "fa" ) )) # Ptr |->_)
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (0 : Int) tr_low_level_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_2 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "fa" ) )) # Ptr |-> (fa))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v fa tr0)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def insert_safety_wit_3 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "fa" ) )) # Ptr |-> (fa))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v fa tr0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_4 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_v = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |->_)
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |->_)
  ** ((&((retval # "tree")  ->ₛ "father")) # Ptr |->_)
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "fa" ) )) # Ptr |-> (fa))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (retval))
  ** (store_tree b_v fa tr0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_5 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_v = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |->_)
  ** ((&((retval # "tree")  ->ₛ "father")) # Ptr |->_)
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "fa" ) )) # Ptr |-> (fa))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (retval))
  ** (store_tree b_v fa tr0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_entail_wit_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_pre_v : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (0 : Int) tr_low_level_spec)
|--
  EX b_v : Int, EX pt0 : partial_tree, EX tr0 : tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb b_pre b_pre (0 : Int) (0 : Int) pt0)
  ** ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v (0 : Int) tr0)
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
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v_2 : Int) (b : Int) (fa : Int) (pt0_2 : partial_tree) (tr0_2 : tree) (PreH1 : (b_v_2 ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa (0 : Int) pt0_2)
  ** ((b) # Ptr |-> (b_v_2))
  ** (store_tree b_v_2 fa tr0_2)
|--
  EX b_v_right : Int, EX b_v_left : Int, EX l0 : tree, EX b_v_value : Int, EX r0 : tree, EX b_v_father : Int, EX b_v_key : Int, EX pt0 : partial_tree, EX tr0 : tree, EX b_v : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (b_v ≠ (0 : Int)) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” &&
  “ (INT_MIN <= b_v_key) ” &&
  “ (b_v_key <= INT_MAX) ” &&
  “ (b_v_father = fa) ” &&
  “ (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) ”
  &&  ((b) # Ptr |-> (b_v))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (b_v_value))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v r0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v_2 : Int) (b : Int) (fa : Int) (pt0_2 : partial_tree) (tr0_2 : tree) (PreH1 : (b_v_2 ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa (0 : Int) pt0_2)
  ** (store_tree b_v_2 fa tr0_2)
|--
  EX b_v_right : Int, EX b_v_left : Int, EX l0 : tree, EX b_v_value : Int, EX r0 : tree, EX b_v_key : Int, EX pt0 : partial_tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (b_v_2 ≠ (0 : Int)) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) ((make_tree (l0) (b_v_key) (b_v_value) (r0)))))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ” &&
  “ (INT_MIN <= b_v_key) ” &&
  “ (b_v_key <= INT_MAX) ”
  &&  (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((&((b_v_2 # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v_2 # "tree")  ->ₛ "father")) # Ptr |-> (fa))
  ** ((&((b_v_2 # "tree")  ->ₛ "value")) # Int |-> (b_v_value))
  ** ((&((b_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v_2 l0)
  ** ((&((b_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v_2 r0)
)

noncomputable def insert_entail_wit_3_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_v_2 : Int) (fa : Int) (b_v_key : Int) (b_v_father : Int) (b_v_value : Int) (b_v_left : Int) (b_v_right : Int) (PreH1 : (x_pre < b_v_key)) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (b_v_2 ≠ (0 : Int))) (PreH5 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH6 : (INT_MIN <= b_v_key)) (PreH7 : (b_v_key <= INT_MAX)) (PreH8 : (b_v_father = fa)) (PreH9 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre fa (0 : Int) pt0_2)
  ** ((&((b_v_2 # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v_2 # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v_2 # "tree")  ->ₛ "value")) # Int |-> (b_v_value))
  ** ((&((b_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v_2 l0)
  ** ((&((b_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v_2 r0)
|--
  EX b_v : Int, EX pt0 : partial_tree, EX tr0 : tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2 # "tree")  ->ₛ "left") b_pre b_v_2 (0 : Int) pt0)
  ** ((&((b_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (b_v))
  ** (store_tree b_v b_v_2 tr0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_v_2 : Int) (fa : Int) (b_v_key : Int) (b_v_father : Int) (b_v_value : Int) (b_v_right : Int) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (x_pre < b_v_key)) (PreH5 : (INT_MIN <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : (b_v_2 ≠ (0 : Int))) (PreH8 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH9 : (INT_MIN <= b_v_key)) (PreH10 : (b_v_key <= INT_MAX)) (PreH11 : (b_v_father = fa)) (PreH12 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre fa (0 : Int) pt0_2)
  ** ((&((b_v_2 # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v_2 # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v_2 # "tree")  ->ₛ "value")) # Int |-> (b_v_value))
  ** ((&((b_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v_2 r0)
|--
  EX pt0 : partial_tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (l0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2 # "tree")  ->ₛ "left") b_pre b_v_2 (0 : Int) pt0)
)

noncomputable def insert_entail_wit_3_2 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_v_2 : Int) (fa : Int) (b_v_key : Int) (b_v_father : Int) (b_v_value : Int) (b_v_left : Int) (b_v_right : Int) (PreH1 : (b_v_key < x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (b_v_2 ≠ (0 : Int))) (PreH6 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre fa (0 : Int) pt0_2)
  ** ((&((b_v_2 # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v_2 # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v_2 # "tree")  ->ₛ "value")) # Int |-> (b_v_value))
  ** ((&((b_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v_2 l0)
  ** ((&((b_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v_2 r0)
|--
  EX b_v : Int, EX pt0 : partial_tree, EX tr0 : tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2 # "tree")  ->ₛ "right") b_pre b_v_2 (0 : Int) pt0)
  ** ((&((b_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (b_v))
  ** (store_tree b_v b_v_2 tr0)
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0_2 : partial_tree) (tr0_2 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_v_2 : Int) (fa : Int) (b_v_key : Int) (b_v_father : Int) (b_v_value : Int) (b_v_left : Int) (PreH1 : (b_v_value <= INT_MAX)) (PreH2 : (b_v_value >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_key < x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : (b_v_2 ≠ (0 : Int))) (PreH9 : ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= b_v_key)) (PreH11 : (b_v_key <= INT_MAX)) (PreH12 : (b_v_father = fa)) (PreH13 : (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr |-> (b_v_2))
  ** (store_ptb b b_pre fa (0 : Int) pt0_2)
  ** ((&((b_v_2 # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v_2 # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v_2 # "tree")  ->ₛ "value")) # Int |-> (b_v_value))
  ** ((&((b_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v_2 l0)
|--
  EX pt0 : partial_tree,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (r0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb &((b_v_2 # "tree")  ->ₛ "right") b_pre b_v_2 (0 : Int) pt0)
)

noncomputable def insert_return_wit_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0 : partial_tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_v : Int) (fa : Int) (b_v_key : Int) (b_v_father : Int) (b_v_value : Int) (b_v_left : Int) (b_v_right : Int) (PreH1 : (b_v_key >= x_pre)) (PreH2 : (x_pre >= b_v_key)) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (b_v ≠ (0 : Int))) (PreH6 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH7 : (INT_MIN <= b_v_key)) (PreH8 : (b_v_key <= INT_MAX)) (PreH9 : (b_v_father = fa)) (PreH10 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr |-> (b_v))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (0 : Int) (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (pt0 : partial_tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_v : Int) (fa : Int) (b_v_key : Int) (b_v_father : Int) (b_v_value : Int) (b_v_left : Int) (b_v_right : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (b_v_key >= INT_MIN)) (PreH4 : (b_v_key >= x_pre)) (PreH5 : (x_pre >= b_v_key)) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : (b_v ≠ (0 : Int))) (PreH9 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) (PreH10 : (INT_MIN <= b_v_key)) (PreH11 : (b_v_key <= INT_MAX)) (PreH12 : (b_v_father = fa)) (PreH13 : (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0)))) ,
  ((b) # Ptr |-> (b_v))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (b_v_key))
  ** ((&((b_v # "tree")  ->ₛ "father")) # Ptr |-> (b_v_father))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (b_v_left))
  ** (store_tree b_v_left b_v l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (b_v_right))
  ** (store_tree b_v_right b_v r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (0 : Int) (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_return_wit_2 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_v = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "father")) # Ptr |-> (fa))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (retval))
  ** (store_tree b_v fa tr0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (0 : Int) (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (retval : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : (b_v = (0 : Int))) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "father")) # Ptr |-> (fa))
  ** (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (retval))
  ** (store_tree b_v fa tr0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (0 : Int) (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_partial_solve_wit_1 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_v : Int) (b : Int) (fa : Int) (pt0 : partial_tree) (tr0 : tree) (PreH1 : (b_v = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))) ,
  (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v fa tr0)
|--
  “ (b_v = (0 : Int)) ” &&
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr_low_level_spec))) ”
  &&  (store_ptb b b_pre fa (0 : Int) pt0)
  ** ((b) # Ptr |-> (b_v))
  ** (store_tree b_v fa tr0)

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
  ** (store_tree b_callee_v (0 : Int) tr_low_level_spec))
  **
  ((EX b_callee_v_2 : Int,
  ((b_pre) # Ptr |-> (b_callee_v_2))
  ** (store_tree b_callee_v_2 (0 : Int) (tree_insert (x_pre) (value_pre) (tr_low_level_spec))))
  -*
  (EX b_pre_v_2 : Int,
  ((b_pre) # Ptr |-> (b_pre_v_2))
  ** (Bst.store_map b_pre_v_2 (map_insert (x_pre) (value_pre) (m_high_level_spec)))))


structure VC_Correct : Type where
  proof_of_insert_safety_wit_1 : insert_safety_wit_1
  proof_of_insert_safety_wit_2 : insert_safety_wit_2
  proof_of_insert_safety_wit_3 : insert_safety_wit_3
  proof_of_insert_safety_wit_4 : insert_safety_wit_4
  proof_of_insert_safety_wit_5 : insert_safety_wit_5
  proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1
  proof_of_insert_entail_wit_1 : insert_entail_wit_1
  proof_of_insert_entail_wit_2 : insert_entail_wit_2
  proof_of_insert_entail_wit_3_1 : insert_entail_wit_3_1
  proof_of_insert_entail_wit_3_2 : insert_entail_wit_3_2
  proof_of_insert_return_wit_1 : insert_return_wit_1
  proof_of_insert_return_wit_2 : insert_return_wit_2
  proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec

end SimpleC.EE.QCP_demos_LLM.generated.bst_fp_insert_goal
