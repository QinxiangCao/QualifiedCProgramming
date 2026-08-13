import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.bst_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_insert_rec_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open SimpleC.EE.QCP_demos_LLM.Bst
open scoped SimpleC.SL.SAC

local instance bst_insert_rec_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** (store_tree b_pre tr_low_level_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_2 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |->_)
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |->_)
  ** ((( &( "b" ) )) # Ptr |-> (retval))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** (store_tree b_pre tr_low_level_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_3 : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |->_)
  ** ((( &( "b" ) )) # Ptr |-> (retval))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** (store_tree b_pre tr_low_level_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (PreH1 : (b_pre ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (store_tree b_pre tr_low_level_spec)
|--
  EX b_right : Int, EX b_left : Int, EX l0 : tree, EX b_value : Int, EX r0 : tree, EX b_key : Int, EX tr0 : tree,
  “ (b_pre ≠ (0 : Int)) ” &&
  “ (tr_low_level_spec = tr0) ” &&
  “ (INT_MIN <= b_key) ” &&
  “ (b_key <= INT_MAX) ” &&
  “ (tr0 = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  ((&((b_pre # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b_pre # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b_pre # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b_pre # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
) \/
(
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (PreH1 : (b_pre ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (store_tree b_pre tr_low_level_spec)
|--
  EX b_right : Int, EX b_left : Int, EX l0 : tree, EX b_value : Int, EX r0 : tree, EX b_key : Int,
  “ (b_pre ≠ (0 : Int)) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (b_key) (b_value) (r0))) ” &&
  “ (INT_MIN <= b_key) ” &&
  “ (b_key <= INT_MAX) ”
  &&  ((&((b_pre # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b_pre # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b_pre # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b_pre # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
)

noncomputable def insert_return_wit_1 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (b_key >= x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (b ≠ (0 : Int))) (PreH4 : (tr_low_level_spec = tr0)) (PreH5 : (INT_MIN <= b_key)) (PreH6 : (b_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key >= x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (b ≠ (0 : Int))) (PreH7 : (tr_low_level_spec = tr0)) (PreH8 : (INT_MIN <= b_key)) (PreH9 : (b_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_return_wit_1_split_goal_spatial : Prop :=
  forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key >= x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (b ≠ (0 : Int))) (PreH7 : (tr_low_level_spec = tr0)) (PreH8 : (INT_MIN <= b_key)) (PreH9 : (b_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))

noncomputable def insert_return_wit_2 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (retval : Int) (PreH1 : (b_key < x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (b ≠ (0 : Int))) (PreH4 : (tr_low_level_spec = tr0)) (PreH5 : (INT_MIN <= b_key)) (PreH6 : (b_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (retval))
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (retval : Int) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key < x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (b ≠ (0 : Int))) (PreH7 : (tr_low_level_spec = tr0)) (PreH8 : (INT_MIN <= b_key)) (PreH9 : (b_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (retval))
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_return_wit_2_split_goal_spatial : Prop :=
  forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (retval : Int) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (b_key < x_pre)) (PreH5 : (x_pre >= b_key)) (PreH6 : (b ≠ (0 : Int))) (PreH7 : (tr_low_level_spec = tr0)) (PreH8 : (INT_MIN <= b_key)) (PreH9 : (b_key <= INT_MAX)) (PreH10 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  (store_tree retval (tree_insert (x_pre) (value_pre) (r0)))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (retval))
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))

noncomputable def insert_return_wit_3 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_right : Int) (retval : Int) (PreH1 : (x_pre < b_key)) (PreH2 : (b ≠ (0 : Int))) (PreH3 : (tr_low_level_spec = tr0)) (PreH4 : (INT_MIN <= b_key)) (PreH5 : (b_key <= INT_MAX)) (PreH6 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (retval))
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_right : Int) (retval : Int) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (x_pre < b_key)) (PreH5 : (b ≠ (0 : Int))) (PreH6 : (tr_low_level_spec = tr0)) (PreH7 : (INT_MIN <= b_key)) (PreH8 : (b_key <= INT_MAX)) (PreH9 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (retval))
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_return_wit_3_split_goal_spatial : Prop :=
  forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_right : Int) (retval : Int) (PreH1 : (b_value <= INT_MAX)) (PreH2 : (b_value >= INT_MIN)) (PreH3 : (b_key >= INT_MIN)) (PreH4 : (x_pre < b_key)) (PreH5 : (b ≠ (0 : Int))) (PreH6 : (tr_low_level_spec = tr0)) (PreH7 : (INT_MIN <= b_key)) (PreH8 : (b_key <= INT_MAX)) (PreH9 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  (store_tree retval (tree_insert (x_pre) (value_pre) (l0)))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (retval))
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  (store_tree b (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))

noncomputable def insert_return_wit_4 : Prop :=
  (
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (b_pre = (0 : Int))) (PreH3 : (INT_MIN <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** (store_tree b_pre tr_low_level_spec)
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
) \/
(
forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (retval : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : (b_pre = (0 : Int))) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** (store_tree b_pre tr_low_level_spec)
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))
)

noncomputable def insert_return_wit_4_split_goal_spatial : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (retval : Int) (PreH1 : (value_pre <= INT_MAX)) (PreH2 : (value_pre >= INT_MIN)) (PreH3 : (x_pre >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : (b_pre = (0 : Int))) (PreH6 : (INT_MIN <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (x_pre))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** (store_tree b_pre tr_low_level_spec)
|--
  (store_tree retval (tree_insert (x_pre) (value_pre) (tr_low_level_spec)))

noncomputable def insert_partial_solve_wit_1 : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (PreH1 : (b_pre = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (store_tree b_pre tr_low_level_spec)
|--
  “ (b_pre = (0 : Int)) ” &&
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_pre tr_low_level_spec)

noncomputable def insert_partial_solve_wit_2_pure : Prop :=
  forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (x_pre < b_key)) (PreH2 : (b ≠ (0 : Int))) (PreH3 : (tr_low_level_spec = tr0)) (PreH4 : (INT_MIN <= b_key)) (PreH5 : (b_key <= INT_MAX)) (PreH6 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  “ (x_pre <= INT_MAX) ” &&
  “ (INT_MIN <= x_pre) ”

noncomputable def insert_partial_solve_wit_2_aux : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (x_pre < b_key)) (PreH2 : (b ≠ (0 : Int))) (PreH3 : (tr_low_level_spec = tr0)) (PreH4 : (INT_MIN <= b_key)) (PreH5 : (b_key <= INT_MAX)) (PreH6 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  “ (x_pre <= INT_MAX) ” &&
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre < b_key) ” &&
  “ (b ≠ (0 : Int)) ” &&
  “ (tr_low_level_spec = tr0) ” &&
  “ (INT_MIN <= b_key) ” &&
  “ (b_key <= INT_MAX) ” &&
  “ (tr0 = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)

noncomputable def insert_partial_solve_wit_2 : Prop := insert_partial_solve_wit_2_pure -> insert_partial_solve_wit_2_aux

noncomputable def insert_partial_solve_wit_3_pure : Prop :=
  forall (value_pre : Int) (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (b_key < x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (b ≠ (0 : Int))) (PreH4 : (tr_low_level_spec = tr0)) (PreH5 : (INT_MIN <= b_key)) (PreH6 : (b_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b))
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”

noncomputable def insert_partial_solve_wit_3_aux : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (tr0 : tree) (l0 : tree) (r0 : tree) (b : Int) (b_key : Int) (b_value : Int) (b_left : Int) (b_right : Int) (PreH1 : (b_key < x_pre)) (PreH2 : (x_pre >= b_key)) (PreH3 : (b ≠ (0 : Int))) (PreH4 : (tr_low_level_spec = tr0)) (PreH5 : (INT_MIN <= b_key)) (PreH6 : (b_key <= INT_MAX)) (PreH7 : (tr0 = (make_tree (l0) (b_key) (b_value) (r0)))) ,
  ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))
  ** (store_tree b_right r0)
|--
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (b_key < x_pre) ” &&
  “ (x_pre >= b_key) ” &&
  “ (b ≠ (0 : Int)) ” &&
  “ (tr_low_level_spec = tr0) ” &&
  “ (INT_MIN <= b_key) ” &&
  “ (b_key <= INT_MAX) ” &&
  “ (tr0 = (make_tree (l0) (b_key) (b_value) (r0))) ”
  &&  (store_tree b_right r0)
  ** ((&((b # "tree")  ->ₛ "key")) # Int |-> (b_key))
  ** ((&((b # "tree")  ->ₛ "value")) # Int |-> (b_value))
  ** ((&((b # "tree")  ->ₛ "left")) # Ptr |-> (b_left))
  ** (store_tree b_left l0)
  ** ((&((b # "tree")  ->ₛ "right")) # Ptr |-> (b_right))

noncomputable def insert_partial_solve_wit_3 : Prop := insert_partial_solve_wit_3_pure -> insert_partial_solve_wit_3_aux

noncomputable def insert_derive_high_level_spec_by_low_level_spec : Prop :=
  forall (value_pre : Int) (x_pre : Int) (b_pre : Int) (m_high_level_spec : mapping) ,
  (“ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  (Bst.store_map b_pre m_high_level_spec))
|--
  EX tr_low_level_spec : tree,
  (“ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  (store_tree b_pre tr_low_level_spec))
  **
  ((EX retval_2 : Int,
  (store_tree retval_2 (tree_insert (x_pre) (value_pre) (tr_low_level_spec))))
  -*
  (EX retval : Int,
  (Bst.store_map retval (map_insert (x_pre) (value_pre) (m_high_level_spec)))))


structure VC_Correct : Type where
  proof_of_insert_safety_wit_1 : insert_safety_wit_1
  proof_of_insert_safety_wit_2 : insert_safety_wit_2
  proof_of_insert_safety_wit_3 : insert_safety_wit_3
  proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1
  proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure
  proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2
  proof_of_insert_partial_solve_wit_3_pure : insert_partial_solve_wit_3_pure
  proof_of_insert_partial_solve_wit_3 : insert_partial_solve_wit_3
  proof_of_insert_entail_wit_1 : insert_entail_wit_1
  proof_of_insert_return_wit_1 : insert_return_wit_1
  proof_of_insert_return_wit_2 : insert_return_wit_2
  proof_of_insert_return_wit_3 : insert_return_wit_3
  proof_of_insert_return_wit_4 : insert_return_wit_4
  proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec

end SimpleC.EE.QCP_demos_LLM.generated.bst_insert_rec_goal
