import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.bst_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_delete_rec2_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open SimpleC.EE.QCP_demos_LLM.Bst
open scoped SimpleC.SL.SAC

local instance bst_delete_rec2_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def get_pre_safety_wit_1 : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_left : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= t_key)) (PreH3 : (t_key <= INT_MAX)) ,
  ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((t_pre) # Ptr |-> (t_pre_v))
  ** ((&((t_pre_v # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre_v # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre_v # "tree")  ->ₛ "left")) # Ptr |-> (t_pre_v_left))
  ** (store_tree t_pre_v_left t_left)
  ** ((&((t_pre_v # "tree")  ->ₛ "right")) # Ptr |-> (t_pre_v_right))
  ** (store_tree t_pre_v_right t_right)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_pre_entail_wit_1 : Prop :=
  (
forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_left : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right ≠ (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  ((t_pre) # Ptr |-> (t_pre_v))
  ** ((&((t_pre_v # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre_v # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre_v # "tree")  ->ₛ "left")) # Ptr |-> (t_pre_v_left))
  ** (store_tree t_pre_v_left t_left)
  ** ((&((t_pre_v # "tree")  ->ₛ "right")) # Ptr |-> (t_pre_v_right))
  ** (store_tree t_pre_v_right t_right)
|--
  EX t_v_right_right : Int, EX t_v_right_left : Int, EX t_v_left : Int, EX l0 : tree, EX r0 : tree, EX t_v : Int, EX t_k : Int, EX t_v_right : Int, EX t_v_2 : Int,
  “ (t_v_2 ≠ (0 : Int)) ” &&
  “ (t_v_right ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ” &&
  “ (INT_MIN <= t_k) ” &&
  “ (t_k <= INT_MAX) ” &&
  “ (t_right = (make_tree (l0) (t_k) (t_v) (r0))) ”
  &&  ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_right # "tree")  ->ₛ "key")) # Int |-> (t_k))
  ** ((&((t_v_right # "tree")  ->ₛ "value")) # Int |-> (t_v))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
  ** ((&((t_v_right # "tree")  ->ₛ "left")) # Ptr |-> (t_v_right_left))
  ** (store_tree t_v_right_left l0)
  ** ((&((t_v_right # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right_right))
  ** (store_tree t_v_right_right r0)
) \/
(
forall (t_right : tree) (t_key : Int) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right ≠ (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  EX t_v_right_right : Int, EX t_v_right_left : Int, EX l0 : tree, EX r0 : tree, EX t_v : Int, EX t_k : Int,
  “ (t_pre_v ≠ (0 : Int)) ” &&
  “ (t_pre_v_right ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ” &&
  “ (INT_MIN <= t_k) ” &&
  “ (t_k <= INT_MAX) ” &&
  “ (t_right = (make_tree (l0) (t_k) (t_v) (r0))) ”
  &&  ((&((t_pre_v_right # "tree")  ->ₛ "key")) # Int |-> (t_k))
  ** ((&((t_pre_v_right # "tree")  ->ₛ "value")) # Int |-> (t_v))
  ** ((&((t_pre_v_right # "tree")  ->ₛ "left")) # Ptr |-> (t_v_right_left))
  ** (store_tree t_v_right_left l0)
  ** ((&((t_pre_v_right # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right_right))
  ** (store_tree t_v_right_right r0)
)

noncomputable def get_pre_return_wit_1 : Prop :=
  (
forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (retval_v_left_2 : Int) (retval_v_right_2 : Int) (ret_left_2 : tree) (t_pt_2 : partial_tree) (retval_v_value_2 : Int) (retval_v_key_2 : Int) (retval_v_2 : Int) (retval : Int) (PreH1 : (retval_v_2 ≠ (0 : Int))) (PreH2 : (INT_MIN <= retval_v_key_2)) (PreH3 : (retval_v_key_2 <= INT_MAX)) (PreH4 : (((find_pre (l0) (t_k) (t_v) (r0)).k) = retval_v_key_2)) (PreH5 : (((find_pre (l0) (t_k) (t_v) (r0)).v) = retval_v_value_2)) (PreH6 : (((find_pre (l0) (t_k) (t_v) (r0)).pt) = t_pt_2)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).l_tree) = ret_left_2)) (PreH8 : (retval_v_right_2 = (0 : Int))) (PreH9 : (t_v_2 ≠ (0 : Int))) (PreH10 : (t_v_right ≠ (0 : Int))) (PreH11 : (INT_MIN <= t_key)) (PreH12 : (t_key <= INT_MAX)) (PreH13 : (INT_MIN <= t_k)) (PreH14 : (t_k <= INT_MAX)) (PreH15 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  ((retval) # Ptr |-> (retval_v_2))
  ** ((&((retval_v_2 # "tree")  ->ₛ "key")) # Int |-> (retval_v_key_2))
  ** ((&((retval_v_2 # "tree")  ->ₛ "value")) # Int |-> (retval_v_value_2))
  ** ((&((retval_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (retval_v_right_2))
  ** (store_ptb retval &((t_v_2 # "tree")  ->ₛ "right") t_pt_2)
  ** ((&((retval_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (retval_v_left_2))
  ** (store_tree retval_v_left_2 ret_left_2)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
|--
  EX retval_v_left : Int, EX retval_v_right : Int, EX ret_left : tree, EX t_pt : partial_tree, EX retval_v_value : Int, EX retval_v_key : Int, EX retval_v : Int,
  “ (retval_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= retval_v_key) ” &&
  “ (retval_v_key <= INT_MAX) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).k) = retval_v_key) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).v) = retval_v_value) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).pt) = t_pt) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).l_tree) = ret_left) ” &&
  “ (retval_v_right = (0 : Int)) ”
  &&  ((retval) # Ptr |-> (retval_v))
  ** ((&((retval_v # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((retval_v # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((retval_v # "tree")  ->ₛ "right")) # Ptr |-> (retval_v_right))
  ** (store_ptb retval t_pre t_pt)
  ** ((&((retval_v # "tree")  ->ₛ "left")) # Ptr |-> (retval_v_left))
  ** (store_tree retval_v_left ret_left)
) \/
(
forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (retval_v_right_2 : Int) (ret_left_2 : tree) (t_pt_2 : partial_tree) (retval_v_value_2 : Int) (retval_v_key_2 : Int) (retval_v_2 : Int) (retval : Int) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).k) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).v) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).pt) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).l_tree) = ret_left_2)) (PreH11 : (retval_v_right_2 = (0 : Int))) (PreH12 : (t_v_2 ≠ (0 : Int))) (PreH13 : (t_v_right ≠ (0 : Int))) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2 # "tree")  ->ₛ "right") t_pt_2)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).l_tree) = ret_left_2) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).v) = retval_v_value_2) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).k) = retval_v_key_2) ”
  &&  (store_ptb retval t_pre ((find_pre (t_left) (t_key) (t_value) (t_right)).pt))
)

noncomputable def get_pre_return_wit_1_split_goal_1 : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (retval_v_right_2 : Int) (ret_left_2 : tree) (t_pt_2 : partial_tree) (retval_v_value_2 : Int) (retval_v_key_2 : Int) (retval_v_2 : Int) (retval : Int) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).k) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).v) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).pt) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).l_tree) = ret_left_2)) (PreH11 : (retval_v_right_2 = (0 : Int))) (PreH12 : (t_v_2 ≠ (0 : Int))) (PreH13 : (t_v_right ≠ (0 : Int))) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2 # "tree")  ->ₛ "right") t_pt_2)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).l_tree) = ret_left_2) ”

noncomputable def get_pre_return_wit_1_split_goal_2 : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (retval_v_right_2 : Int) (ret_left_2 : tree) (t_pt_2 : partial_tree) (retval_v_value_2 : Int) (retval_v_key_2 : Int) (retval_v_2 : Int) (retval : Int) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).k) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).v) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).pt) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).l_tree) = ret_left_2)) (PreH11 : (retval_v_right_2 = (0 : Int))) (PreH12 : (t_v_2 ≠ (0 : Int))) (PreH13 : (t_v_right ≠ (0 : Int))) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2 # "tree")  ->ₛ "right") t_pt_2)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).v) = retval_v_value_2) ”

noncomputable def get_pre_return_wit_1_split_goal_3 : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (retval_v_right_2 : Int) (ret_left_2 : tree) (t_pt_2 : partial_tree) (retval_v_value_2 : Int) (retval_v_key_2 : Int) (retval_v_2 : Int) (retval : Int) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).k) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).v) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).pt) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).l_tree) = ret_left_2)) (PreH11 : (retval_v_right_2 = (0 : Int))) (PreH12 : (t_v_2 ≠ (0 : Int))) (PreH13 : (t_v_right ≠ (0 : Int))) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2 # "tree")  ->ₛ "right") t_pt_2)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).k) = retval_v_key_2) ”

noncomputable def get_pre_return_wit_1_split_goal_spatial : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (retval_v_right_2 : Int) (ret_left_2 : tree) (t_pt_2 : partial_tree) (retval_v_value_2 : Int) (retval_v_key_2 : Int) (retval_v_2 : Int) (retval : Int) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval_v_2 ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key_2)) (PreH6 : (retval_v_key_2 <= INT_MAX)) (PreH7 : (((find_pre (l0) (t_k) (t_v) (r0)).k) = retval_v_key_2)) (PreH8 : (((find_pre (l0) (t_k) (t_v) (r0)).v) = retval_v_value_2)) (PreH9 : (((find_pre (l0) (t_k) (t_v) (r0)).pt) = t_pt_2)) (PreH10 : (((find_pre (l0) (t_k) (t_v) (r0)).l_tree) = ret_left_2)) (PreH11 : (retval_v_right_2 = (0 : Int))) (PreH12 : (t_v_2 ≠ (0 : Int))) (PreH13 : (t_v_right ≠ (0 : Int))) (PreH14 : (INT_MIN <= t_key)) (PreH15 : (t_key <= INT_MAX)) (PreH16 : (INT_MIN <= t_k)) (PreH17 : (t_k <= INT_MAX)) (PreH18 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  (store_ptb retval &((t_v_2 # "tree")  ->ₛ "right") t_pt_2)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
|--
  (store_ptb retval t_pre ((find_pre (t_left) (t_key) (t_value) (t_right)).pt))

noncomputable def get_pre_return_wit_2 : Prop :=
  (
forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_left : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  ((t_pre) # Ptr |-> (t_pre_v))
  ** ((&((t_pre_v # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre_v # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre_v # "tree")  ->ₛ "left")) # Ptr |-> (t_pre_v_left))
  ** (store_tree t_pre_v_left t_left)
  ** ((&((t_pre_v # "tree")  ->ₛ "right")) # Ptr |-> (t_pre_v_right))
  ** (store_tree t_pre_v_right t_right)
|--
  EX retval_v_left : Int, EX retval_v_right : Int, EX ret_left : tree, EX t_pt : partial_tree, EX retval_v_value : Int, EX retval_v_key : Int, EX retval_v : Int,
  “ (retval_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= retval_v_key) ” &&
  “ (retval_v_key <= INT_MAX) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).k) = retval_v_key) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).v) = retval_v_value) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).pt) = t_pt) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).l_tree) = ret_left) ” &&
  “ (retval_v_right = (0 : Int)) ”
  &&  ((t_pre) # Ptr |-> (retval_v))
  ** ((&((retval_v # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((retval_v # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((retval_v # "tree")  ->ₛ "right")) # Ptr |-> (retval_v_right))
  ** (store_ptb t_pre t_pre t_pt)
  ** ((&((retval_v # "tree")  ->ₛ "left")) # Ptr |-> (retval_v_left))
  ** (store_tree retval_v_left ret_left)
) \/
(
forall (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).l_tree) = t_left) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).pt) = empty_partial_tree) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).v) = t_value) ” &&
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).k) = t_key) ”
  &&  emp
)

noncomputable def get_pre_return_wit_2_split_goal_1 : Prop :=
  forall (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).l_tree) = t_left) ”

noncomputable def get_pre_return_wit_2_split_goal_2 : Prop :=
  forall (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).pt) = empty_partial_tree) ”

noncomputable def get_pre_return_wit_2_split_goal_3 : Prop :=
  forall (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).v) = t_value) ”

noncomputable def get_pre_return_wit_2_split_goal_4 : Prop :=
  forall (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  “ (((find_pre (t_left) (t_key) (t_value) (t_right)).k) = t_key) ”

noncomputable def get_pre_return_wit_2_split_goal_spatial : Prop :=
  forall (t_right : tree) (t_key : Int) (t_pre_v : Int) (t_pre_v_right : Int) (PreH1 : (t_pre_v_right = (0 : Int))) (PreH2 : (t_pre_v ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) ,
  (store_tree t_pre_v_right t_right)
|--
  TT && emp 

noncomputable def get_pre_partial_solve_wit_1_pure : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (t_v_right_left : Int) (t_v_right_right : Int) (PreH1 : (t_v_2 ≠ (0 : Int))) (PreH2 : (t_v_right ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (INT_MIN <= t_k)) (PreH6 : (t_k <= INT_MAX)) (PreH7 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_right # "tree")  ->ₛ "key")) # Int |-> (t_k))
  ** ((&((t_v_right # "tree")  ->ₛ "value")) # Int |-> (t_v))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
  ** ((&((t_v_right # "tree")  ->ₛ "left")) # Ptr |-> (t_v_right_left))
  ** (store_tree t_v_right_left l0)
  ** ((&((t_v_right # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right_right))
  ** (store_tree t_v_right_right r0)
|--
  “ (t_v_right ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_k) ” &&
  “ (t_k <= INT_MAX) ”

noncomputable def get_pre_partial_solve_wit_1_aux : Prop :=
  forall (t_pre : Int) (t_right : tree) (t_value : Int) (t_key : Int) (t_left : tree) (l0 : tree) (r0 : tree) (t_k : Int) (t_v : Int) (t_v_2 : Int) (t_v_right : Int) (t_v_left : Int) (t_v_right_left : Int) (t_v_right_right : Int) (PreH1 : (t_v_2 ≠ (0 : Int))) (PreH2 : (t_v_right ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (INT_MIN <= t_k)) (PreH6 : (t_k <= INT_MAX)) (PreH7 : (t_right = (make_tree (l0) (t_k) (t_v) (r0)))) ,
  ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_right # "tree")  ->ₛ "key")) # Int |-> (t_k))
  ** ((&((t_v_right # "tree")  ->ₛ "value")) # Int |-> (t_v))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)
  ** ((&((t_v_right # "tree")  ->ₛ "left")) # Ptr |-> (t_v_right_left))
  ** (store_tree t_v_right_left l0)
  ** ((&((t_v_right # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right_right))
  ** (store_tree t_v_right_right r0)
|--
  “ (t_v_right ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_k) ” &&
  “ (t_k <= INT_MAX) ” &&
  “ (t_v_2 ≠ (0 : Int)) ” &&
  “ (t_v_right ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ” &&
  “ (INT_MIN <= t_k) ” &&
  “ (t_k <= INT_MAX) ” &&
  “ (t_right = (make_tree (l0) (t_k) (t_v) (r0))) ”
  &&  ((&((t_v_2 # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right))
  ** ((&((t_v_right # "tree")  ->ₛ "key")) # Int |-> (t_k))
  ** ((&((t_v_right # "tree")  ->ₛ "value")) # Int |-> (t_v))
  ** ((&((t_v_right # "tree")  ->ₛ "left")) # Ptr |-> (t_v_right_left))
  ** (store_tree t_v_right_left l0)
  ** ((&((t_v_right # "tree")  ->ₛ "right")) # Ptr |-> (t_v_right_right))
  ** (store_tree t_v_right_right r0)
  ** ((t_pre) # Ptr |-> (t_v_2))
  ** ((&((t_v_2 # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_v_2 # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_v_2 # "tree")  ->ₛ "left")) # Ptr |-> (t_v_left))
  ** (store_tree t_v_left t_left)

noncomputable def get_pre_partial_solve_wit_1 : Prop := get_pre_partial_solve_wit_1_pure -> get_pre_partial_solve_wit_1_aux

noncomputable def delete_safety_wit_1 : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_pre_v : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "p" ) )) # Ptr |-> (b_pre_v))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v tr_low_level_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def delete_safety_wit_2 : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre <= p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "y" ) )) # Int |-> (p_key))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def delete_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_pre_v : Int) (PreH1 : (b_pre_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v tr_low_level_spec)
|--
  EX p_right : Int, EX p_left : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key : Int, EX b_v : Int,
  “ (b_pre_v = b_v) ” &&
  “ (b_pre_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((b_pre) # Ptr |-> (b_v))
  ** ((&((b_pre_v # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((b_pre_v # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((b_pre_v # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((b_pre_v # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (b_pre_v : Int) (PreH1 : (b_pre_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (store_tree b_pre_v tr_low_level_spec)
|--
  EX p_right : Int, EX p_left : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key : Int,
  “ (b_pre_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((b_pre_v # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((b_pre_v # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((b_pre_v # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((b_pre_v # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
)

noncomputable def delete_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0_2 : tree) (r0_2 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value_2 : Int) (p_left_2 : Int) (p_right_2 : Int) (PreH1 : (p_left_2 ≠ (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0_2) (p_key) (p_value_2) (r0_2)))) ,
  ((b_pre) # Ptr |-> (b_v_2))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value_2))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left_2))
  ** (store_tree p_left_2 l0_2)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right_2))
  ** (store_tree p_right_2 r0_2)
|--
  EX p_left_right : Int, EX p_left_left : Int, EX l0_left : tree, EX r0_left : tree, EX p_l_v : Int, EX p_l_k : Int, EX p_left : Int, EX p_right : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key_2 : Int, EX b_v : Int,
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (x_pre = p_key) ” &&
  “ (p_key = p_key_2) ” &&
  “ (INT_MIN <= p_key_2) ” &&
  “ (p_key_2 <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key_2) (p_value) (r0))) ” &&
  “ (p_left ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_l_k) ” &&
  “ (p_l_k <= INT_MAX) ” &&
  “ (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) ”
  &&  ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key_2))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p_left # "tree")  ->ₛ "key")) # Int |-> (p_l_k))
  ** ((&((p_left # "tree")  ->ₛ "value")) # Int |-> (p_l_v))
  ** ((&((p_left # "tree")  ->ₛ "left")) # Ptr |-> (p_left_left))
  ** (store_tree p_left_left l0_left)
  ** ((&((p_left # "tree")  ->ₛ "right")) # Ptr |-> (p_left_right))
  ** (store_tree p_left_right r0_left)
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (l0_2 : tree) (r0_2 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value_2 : Int) (p_left_2 : Int) (PreH1 : (p_left_2 ≠ (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0_2) (p_key) (p_value_2) (r0_2)))) ,
  (store_tree p_left_2 l0_2)
|--
  EX p_left_right : Int, EX p_left_left : Int, EX l0_left : tree, EX r0_left : tree, EX p_l_v : Int, EX p_l_k : Int,
  “ (p = b_v_2) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (x_pre = p_key) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree ((make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) (p_key) (p_value_2) (r0_2))) ” &&
  “ (p_left_2 ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_l_k) ” &&
  “ (p_l_k <= INT_MAX) ”
  &&  ((&((p_left_2 # "tree")  ->ₛ "key")) # Int |-> (p_l_k))
  ** ((&((p_left_2 # "tree")  ->ₛ "value")) # Int |-> (p_l_v))
  ** ((&((p_left_2 # "tree")  ->ₛ "left")) # Ptr |-> (p_left_left))
  ** (store_tree p_left_left l0_left)
  ** ((&((p_left_2 # "tree")  ->ₛ "right")) # Ptr |-> (p_left_right))
  ** (store_tree p_left_right r0_left)
)

noncomputable def delete_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (b_pre_v_2 : Int) (PreH1 : (b_pre_v_2 = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr |-> (b_pre_v_2))
  ** (store_tree b_pre_v_2 tr_low_level_spec)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)))
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (b_pre_v_2 : Int) (PreH1 : (b_pre_v_2 = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (tr_low_level_spec = (tree_delete' (x_pre) (tr_low_level_spec))) ”
  &&  emp
)

noncomputable def delete_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (b_pre_v_2 : Int) (PreH1 : (b_pre_v_2 = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (tr_low_level_spec = (tree_delete' (x_pre) (tr_low_level_spec)))

noncomputable def delete_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_right : Int) (b_callee_v : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v (tree_delete' (x_pre) (l0)))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)))
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_right : Int) (b_callee_v : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v)) (PreH6 : (p ≠ (0 : Int))) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v (tree_delete' (x_pre) (l0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)))
)

noncomputable def delete_return_wit_2_split_goal_spatial : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_right : Int) (b_callee_v : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v)) (PreH6 : (p ≠ (0 : Int))) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v (tree_delete' (x_pre) (l0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)))

noncomputable def delete_return_wit_3 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (b_callee_v : Int) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v (tree_delete' (x_pre) (r0)))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)))
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (b_callee_v : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v)) (PreH7 : (p ≠ (0 : Int))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v (tree_delete' (x_pre) (r0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)))
)

noncomputable def delete_return_wit_3_split_goal_spatial : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (b_callee_v : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v)) (PreH7 : (p ≠ (0 : Int))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_callee_v))
  ** (store_tree b_callee_v (tree_delete' (x_pre) (r0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)))

noncomputable def delete_return_wit_4 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr |-> (p_right))
  ** (store_tree p_left l0)
  ** (store_tree p_right r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)))
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0)
|--
  “ (r0 = (tree_delete' (x_pre) (tr_low_level_spec))) ”
  &&  emp
)

noncomputable def delete_return_wit_4_split_goal_1 : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0)
|--
  “ (r0 = (tree_delete' (x_pre) (tr_low_level_spec))) ”

noncomputable def delete_return_wit_4_split_goal_spatial : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0)
|--
  TT && emp 

noncomputable def delete_return_wit_5 : Prop :=
  (
forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (l0_left : tree) (r0_left : tree) (p_l_k : Int) (p_l_v : Int) (p : Int) (b_v : Int) (y : Int) (p_key : Int) (p_value : Int) (p_right : Int) (p_left : Int) (retval_v_left : Int) (retval_v_right : Int) (ret_left : tree) (t_pt : partial_tree) (retval_v_value : Int) (retval_v_key : Int) (retval_v : Int) (retval : Int) (PreH1 : (retval_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= retval_v_key)) (PreH3 : (retval_v_key <= INT_MAX)) (PreH4 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).k) = retval_v_key)) (PreH5 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).v) = retval_v_value)) (PreH6 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).pt) = t_pt)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).l_tree) = ret_left)) (PreH8 : (retval_v_right = (0 : Int))) (PreH9 : (p = b_v)) (PreH10 : (p ≠ (0 : Int))) (PreH11 : (x_pre = y)) (PreH12 : (y = p_key)) (PreH13 : (INT_MIN <= p_key)) (PreH14 : (p_key <= INT_MAX)) (PreH15 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH16 : (p_left ≠ (0 : Int))) (PreH17 : (INT_MIN <= p_l_k)) (PreH18 : (p_l_k <= INT_MAX)) (PreH19 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr |-> (retval_v_left))
  ** (store_ptb retval &((p # "tree")  ->ₛ "left") t_pt)
  ** (store_tree retval_v_left ret_left)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_pre_v : Int,
  ((b_pre) # Ptr |-> (b_pre_v))
  ** (store_tree b_pre_v (tree_delete' (x_pre) (tr_low_level_spec)))
) \/
(
forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (l0_left : tree) (r0_left : tree) (p_l_k : Int) (p_l_v : Int) (p : Int) (b_v : Int) (y : Int) (p_key : Int) (p_value : Int) (p_right : Int) (p_left : Int) (retval_v_left : Int) (retval_v_right : Int) (ret_left : tree) (t_pt : partial_tree) (retval_v_value : Int) (retval_v_key : Int) (retval_v : Int) (retval : Int) (PreH1 : (retval_v_value <= INT_MAX)) (PreH2 : (retval_v_value >= INT_MIN)) (PreH3 : (retval_v_key >= INT_MIN)) (PreH4 : (retval_v ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key)) (PreH6 : (retval_v_key <= INT_MAX)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).k) = retval_v_key)) (PreH8 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).v) = retval_v_value)) (PreH9 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).pt) = t_pt)) (PreH10 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).l_tree) = ret_left)) (PreH11 : (retval_v_right = (0 : Int))) (PreH12 : (p = b_v)) (PreH13 : (p ≠ (0 : Int))) (PreH14 : (x_pre = y)) (PreH15 : (y = p_key)) (PreH16 : (INT_MIN <= p_key)) (PreH17 : (p_key <= INT_MAX)) (PreH18 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH19 : (p_left ≠ (0 : Int))) (PreH20 : (INT_MIN <= p_l_k)) (PreH21 : (p_l_k <= INT_MAX)) (PreH22 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr |-> (retval_v_left))
  ** (store_ptb retval &((p # "tree")  ->ₛ "left") t_pt)
  ** (store_tree retval_v_left ret_left)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)))
)

noncomputable def delete_return_wit_5_split_goal_spatial : Prop :=
  forall (x_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (l0_left : tree) (r0_left : tree) (p_l_k : Int) (p_l_v : Int) (p : Int) (b_v : Int) (y : Int) (p_key : Int) (p_value : Int) (p_right : Int) (p_left : Int) (retval_v_left : Int) (retval_v_right : Int) (ret_left : tree) (t_pt : partial_tree) (retval_v_value : Int) (retval_v_key : Int) (retval_v : Int) (retval : Int) (PreH1 : (retval_v_value <= INT_MAX)) (PreH2 : (retval_v_value >= INT_MIN)) (PreH3 : (retval_v_key >= INT_MIN)) (PreH4 : (retval_v ≠ (0 : Int))) (PreH5 : (INT_MIN <= retval_v_key)) (PreH6 : (retval_v_key <= INT_MAX)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).k) = retval_v_key)) (PreH8 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).v) = retval_v_value)) (PreH9 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).pt) = t_pt)) (PreH10 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).l_tree) = ret_left)) (PreH11 : (retval_v_right = (0 : Int))) (PreH12 : (p = b_v)) (PreH13 : (p ≠ (0 : Int))) (PreH14 : (x_pre = y)) (PreH15 : (y = p_key)) (PreH16 : (INT_MIN <= p_key)) (PreH17 : (p_key <= INT_MAX)) (PreH18 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH19 : (p_left ≠ (0 : Int))) (PreH20 : (INT_MIN <= p_l_k)) (PreH21 : (p_l_k <= INT_MAX)) (PreH22 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr |-> (retval_v_left))
  ** (store_ptb retval &((p # "tree")  ->ₛ "left") t_pt)
  ** (store_tree retval_v_left ret_left)
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  (store_tree b_v (tree_delete' (x_pre) (tr_low_level_spec)))

noncomputable def delete_partial_solve_wit_1_pure : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "y" ) )) # Int |-> (p_key))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (x_pre <= INT_MAX) ” &&
  “ (INT_MIN <= x_pre) ”

noncomputable def delete_partial_solve_wit_1_aux : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (x_pre <= INT_MAX) ” &&
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre < p_key) ” &&
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)

noncomputable def delete_partial_solve_wit_1 : Prop := delete_partial_solve_wit_1_pure -> delete_partial_solve_wit_1_aux

noncomputable def delete_partial_solve_wit_2_pure : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "y" ) )) # Int |-> (p_key))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”

noncomputable def delete_partial_solve_wit_2_aux : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ” &&
  “ (x_pre > p_key) ” &&
  “ (x_pre >= p_key) ” &&
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)

noncomputable def delete_partial_solve_wit_2 : Prop := delete_partial_solve_wit_2_pure -> delete_partial_solve_wit_2_aux

noncomputable def delete_partial_solve_wit_3 : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr |-> (p_right))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (p_left = (0 : Int)) ” &&
  “ (x_pre <= p_key) ” &&
  “ (x_pre >= p_key) ” &&
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((b_pre) # Ptr |-> (p_right))
  ** (store_tree p_left l0)
  ** (store_tree p_right r0)

noncomputable def delete_partial_solve_wit_4_pure : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (l0_left : tree) (r0_left : tree) (p_l_k : Int) (p_l_v : Int) (p : Int) (b_v : Int) (y : Int) (p_key : Int) (p_value : Int) (p_right : Int) (p_left : Int) (p_left_left : Int) (p_left_right : Int) (PreH1 : (p = b_v)) (PreH2 : (p ≠ (0 : Int))) (PreH3 : (x_pre = y)) (PreH4 : (y = p_key)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH8 : (p_left ≠ (0 : Int))) (PreH9 : (INT_MIN <= p_l_k)) (PreH10 : (p_l_k <= INT_MAX)) (PreH11 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((( &( "pre" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p_left # "tree")  ->ₛ "key")) # Int |-> (p_l_k))
  ** ((&((p_left # "tree")  ->ₛ "value")) # Int |-> (p_l_v))
  ** ((&((p_left # "tree")  ->ₛ "left")) # Ptr |-> (p_left_left))
  ** (store_tree p_left_left l0_left)
  ** ((&((p_left # "tree")  ->ₛ "right")) # Ptr |-> (p_left_right))
  ** (store_tree p_left_right r0_left)
|--
  “ (p_left ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_l_k) ” &&
  “ (p_l_k <= INT_MAX) ”

noncomputable def delete_partial_solve_wit_4_aux : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (l0_left : tree) (r0_left : tree) (p_l_k : Int) (p_l_v : Int) (p : Int) (b_v : Int) (y : Int) (p_key : Int) (p_value : Int) (p_right : Int) (p_left : Int) (p_left_left : Int) (p_left_right : Int) (PreH1 : (p = b_v)) (PreH2 : (p ≠ (0 : Int))) (PreH3 : (x_pre = y)) (PreH4 : (y = p_key)) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH8 : (p_left ≠ (0 : Int))) (PreH9 : (INT_MIN <= p_l_k)) (PreH10 : (p_l_k <= INT_MAX)) (PreH11 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p_left # "tree")  ->ₛ "key")) # Int |-> (p_l_k))
  ** ((&((p_left # "tree")  ->ₛ "value")) # Int |-> (p_l_v))
  ** ((&((p_left # "tree")  ->ₛ "left")) # Ptr |-> (p_left_left))
  ** (store_tree p_left_left l0_left)
  ** ((&((p_left # "tree")  ->ₛ "right")) # Ptr |-> (p_left_right))
  ** (store_tree p_left_right r0_left)
|--
  “ (p_left ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_l_k) ” &&
  “ (p_l_k <= INT_MAX) ” &&
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (x_pre = y) ” &&
  “ (y = p_key) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ” &&
  “ (p_left ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_l_k) ” &&
  “ (p_l_k <= INT_MAX) ” &&
  “ (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) ”
  &&  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p_left # "tree")  ->ₛ "key")) # Int |-> (p_l_k))
  ** ((&((p_left # "tree")  ->ₛ "value")) # Int |-> (p_l_v))
  ** ((&((p_left # "tree")  ->ₛ "left")) # Ptr |-> (p_left_left))
  ** (store_tree p_left_left l0_left)
  ** ((&((p_left # "tree")  ->ₛ "right")) # Ptr |-> (p_left_right))
  ** (store_tree p_left_right r0_left)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)

noncomputable def delete_partial_solve_wit_4 : Prop := delete_partial_solve_wit_4_pure -> delete_partial_solve_wit_4_aux

noncomputable def delete_partial_solve_wit_5 : Prop :=
  forall (x_pre : Int) (b_pre : Int) (tr_low_level_spec : tree) (l0 : tree) (r0 : tree) (l0_left : tree) (r0_left : tree) (p_l_k : Int) (p_l_v : Int) (p : Int) (b_v : Int) (y : Int) (p_key : Int) (p_value : Int) (p_right : Int) (p_left : Int) (retval_v_left : Int) (retval_v_right : Int) (ret_left : tree) (t_pt : partial_tree) (retval_v_value : Int) (retval_v_key : Int) (retval_v : Int) (retval : Int) (PreH1 : (retval_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= retval_v_key)) (PreH3 : (retval_v_key <= INT_MAX)) (PreH4 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).k) = retval_v_key)) (PreH5 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).v) = retval_v_value)) (PreH6 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).pt) = t_pt)) (PreH7 : (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).l_tree) = ret_left)) (PreH8 : (retval_v_right = (0 : Int))) (PreH9 : (p = b_v)) (PreH10 : (p ≠ (0 : Int))) (PreH11 : (x_pre = y)) (PreH12 : (y = p_key)) (PreH13 : (INT_MIN <= p_key)) (PreH14 : (p_key <= INT_MAX)) (PreH15 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) (PreH16 : (p_left ≠ (0 : Int))) (PreH17 : (INT_MIN <= p_l_k)) (PreH18 : (p_l_k <= INT_MAX)) (PreH19 : (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left)))) ,
  ((retval) # Ptr |-> (retval_v_left))
  ** ((&((retval_v # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((retval_v # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((retval_v # "tree")  ->ₛ "right")) # Ptr |-> (retval_v_right))
  ** (store_ptb retval &((p # "tree")  ->ₛ "left") t_pt)
  ** ((&((retval_v # "tree")  ->ₛ "left")) # Ptr |-> (retval_v_left))
  ** (store_tree retval_v_left ret_left)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (retval_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= retval_v_key) ” &&
  “ (retval_v_key <= INT_MAX) ” &&
  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).k) = retval_v_key) ” &&
  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).v) = retval_v_value) ” &&
  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).pt) = t_pt) ” &&
  “ (((find_pre (l0_left) (p_l_k) (p_l_v) (r0_left)).l_tree) = ret_left) ” &&
  “ (retval_v_right = (0 : Int)) ” &&
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (x_pre = y) ” &&
  “ (y = p_key) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ” &&
  “ (p_left ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_l_k) ” &&
  “ (p_l_k <= INT_MAX) ” &&
  “ (l0 = (make_tree (l0_left) (p_l_k) (p_l_v) (r0_left))) ”
  &&  ((&((retval_v # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((retval_v # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((retval_v # "tree")  ->ₛ "left")) # Ptr |-> (retval_v_left))
  ** ((&((retval_v # "tree")  ->ₛ "right")) # Ptr |-> (retval_v_right))
  ** ((retval) # Ptr |-> (retval_v_left))
  ** (store_ptb retval &((p # "tree")  ->ₛ "left") t_pt)
  ** (store_tree retval_v_left ret_left)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (retval_v_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (retval_v_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)

noncomputable def delete_derive_high_level_spec_by_low_level_spec : Prop :=
  forall (x_pre : Int) (b_pre : Int) (m_high_level_spec : mapping) ,
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
  ** (store_tree b_callee_v_2 (tree_delete' (x_pre) (tr_low_level_spec))))
  -*
  (EX b_pre_v_2 : Int,
  ((b_pre) # Ptr |-> (b_pre_v_2))
  ** (Bst.store_map b_pre_v_2 (map_delete (x_pre) (m_high_level_spec)))))


structure VC_Correct : Type where
  proof_of_get_pre_safety_wit_1 : get_pre_safety_wit_1
  proof_of_get_pre_partial_solve_wit_1_pure : get_pre_partial_solve_wit_1_pure
  proof_of_get_pre_partial_solve_wit_1 : get_pre_partial_solve_wit_1
  proof_of_delete_safety_wit_1 : delete_safety_wit_1
  proof_of_delete_safety_wit_2 : delete_safety_wit_2
  proof_of_delete_partial_solve_wit_1_pure : delete_partial_solve_wit_1_pure
  proof_of_delete_partial_solve_wit_1 : delete_partial_solve_wit_1
  proof_of_delete_partial_solve_wit_2_pure : delete_partial_solve_wit_2_pure
  proof_of_delete_partial_solve_wit_2 : delete_partial_solve_wit_2
  proof_of_delete_partial_solve_wit_3 : delete_partial_solve_wit_3
  proof_of_delete_partial_solve_wit_4_pure : delete_partial_solve_wit_4_pure
  proof_of_delete_partial_solve_wit_4 : delete_partial_solve_wit_4
  proof_of_delete_partial_solve_wit_5 : delete_partial_solve_wit_5
  proof_of_get_pre_entail_wit_1 : get_pre_entail_wit_1
  proof_of_get_pre_return_wit_1 : get_pre_return_wit_1
  proof_of_get_pre_return_wit_2 : get_pre_return_wit_2
  proof_of_delete_entail_wit_1 : delete_entail_wit_1
  proof_of_delete_entail_wit_2 : delete_entail_wit_2
  proof_of_delete_return_wit_1 : delete_return_wit_1
  proof_of_delete_return_wit_2 : delete_return_wit_2
  proof_of_delete_return_wit_3 : delete_return_wit_3
  proof_of_delete_return_wit_4 : delete_return_wit_4
  proof_of_delete_return_wit_5 : delete_return_wit_5
  proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec

end SimpleC.EE.QCP_demos_LLM.generated.bst_delete_rec2_goal
