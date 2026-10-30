import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.QCP_demos_LLM.bst_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.bst_delete_rec_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open SimpleC.EE.QCP_demos_LLM.Bst
open scoped SimpleC.SL.SAC CoqZ

local instance bst_delete_rec_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def get_pre_safety_wit_1 : Prop :=
  forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_left : Int) (t_right : Int) (PreH1 : (t_pre ≠ (0 : Int))) (PreH2 : (INT_MIN <= t_key)) (PreH3 : (t_key <= INT_MAX)) (PreH4 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
  ** (store_tree t_right r0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_pre_entail_wit_1 : Prop :=
  (
forall (tr : tree) (t_pre : Int) (PreH1 : (t_pre ≠ (0 : Int))) ,
  (store_tree t_pre tr)
|--
  EX t_right : Int, EX t_left : Int, EX l0 : tree, EX t_value : Int, EX r0 : tree, EX t_key : Int,
  “ (t_pre ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ” &&
  “ (tr = (make_tree (l0) (t_key) (t_value) (r0))) ”
  &&  ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
  ** (store_tree t_right r0)
) \/
(
forall (tr : tree) (t_pre : Int) (PreH1 : (t_pre ≠ (0 : Int))) ,
  (store_tree t_pre tr)
|--
  EX t_right : Int, EX t_left : Int, EX l0 : tree, EX t_value : Int, EX r0 : tree, EX t_key : Int,
  “ (t_pre ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ” &&
  “ (tr = (make_tree (l0) (t_key) (t_value) (r0))) ”
  &&  ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
  ** (store_tree t_right r0)
)

noncomputable def get_pre_return_wit_1 : Prop :=
  (
forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_left : Int) (t_right : Int) (retval_left_2 : Int) (retval_right_2 : Int) (pt_2 : partial_tree) (tr_ret_left_2 : tree) (retval_key_2 : Int) (retval_value_2 : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : forall (tr_ret_right_2 : tree) , ((tree_pre_merge (r0) (tr_ret_right_2)) = (combine_tree (pt_2) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right_2)))))) (PreH3 : (retval_right_2 = (0 : Int))) (PreH4 : (INT_MIN <= retval_key_2)) (PreH5 : (retval_key_2 <= INT_MAX)) (PreH6 : (t_right ≠ (0 : Int))) (PreH7 : (t_pre ≠ (0 : Int))) (PreH8 : (INT_MIN <= t_key)) (PreH9 : (t_key <= INT_MAX)) (PreH10 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value_2))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key_2))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (retval_right_2))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left_2))
  ** (store_tree retval_left_2 tr_ret_left_2)
  ** (store_pt retval t_right pt_2)
  ** ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
|--
  EX retval_left : Int, EX retval_right : Int, EX pt : partial_tree, EX tr_ret_left : tree, EX retval_key : Int, EX retval_value : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ forall (tr_ret_right : tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) ” &&
  “ (retval_right = (0 : Int)) ” &&
  “ (INT_MIN <= retval_key) ” &&
  “ (retval_key <= INT_MAX) ”
  &&  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (retval_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval t_pre pt)
) \/
(
forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_left : Int) (t_right : Int) (retval_right_2 : Int) (pt_2 : partial_tree) (tr_ret_left_2 : tree) (retval_key_2 : Int) (retval_value_2 : Int) (retval : Int) (PreH1 : (t_value <= INT_MAX)) (PreH2 : (t_value >= INT_MIN)) (PreH3 : (t_key >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : forall (tr_ret_right_2 : tree) , ((tree_pre_merge (r0) (tr_ret_right_2)) = (combine_tree (pt_2) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right_2)))))) (PreH6 : (retval_right_2 = (0 : Int))) (PreH7 : (INT_MIN <= retval_key_2)) (PreH8 : (retval_key_2 <= INT_MAX)) (PreH9 : (t_right ≠ (0 : Int))) (PreH10 : (t_pre ≠ (0 : Int))) (PreH11 : (INT_MIN <= t_key)) (PreH12 : (t_key <= INT_MAX)) (PreH13 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  (store_pt retval t_right pt_2)
  ** ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
|--
  EX pt : partial_tree,
  “ (retval_right_2 = (0 : Int)) ” &&
  “ (retval_right_2 = (0 : Int)) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ forall (tr_ret_right : tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right))))) ” &&
  “ (INT_MIN <= retval_key_2) ” &&
  “ (retval_key_2 <= INT_MAX) ”
  &&  (store_pt retval t_pre pt)
)

noncomputable def get_pre_return_wit_2 : Prop :=
  (
forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_left : Int) (t_right : Int) (PreH1 : (t_right = (0 : Int))) (PreH2 : (t_pre ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
  ** (store_tree t_right r0)
|--
  EX retval_left : Int, EX retval_right : Int, EX pt : partial_tree, EX tr_ret_left : tree, EX retval_key : Int, EX retval_value : Int,
  “ (t_pre ≠ (0 : Int)) ” &&
  “ forall (tr_ret_right : tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) ” &&
  “ (retval_right = (0 : Int)) ” &&
  “ (INT_MIN <= retval_key) ” &&
  “ (retval_key <= INT_MAX) ”
  &&  ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (retval_right))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt t_pre t_pre pt)
) \/
(
forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_right : Int) (PreH1 : (t_right = (0 : Int))) (PreH2 : (t_pre ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  (store_tree t_right r0)
|--
  EX pt : partial_tree,
  “ (t_right = (0 : Int)) ” &&
  “ (t_right = (0 : Int)) ” &&
  “ (t_pre ≠ (0 : Int)) ” &&
  “ forall (tr_ret_right : tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (l0) (t_key) (t_value) (tr_ret_right))))) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ”
  &&  (store_pt t_pre t_pre pt)
)

noncomputable def get_pre_partial_solve_wit_1_pure : Prop :=
  forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_left : Int) (t_right : Int) (PreH1 : (t_right ≠ (0 : Int))) (PreH2 : (t_pre ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((( &( "t" ) )) # Ptr |-> (t_pre))
  ** ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
  ** (store_tree t_right r0)
|--
  “ (t_right ≠ (0 : Int)) ”

noncomputable def get_pre_partial_solve_wit_1_aux : Prop :=
  forall (tr : tree) (t_pre : Int) (l0 : tree) (r0 : tree) (t_key : Int) (t_value : Int) (t_left : Int) (t_right : Int) (PreH1 : (t_right ≠ (0 : Int))) (PreH2 : (t_pre ≠ (0 : Int))) (PreH3 : (INT_MIN <= t_key)) (PreH4 : (t_key <= INT_MAX)) (PreH5 : (tr = (make_tree (l0) (t_key) (t_value) (r0)))) ,
  ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))
  ** (store_tree t_right r0)
|--
  “ (t_right ≠ (0 : Int)) ” &&
  “ (t_right ≠ (0 : Int)) ” &&
  “ (t_pre ≠ (0 : Int)) ” &&
  “ (INT_MIN <= t_key) ” &&
  “ (t_key <= INT_MAX) ” &&
  “ (tr = (make_tree (l0) (t_key) (t_value) (r0))) ”
  &&  (store_tree t_right r0)
  ** ((&((t_pre # "tree")  ->ₛ "key")) # Int |-> (t_key))
  ** ((&((t_pre # "tree")  ->ₛ "value")) # Int |-> (t_value))
  ** ((&((t_pre # "tree")  ->ₛ "left")) # Ptr |-> (t_left))
  ** (store_tree t_left l0)
  ** ((&((t_pre # "tree")  ->ₛ "right")) # Ptr |-> (t_right))

noncomputable def get_pre_partial_solve_wit_1 : Prop := get_pre_partial_solve_wit_1_pure -> get_pre_partial_solve_wit_1_aux

noncomputable def delete_safety_wit_1 : Prop :=
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (b_v : Int) (PreH1 : (INT_MIN <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "p" ) )) # Ptr |-> (b_v))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v tr_low_level_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def delete_safety_wit_2 : Prop :=
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre <= p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
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

noncomputable def delete_safety_wit_3 : Prop :=
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (retval_left : Int) (retval_right : Int) (pt : partial_tree) (tr_ret_left : tree) (retval_key : Int) (retval_value : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : forall (tr_ret_right : tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH3 : (retval_right = (0 : Int))) (PreH4 : (INT_MIN <= retval_key)) (PreH5 : (retval_key <= INT_MAX)) (PreH6 : (p_left ≠ (0 : Int))) (PreH7 : (x_pre <= p_key)) (PreH8 : (x_pre >= p_key)) (PreH9 : (p = b_v)) (PreH10 : (p ≠ (0 : Int))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval p_left pt)
  ** ((( &( "pre" ) )) # Ptr |-> (retval))
  ** ((( &( "y" ) )) # Int |-> (p_key))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def delete_entail_wit_1 : Prop :=
  (
forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (b_v : Int) (PreH1 : (b_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v tr_low_level_spec)
|--
  EX p_right : Int, EX p_left : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key : Int, EX b_v_2 : Int,
  “ (b_v = b_v_2) ” &&
  “ (b_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((b_pre) # Ptr |-> (b_v_2))
  ** ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
) \/
(
forall (tr_low_level_spec : tree) (x_pre : Int) (b_v : Int) (PreH1 : (b_v ≠ (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (store_tree b_v tr_low_level_spec)
|--
  EX p_right : Int, EX p_left : Int, EX l0 : tree, EX p_value : Int, EX r0 : tree, EX p_key : Int,
  “ (b_v ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  ((&((b_v # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((b_v # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((b_v # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((b_v # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
)

noncomputable def delete_return_wit_1 : Prop :=
  (
forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (b_v_2 : Int) (PreH1 : (b_v_2 = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((b_pre) # Ptr |-> (b_v_2))
  ** (store_tree b_v_2 tr_low_level_spec)
|--
  EX b_v : Int,
  ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)))
) \/
(
forall (tr_low_level_spec : tree) (x_pre : Int) (b_v_2 : Int) (PreH1 : (b_v_2 = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (tr_low_level_spec = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  emp
)

noncomputable def delete_return_wit_1_split_goal_1 : Prop :=
  forall (tr_low_level_spec : tree) (x_pre : Int) (b_v_2 : Int) (PreH1 : (b_v_2 = (0 : Int))) (PreH2 : (INT_MIN <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (tr_low_level_spec = (tree_delete (x_pre) (tr_low_level_spec)))

noncomputable def delete_return_wit_2 : Prop :=
  (
forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_right : Int) (b_v_3 : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v_2)) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 (tree_delete (x_pre) (l0)))
  ** ((b_pre) # Ptr |-> (b_v_2))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  EX b_v : Int,
  ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)))
) \/
(
forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_right : Int) (b_v_3 : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v_2)) (PreH6 : (p ≠ (0 : Int))) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 (tree_delete (x_pre) (l0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  (store_tree b_v_2 (tree_delete (x_pre) (tr_low_level_spec)))
)

noncomputable def delete_return_wit_2_split_goal_spatial : Prop :=
  forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_right : Int) (b_v_3 : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre < p_key)) (PreH5 : (p = b_v_2)) (PreH6 : (p ≠ (0 : Int))) (PreH7 : (INT_MIN <= p_key)) (PreH8 : (p_key <= INT_MAX)) (PreH9 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 (tree_delete (x_pre) (l0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  (store_tree b_v_2 (tree_delete (x_pre) (tr_low_level_spec)))

noncomputable def delete_return_wit_3 : Prop :=
  (
forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (b_v_3 : Int) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v_2)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 (tree_delete (x_pre) (r0)))
  ** ((b_pre) # Ptr |-> (b_v_2))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  EX b_v : Int,
  ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)))
) \/
(
forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (b_v_3 : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v_2)) (PreH7 : (p ≠ (0 : Int))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 (tree_delete (x_pre) (r0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  (store_tree b_v_2 (tree_delete (x_pre) (tr_low_level_spec)))
)

noncomputable def delete_return_wit_3_split_goal_spatial : Prop :=
  forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (b_v_3 : Int) (PreH1 : (p_value <= INT_MAX)) (PreH2 : (p_value >= INT_MIN)) (PreH3 : (p_key >= INT_MIN)) (PreH4 : (x_pre > p_key)) (PreH5 : (x_pre >= p_key)) (PreH6 : (p = b_v_2)) (PreH7 : (p ≠ (0 : Int))) (PreH8 : (INT_MIN <= p_key)) (PreH9 : (p_key <= INT_MAX)) (PreH10 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 (tree_delete (x_pre) (r0)))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
|--
  (store_tree b_v_2 (tree_delete (x_pre) (tr_low_level_spec)))

noncomputable def delete_return_wit_4 : Prop :=
  (
forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr |-> (p_right))
  ** (store_tree p_left l0)
  ** (store_tree p_right r0)
|--
  EX b_v : Int,
  ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)))
) \/
(
forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0)
|--
  “ (r0 = (tree_delete (x_pre) (tr_low_level_spec))) ”
  &&  emp
)

noncomputable def delete_return_wit_4_split_goal_1 : Prop :=
  forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0)
|--
  “ (r0 = (tree_delete (x_pre) (tr_low_level_spec))) ”

noncomputable def delete_return_wit_4_split_goal_spatial : Prop :=
  forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v_2)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  (store_tree p_left l0)
|--
  TT && emp 

noncomputable def delete_return_wit_5 : Prop :=
  (
forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (retval_left : Int) (retval_right : Int) (pt : partial_tree) (tr_ret_left : tree) (retval_key : Int) (retval_value : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : forall (tr_ret_right : tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH3 : (retval_right = (0 : Int))) (PreH4 : (INT_MIN <= retval_key)) (PreH5 : (retval_key <= INT_MAX)) (PreH6 : (p_left ≠ (0 : Int))) (PreH7 : (x_pre <= p_key)) (PreH8 : (x_pre >= p_key)) (PreH9 : (p = b_v_2)) (PreH10 : (p ≠ (0 : Int))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval p_left pt)
  ** ((b_pre) # Ptr |-> (p_left))
  ** (store_tree p_right r0)
|--
  EX b_v : Int,
  ((b_pre) # Ptr |-> (b_v))
  ** (store_tree b_v (tree_delete (x_pre) (tr_low_level_spec)))
) \/
(
forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (retval_left : Int) (retval_right : Int) (pt : partial_tree) (tr_ret_left : tree) (retval_key : Int) (retval_value : Int) (retval : Int) (PreH1 : (retval_value <= INT_MAX)) (PreH2 : (retval_key >= INT_MIN)) (PreH3 : (retval_value >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : forall (tr_ret_right : tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH6 : (retval_right = (0 : Int))) (PreH7 : (INT_MIN <= retval_key)) (PreH8 : (retval_key <= INT_MAX)) (PreH9 : (p_left ≠ (0 : Int))) (PreH10 : (x_pre <= p_key)) (PreH11 : (x_pre >= p_key)) (PreH12 : (p = b_v_2)) (PreH13 : (p ≠ (0 : Int))) (PreH14 : (INT_MIN <= p_key)) (PreH15 : (p_key <= INT_MAX)) (PreH16 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval p_left pt)
  ** (store_tree p_right r0)
|--
  (store_tree p_left (tree_delete (x_pre) (tr_low_level_spec)))
)

noncomputable def delete_return_wit_5_split_goal_spatial : Prop :=
  forall (tr_low_level_spec : tree) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v_2 : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (retval_left : Int) (retval_right : Int) (pt : partial_tree) (tr_ret_left : tree) (retval_key : Int) (retval_value : Int) (retval : Int) (PreH1 : (retval_value <= INT_MAX)) (PreH2 : (retval_key >= INT_MIN)) (PreH3 : (retval_value >= INT_MIN)) (PreH4 : (retval ≠ (0 : Int))) (PreH5 : forall (tr_ret_right : tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH6 : (retval_right = (0 : Int))) (PreH7 : (INT_MIN <= retval_key)) (PreH8 : (retval_key <= INT_MAX)) (PreH9 : (p_left ≠ (0 : Int))) (PreH10 : (x_pre <= p_key)) (PreH11 : (x_pre >= p_key)) (PreH12 : (p = b_v_2)) (PreH13 : (p ≠ (0 : Int))) (PreH14 : (INT_MIN <= p_key)) (PreH15 : (p_key <= INT_MAX)) (PreH16 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval p_left pt)
  ** (store_tree p_right r0)
|--
  (store_tree p_left (tree_delete (x_pre) (tr_low_level_spec)))

noncomputable def delete_partial_solve_wit_1_pure : Prop :=
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
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
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre < p_key)) (PreH2 : (p = b_v)) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (INT_MIN <= p_key)) (PreH5 : (p_key <= INT_MAX)) (PreH6 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
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
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
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
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (x_pre > p_key)) (PreH2 : (x_pre >= p_key)) (PreH3 : (p = b_v)) (PreH4 : (p ≠ (0 : Int))) (PreH5 : (INT_MIN <= p_key)) (PreH6 : (p_key <= INT_MAX)) (PreH7 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
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
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_left = (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
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
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_left ≠ (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((( &( "pre" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Int |-> (p_key))
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
  “ (p_left ≠ (0 : Int)) ”

noncomputable def delete_partial_solve_wit_4_aux : Prop :=
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (PreH1 : (p_left ≠ (0 : Int))) (PreH2 : (x_pre <= p_key)) (PreH3 : (x_pre >= p_key)) (PreH4 : (p = b_v)) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (INT_MIN <= p_key)) (PreH7 : (p_key <= INT_MAX)) (PreH8 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** (store_tree p_left l0)
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)
|--
  “ (p_left ≠ (0 : Int)) ” &&
  “ (p_left ≠ (0 : Int)) ” &&
  “ (x_pre <= p_key) ” &&
  “ (x_pre >= p_key) ” &&
  “ (p = b_v) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (INT_MIN <= p_key) ” &&
  “ (p_key <= INT_MAX) ” &&
  “ (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) ”
  &&  (store_tree p_left l0)
  ** ((b_pre) # Ptr |-> (b_v))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** (store_tree p_right r0)

noncomputable def delete_partial_solve_wit_4 : Prop := delete_partial_solve_wit_4_pure -> delete_partial_solve_wit_4_aux

noncomputable def delete_partial_solve_wit_5 : Prop :=
  forall (tr_low_level_spec : tree) (b_pre : Int) (x_pre : Int) (l0 : tree) (r0 : tree) (p : Int) (b_v : Int) (p_key : Int) (p_value : Int) (p_left : Int) (p_right : Int) (retval_left : Int) (retval_right : Int) (pt : partial_tree) (tr_ret_left : tree) (retval_key : Int) (retval_value : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : forall (tr_ret_right : tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right)))))) (PreH3 : (retval_right = (0 : Int))) (PreH4 : (INT_MIN <= retval_key)) (PreH5 : (retval_key <= INT_MAX)) (PreH6 : (p_left ≠ (0 : Int))) (PreH7 : (x_pre <= p_key)) (PreH8 : (x_pre >= p_key)) (PreH9 : (p = b_v)) (PreH10 : (p ≠ (0 : Int))) (PreH11 : (INT_MIN <= p_key)) (PreH12 : (p_key <= INT_MAX)) (PreH13 : (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0)))) ,
  ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval p_left pt)
  ** ((b_pre) # Ptr |-> (p_left))
  ** ((&((p # "tree")  ->ₛ "key")) # Int |-> (p_key))
  ** ((&((p # "tree")  ->ₛ "value")) # Int |-> (p_value))
  ** ((&((p # "tree")  ->ₛ "left")) # Ptr |-> (p_left))
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** (store_tree p_right r0)
|--
  “ (retval ≠ (0 : Int)) ” &&
  “ forall (tr_ret_right : tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) ” &&
  “ (retval_right = (0 : Int)) ” &&
  “ (INT_MIN <= retval_key) ” &&
  “ (retval_key <= INT_MAX) ” &&
  “ (p_left ≠ (0 : Int)) ” &&
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
  ** ((&((p # "tree")  ->ₛ "right")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (retval_value))
  ** ((&((retval # "tree")  ->ₛ "key")) # Int |-> (retval_key))
  ** ((&((retval # "tree")  ->ₛ "right")) # Ptr |-> (p_right))
  ** ((&((retval # "tree")  ->ₛ "left")) # Ptr |-> (retval_left))
  ** (store_tree retval_left tr_ret_left)
  ** (store_pt retval p_left pt)
  ** ((b_pre) # Ptr |-> (p_left))
  ** (store_tree p_right r0)

noncomputable def delete_low_level_spec_entail_high_level_spec : Prop :=
  forall (b_pre : Int) (x_pre : Int) (m_high_level_spec : mapping) ,
  (EX b_v : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr |-> (b_v))
  ** (Bst.store_map b_v m_high_level_spec))
|--
  EX tr_low_level_spec : tree,
  (EX b_v_3 : Int,
  “ (INT_MIN <= x_pre) ” &&
  “ (x_pre <= INT_MAX) ”
  &&  ((b_pre) # Ptr |-> (b_v_3))
  ** (store_tree b_v_3 tr_low_level_spec))
  **
  ((EX b_v_4 : Int,
  ((b_pre) # Ptr |-> (b_v_4))
  ** (store_tree b_v_4 (tree_delete (x_pre) (tr_low_level_spec))))
  -*
  (EX b_v_2 : Int,
  ((b_pre) # Ptr |-> (b_v_2))
  ** (Bst.store_map b_v_2 (map_delete (x_pre) (m_high_level_spec)))))


structure VC_Correct : Type where
  proof_of_get_pre_safety_wit_1 : get_pre_safety_wit_1
  proof_of_get_pre_partial_solve_wit_1_pure : get_pre_partial_solve_wit_1_pure
  proof_of_get_pre_partial_solve_wit_1 : get_pre_partial_solve_wit_1
  proof_of_delete_safety_wit_1 : delete_safety_wit_1
  proof_of_delete_safety_wit_2 : delete_safety_wit_2
  proof_of_delete_safety_wit_3 : delete_safety_wit_3
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
  proof_of_delete_return_wit_1 : delete_return_wit_1
  proof_of_delete_return_wit_2 : delete_return_wit_2
  proof_of_delete_return_wit_3 : delete_return_wit_3
  proof_of_delete_return_wit_4 : delete_return_wit_4
  proof_of_delete_return_wit_5 : delete_return_wit_5
  proof_of_delete_low_level_spec_entail_high_level_spec : delete_low_level_spec_entail_high_level_spec

end SimpleC.EE.QCP_demos_LLM.generated.bst_delete_rec_goal
