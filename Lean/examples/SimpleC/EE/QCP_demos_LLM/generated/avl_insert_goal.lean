import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.avl_shape

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.avl_insert_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance avl_insert_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def update_height_safety_wit_1 : Prop :=
  forall (root_pre : Int) ,
  ((( &( "rh" ) )) # UChar |->_)
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
  ** (store_non_empty_tree root_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def update_height_safety_wit_2 : Prop :=
  forall (root_pre : Int) ,
  ((( &( "lh" ) )) # UChar |->_)
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
  ** (store_non_empty_tree root_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def update_height_safety_wit_3 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (tr = (make_tree (tr1) (tr2)))) (PreH4 : (root_pre ≠ (0 : Int))) (PreH5 : ((0 : Int) <= 255)) (PreH6 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def update_height_safety_wit_4 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre ≠ (0 : Int))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def update_height_safety_wit_5 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (tr1 = empty)) (PreH2 : (l = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (root_pre ≠ (0 : Int))) (PreH7 : ((0 : Int) <= 255)) (PreH8 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def update_height_safety_wit_6 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : ((0 : Int) > h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (tr1 = empty)) (PreH7 : (l = (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h_2))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ False ”

noncomputable def update_height_safety_wit_7 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h <= 255)) (PreH7 : (h >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h l_2 r_2)
  ** (single_tree_node root_pre k v h_2 l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h_3))
  ** ((( &( "lh" ) )) # UChar |-> (h))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((h + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h + 1)) ”

noncomputable def update_height_safety_wit_8 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h <= 255)) (PreH11 : (h >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h_3))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def update_height_safety_wit_9 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h > (0 : Int))) (PreH2 : (r = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h l_2 r_2)
  ** (single_tree_node root_pre k v h_2 l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((h + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h + 1)) ”

noncomputable def update_height_safety_wit_10 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 > (0 : Int))) (PreH2 : (r = (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def update_height_safety_wit_11 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_3 <= h)) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_3 <= 255)) (PreH7 : (h_3 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node root_pre k v h_2 l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h))
  ** ((( &( "lh" ) )) # UChar |-> (h_3))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((h + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h + 1)) ”

noncomputable def update_height_safety_wit_12 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 <= h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h <= 255)) (PreH11 : (h >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h_3))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def update_height_safety_wit_13 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : ((0 : Int) <= h)) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (tr1 = empty)) (PreH7 : (l = (0 : Int))) (PreH8 : (h_2 <= 255)) (PreH9 : (h_2 >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_2 v_2 h l_2 r_2)
  ** (single_tree_node root_pre k v h_2 l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((h + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h + 1)) ”

noncomputable def update_height_safety_wit_14 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : ((0 : Int) <= h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (tr1 = empty)) (PreH7 : (l = (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h_2))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def update_height_safety_wit_15 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= (0 : Int))) (PreH2 : (r = (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (((0 : Int) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) + 1)) ”

noncomputable def update_height_safety_wit_16 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= (0 : Int))) (PreH2 : (r = (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def update_height_safety_wit_17 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r = (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre ≠ (0 : Int))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (((0 : Int) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) + 1)) ”

noncomputable def update_height_safety_wit_18 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r = (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre ≠ (0 : Int))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def update_height_return_wit_1 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h <= 255)) (PreH11 : (h >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_2 + 1)) (8)) l r)
  ** (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  (store_non_empty_tree root_pre)

noncomputable def update_height_return_wit_2 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (tr2 = empty)) (PreH2 : (h_2 > (0 : Int))) (PreH3 : (r = (0 : Int))) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= (0 : Int))) (PreH6 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l ≠ (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_2 + 1)) (8)) l r)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  (store_non_empty_tree root_pre)

noncomputable def update_height_return_wit_3 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 <= h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h <= 255)) (PreH11 : (h >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_3 + 1)) (8)) l r)
  ** (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  (store_non_empty_tree root_pre)

noncomputable def update_height_return_wit_4 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : ((0 : Int) <= h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (tr1 = empty)) (PreH7 : (l = (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_2 + 1)) (8)) l r)
  ** (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  (store_non_empty_tree root_pre)

noncomputable def update_height_return_wit_5 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (tr2 = empty)) (PreH2 : (h_2 <= (0 : Int))) (PreH3 : (r = (0 : Int))) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= (0 : Int))) (PreH6 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l ≠ (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v ((0 : Int) + 1) l r)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  (store_non_empty_tree root_pre)

noncomputable def update_height_return_wit_6 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (tr2 = empty)) (PreH2 : (r = (0 : Int))) (PreH3 : (tr1 = empty)) (PreH4 : (l = (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre ≠ (0 : Int))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v ((0 : Int) + 1) l r)
|--
  (store_non_empty_tree root_pre)

noncomputable def update_height_partial_solve_wit_1 : Prop :=
  forall (root_pre : Int) ,
  (store_non_empty_tree root_pre)
|--
  EX tr2 : tree, EX tr1 : tree, EX r : Int, EX l : Int, EX h : Int, EX v : Int, EX k : Int, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr2)
  ** (store_tree l tr1)

noncomputable def update_height_partial_solve_wit_2 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (l ≠ (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (root_pre ≠ (0 : Int))) (PreH6 : ((0 : Int) <= 255)) (PreH7 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int,
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)

noncomputable def update_height_partial_solve_wit_3 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre ≠ (0 : Int))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)

noncomputable def update_height_partial_solve_wit_4 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre ≠ (0 : Int))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)

noncomputable def update_height_partial_solve_wit_5 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (l = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (root_pre ≠ (0 : Int))) (PreH6 : ((0 : Int) <= 255)) (PreH7 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
|--
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr2)

noncomputable def update_height_partial_solve_wit_6 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (r ≠ (0 : Int))) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= (0 : Int))) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l ≠ (0 : Int))) (PreH6 : (h <= 255)) (PreH7 : (h >= (0 : Int))) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (root_pre ≠ (0 : Int))) (PreH10 : ((0 : Int) <= 255)) (PreH11 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX r_3 : Int, EX l_3 : Int, EX h_3 : Int, EX v_3 : Int, EX k_3 : Int,
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_7 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (h <= 255)) (PreH10 : (h >= (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (root_pre ≠ (0 : Int))) (PreH13 : ((0 : Int) <= 255)) (PreH14 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_8 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r ≠ (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre ≠ (0 : Int))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int,
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_9 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (tr1 = empty)) (PreH6 : (l = (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_10 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h <= 255)) (PreH11 : (h >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ (h_2 > h_3) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_11 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 > (0 : Int))) (PreH2 : (r = (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  “ (tr2 = empty) ” &&
  “ (h_2 > (0 : Int)) ” &&
  “ (r = (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_12 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 <= h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (h <= 255)) (PreH11 : (h >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre ≠ (0 : Int))) (PreH14 : ((0 : Int) <= 255)) (PreH15 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ (h_2 <= h_3) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_13 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : ((0 : Int) <= h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= (0 : Int))) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r ≠ (0 : Int))) (PreH6 : (tr1 = empty)) (PreH7 : (l = (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre ≠ (0 : Int))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ ((0 : Int) <= h_2) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_14 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= (0 : Int))) (PreH2 : (r = (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : ((0 : Int) <= 255)) (PreH12 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  “ (tr2 = empty) ” &&
  “ (h_2 <= (0 : Int)) ” &&
  “ (r = (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def update_height_partial_solve_wit_15 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r = (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre ≠ (0 : Int))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
|--
  “ (tr2 = empty) ” &&
  “ (r = (0 : Int)) ” &&
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))

noncomputable def rotateR_return_wit_1 : Prop :=
  forall (root_pre : Int) (h : Int) (l : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (root_pre ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (root_pre ≠ (0 : Int))) ,
  (store_non_empty_tree l)
|--
  “ (l = l) ”
  &&  (store_non_empty_tree l)

noncomputable def rotateR_partial_solve_wit_1 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (PreH1 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
|--
  EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_2 : tree, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)

noncomputable def rotateR_partial_solve_wit_2 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)

noncomputable def rotateR_partial_solve_wit_3 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)

noncomputable def rotateR_partial_solve_wit_4 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h r_2 r)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((l # "tree")  ->ₛ "rchild")) # Ptr |->_)
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (r_2))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)

noncomputable def rotateR_partial_solve_wit_5 : Prop :=
  forall (root_pre : Int) (h : Int) (v_2 : Int) (k_2 : Int) (r : Int) (l : Int) (tr_2 : tree) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k v h_2 l_2 root_pre)
  ** (single_tree_node root_pre k_2 v_2 h r_2 r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr_2)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (store_non_empty_tree root_pre)
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (root_pre))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree l_2 tr1)

noncomputable def rotateR_partial_solve_wit_6 : Prop :=
  forall (root_pre : Int) (h : Int) (l : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k v h_2 l_2 root_pre)
  ** (store_non_empty_tree root_pre)
  ** (store_tree l_2 tr1)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_3 : Int, EX tr_2 : tree,
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (store_non_empty_tree l)

noncomputable def rotateL_return_wit_1 : Prop :=
  forall (root_pre : Int) (h : Int) (r : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (root_pre ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (root_pre ≠ (0 : Int))) ,
  (store_non_empty_tree r)
|--
  “ (r = r) ”
  &&  (store_non_empty_tree r)

noncomputable def rotateL_partial_solve_wit_1 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (PreH1 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
|--
  EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_2 : tree, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)

noncomputable def rotateL_partial_solve_wit_2 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)

noncomputable def rotateL_partial_solve_wit_3 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |->_)
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)

noncomputable def rotateL_partial_solve_wit_4 : Prop :=
  forall (root_pre : Int) (h : Int) (v : Int) (k : Int) (r : Int) (l : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l l_2)
  ** (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((r # "tree")  ->ₛ "lchild")) # Ptr |->_)
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (l_2))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)

noncomputable def rotateL_partial_solve_wit_5 : Prop :=
  forall (root_pre : Int) (h : Int) (v_2 : Int) (k_2 : Int) (r : Int) (l : Int) (tr_2 : tree) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (r ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k v h_2 root_pre r_2)
  ** (single_tree_node root_pre k_2 v_2 h l l_2)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr_2)
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (store_non_empty_tree root_pre)
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (root_pre))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r_2 tr2)

noncomputable def rotateL_partial_solve_wit_6 : Prop :=
  forall (root_pre : Int) (h : Int) (r : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (r ≠ (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k v h_2 root_pre r_2)
  ** (store_non_empty_tree root_pre)
  ** (store_tree r_2 tr2)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_3 : Int, EX tr_2 : tree,
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (store_non_empty_tree r)

noncomputable def rotateRL_return_wit_1 : Prop :=
  forall (root_pre : Int) (l1 : Int) (h1 : Int) (r : Int) (h : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval : Int) (PreH1 : (retval = l1)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l1 ≠ (0 : Int))) (PreH6 : (retval_2 = l1)) (PreH7 : (h1 <= 255)) (PreH8 : (h1 >= (0 : Int))) (PreH9 : (h <= 255)) (PreH10 : (h >= (0 : Int))) (PreH11 : (h_2 <= 255)) (PreH12 : (h_2 >= (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l1 ≠ (0 : Int))) (PreH15 : (root_pre ≠ (0 : Int))) (PreH16 : (r ≠ (0 : Int))) ,
  (store_non_empty_tree l1)
|--
  “ (retval = l1) ”
  &&  (store_non_empty_tree l1)

noncomputable def rotateRL_partial_solve_wit_1 : Prop :=
  forall (root_pre : Int) (r1 : Int) (l1 : Int) (h1 : Int) (v1 : Int) (k1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (PreH1 : (root_pre ≠ (0 : Int))) (PreH2 : (r ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (single_tree_node r k1 v1 h1 l1 r1)
  ** (store_tree_shape l)
  ** (store_non_empty_tree l1)
  ** (store_tree_shape r1)
|--
  EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_3 : tree, EX tr_2 : tree, EX tr : tree,
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1) (tr2))) ” &&
  “ (l1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r1))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l1))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h1))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v1))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k1))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l1 # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l1 # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l1 # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l1 # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l1 # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r1 tr_2)
  ** (store_tree l tr)

noncomputable def rotateRL_partial_solve_wit_2_pure : Prop :=
  forall (root_pre : Int) (r1 : Int) (l1 : Int) (h1 : Int) (v1 : Int) (k1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (l1 ≠ (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) (PreH10 : (r ≠ (0 : Int))) ,
  (single_tree_node l1 k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (single_tree_node r k1 v1 h1 l1 r1)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r1 tr_2)
  ** (store_tree l tr)
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (r ≠ (0 : Int)) ”

noncomputable def rotateRL_partial_solve_wit_2_aux : Prop :=
  forall (root_pre : Int) (r1 : Int) (l1 : Int) (h1 : Int) (v1 : Int) (k1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (l1 ≠ (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) (PreH10 : (r ≠ (0 : Int))) ,
  (single_tree_node l1 k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (single_tree_node r k1 v1 h1 l1 r1)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r1 tr_2)
  ** (store_tree l tr)
|--
  “ (r ≠ (0 : Int)) ” &&
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1) (tr2))) ” &&
  “ (l1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”
  &&  (single_tree_node r k1 v1 h1 l1 r1)
  ** (store_non_empty_tree l1)
  ** (store_tree_shape r1)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree l tr)

noncomputable def rotateRL_partial_solve_wit_2 : Prop := rotateRL_partial_solve_wit_2_pure -> rotateRL_partial_solve_wit_2_aux

noncomputable def rotateRL_partial_solve_wit_3 : Prop :=
  forall (root_pre : Int) (l1 : Int) (h1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval : Int) (PreH1 : (retval = l1)) (PreH2 : (h1 <= 255)) (PreH3 : (h1 >= (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l1 ≠ (0 : Int))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : (r ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_non_empty_tree l1)
  ** (store_tree l tr)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_2 : Int, EX l_2 : Int, EX h_3 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_3 : tree,
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l1 ≠ (0 : Int)) ” &&
  “ (retval = l1) ” &&
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |->_)
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l1 # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l1 # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l1 # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((l1 # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l1 # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree l tr)

noncomputable def rotateRL_partial_solve_wit_4_pure : Prop :=
  forall (root_pre : Int) (l1 : Int) (h1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval : Int) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l1 ≠ (0 : Int))) (PreH5 : (retval = l1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (l1 ≠ (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) (PreH15 : (r ≠ (0 : Int))) ,
  ((( &( "temp" ) )) # Ptr |->_)
  ** (single_tree_node root_pre k v h l retval)
  ** (single_tree_node l1 k_2 v_2 h_3 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree l tr)
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (root_pre ≠ (0 : Int)) ”

noncomputable def rotateRL_partial_solve_wit_4_aux : Prop :=
  forall (root_pre : Int) (l1 : Int) (h1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval : Int) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l1 ≠ (0 : Int))) (PreH5 : (retval = l1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (l1 ≠ (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) (PreH15 : (r ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l retval)
  ** (single_tree_node l1 k_2 v_2 h_3 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree l tr)
|--
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l1 ≠ (0 : Int)) ” &&
  “ (retval = l1) ” &&
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k v h l l1)
  ** (store_tree_shape l)
  ** (store_non_empty_tree l1)

noncomputable def rotateRL_partial_solve_wit_4 : Prop := rotateRL_partial_solve_wit_4_pure -> rotateRL_partial_solve_wit_4_aux

noncomputable def rotateLR_return_wit_1 : Prop :=
  forall (root_pre : Int) (r1 : Int) (h1 : Int) (l : Int) (h : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval : Int) (PreH1 : (retval = r1)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r1 ≠ (0 : Int))) (PreH6 : (retval_2 = r1)) (PreH7 : (h1 <= 255)) (PreH8 : (h1 >= (0 : Int))) (PreH9 : (h <= 255)) (PreH10 : (h >= (0 : Int))) (PreH11 : (h_2 <= 255)) (PreH12 : (h_2 >= (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (r1 ≠ (0 : Int))) (PreH15 : (root_pre ≠ (0 : Int))) (PreH16 : (l ≠ (0 : Int))) ,
  (store_non_empty_tree r1)
|--
  “ (retval = r1) ”
  &&  (store_non_empty_tree r1)

noncomputable def rotateLR_partial_solve_wit_1 : Prop :=
  forall (root_pre : Int) (r1 : Int) (l1 : Int) (h1 : Int) (v1 : Int) (k1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (PreH1 : (root_pre ≠ (0 : Int))) (PreH2 : (l ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (single_tree_node l k1 v1 h1 l1 r1)
  ** (store_tree_shape r)
  ** (store_tree_shape l1)
  ** (store_non_empty_tree r1)
|--
  EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_3 : tree, EX tr_2 : tree, EX tr : tree,
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1) (tr2))) ” &&
  “ (r1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r1))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l1))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h1))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v1))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k1))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r1 # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r1 # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r1 # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r1 # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r1 # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l1 tr_2)
  ** (store_tree r tr)

noncomputable def rotateLR_partial_solve_wit_2_pure : Prop :=
  forall (root_pre : Int) (r1 : Int) (l1 : Int) (h1 : Int) (v1 : Int) (k1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (r1 ≠ (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) (PreH10 : (l ≠ (0 : Int))) ,
  (single_tree_node r1 k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (single_tree_node l k1 v1 h1 l1 r1)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l1 tr_2)
  ** (store_tree r tr)
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (l ≠ (0 : Int)) ”

noncomputable def rotateLR_partial_solve_wit_2_aux : Prop :=
  forall (root_pre : Int) (r1 : Int) (l1 : Int) (h1 : Int) (v1 : Int) (k1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (r1 ≠ (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) (PreH10 : (l ≠ (0 : Int))) ,
  (single_tree_node r1 k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (single_tree_node l k1 v1 h1 l1 r1)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l1 tr_2)
  ** (store_tree r tr)
|--
  “ (l ≠ (0 : Int)) ” &&
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1) (tr2))) ” &&
  “ (r1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”
  &&  (single_tree_node l k1 v1 h1 l1 r1)
  ** (store_tree_shape l1)
  ** (store_non_empty_tree r1)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr)

noncomputable def rotateLR_partial_solve_wit_2 : Prop := rotateLR_partial_solve_wit_2_pure -> rotateLR_partial_solve_wit_2_aux

noncomputable def rotateLR_partial_solve_wit_3 : Prop :=
  forall (root_pre : Int) (r1 : Int) (h1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval : Int) (PreH1 : (retval = r1)) (PreH2 : (h1 <= 255)) (PreH3 : (h1 >= (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r1 ≠ (0 : Int))) (PreH10 : (root_pre ≠ (0 : Int))) (PreH11 : (l ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_non_empty_tree r1)
  ** (store_tree r tr)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_2 : Int, EX l_2 : Int, EX h_3 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_3 : tree,
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r1 ≠ (0 : Int)) ” &&
  “ (retval = r1) ” &&
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |->_)
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r1 # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r1 # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r1 # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r1 # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r1 # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr)

noncomputable def rotateLR_partial_solve_wit_4_pure : Prop :=
  forall (root_pre : Int) (r1 : Int) (h1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval : Int) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r1 ≠ (0 : Int))) (PreH5 : (retval = r1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (r1 ≠ (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) (PreH15 : (l ≠ (0 : Int))) ,
  ((( &( "temp" ) )) # Ptr |->_)
  ** (single_tree_node root_pre k v h retval r)
  ** (single_tree_node r1 k_2 v_2 h_3 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr)
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (root_pre ≠ (0 : Int)) ”

noncomputable def rotateLR_partial_solve_wit_4_aux : Prop :=
  forall (root_pre : Int) (r1 : Int) (h1 : Int) (r : Int) (l : Int) (h : Int) (v : Int) (k : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval : Int) (tr_3 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r1 ≠ (0 : Int))) (PreH5 : (retval = r1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (r1 ≠ (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) (PreH15 : (l ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h retval r)
  ** (single_tree_node r1 k_2 v_2 h_3 l_2 r_2)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr)
|--
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r1 ≠ (0 : Int)) ” &&
  “ (retval = r1) ” &&
  “ (h1 <= 255) ” &&
  “ (h1 >= (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r1 ≠ (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k v h r1 r)
  ** (store_non_empty_tree r1)
  ** (store_tree_shape r)

noncomputable def rotateLR_partial_solve_wit_4 : Prop := rotateLR_partial_solve_wit_4_pure -> rotateLR_partial_solve_wit_4_aux

noncomputable def balance_factor_safety_wit_1 : Prop :=
  forall (root_pre : Int) ,
  ((( &( "rh" ) )) # UChar |->_)
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
  ** (store_tree_shape root_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_2 : Prop :=
  forall (root_pre : Int) ,
  ((( &( "lh" ) )) # UChar |->_)
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
  ** (store_tree_shape root_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_3 : Prop :=
  forall (root_pre : Int) ,
  ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
  ** (store_tree_shape root_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_4 : Prop :=
  forall (root_pre : Int) (PreH1 : (root_pre = (0 : Int))) ,
  ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
  ** (store_tree_shape root_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_5 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (tr = (make_tree (tr1) (tr2)))) (PreH4 : ((0 : Int) <= 255)) (PreH5 : ((0 : Int) >= (0 : Int))) (PreH6 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_6 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) (PreH10 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h_2))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_7 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (tr1 = empty)) (PreH2 : (l = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : ((0 : Int) <= 255)) (PreH7 : ((0 : Int) >= (0 : Int))) (PreH8 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_factor_safety_wit_8 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r = (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : ((0 : Int) <= 255)) (PreH8 : ((0 : Int) >= (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (((0 : Int) - (0 : Int)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) - (0 : Int))) ”

noncomputable def balance_factor_safety_wit_9 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (r = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l ≠ (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) (PreH11 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h l_2 r_2)
  ** (single_tree_node root_pre k v h_2 l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
  ** ((( &( "rh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # UChar |-> (h))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((h - (0 : Int)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h - (0 : Int))) ”

noncomputable def balance_factor_safety_wit_10 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_2 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (tr1 = empty)) (PreH6 : (l = (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : ((0 : Int) <= 255)) (PreH11 : ((0 : Int) >= (0 : Int))) (PreH12 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h l_2 r_2)
  ** (single_tree_node root_pre k v h_2 l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h))
  ** ((( &( "lh" ) )) # UChar |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ (((0 : Int) - h) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) - h)) ”

noncomputable def balance_factor_safety_wit_11 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h_3 : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_2 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_2 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h l_2 r_2)
  ** (single_tree_node root_pre k v h_3 l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "rh" ) )) # UChar |-> (h_2))
  ** ((( &( "lh" ) )) # UChar |-> (h))
  ** ((( &( "root" ) )) # Ptr |-> (root_pre))
|--
  “ ((h - h_2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h - h_2)) ”

noncomputable def balance_factor_return_wit_1 : Prop :=
  forall (root_pre : Int) (tr : tree) (k_4 : Int) (v_4 : Int) (h_6 : Int) (l_4 : Int) (r_4 : Int) (tr1 : tree) (tr2 : tree) (k_5 : Int) (v_5 : Int) (h : Int) (l_5 : Int) (r_5 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_6 : Int) (v_6 : Int) (h_2 : Int) (l_6 : Int) (r_6 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r_4 ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l_4 ≠ (0 : Int))) (PreH9 : (h_6 <= 255)) (PreH10 : (h_6 >= (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r_4 k_6 v_6 h_2 l_6 r_6)
  ** (single_tree_node l_4 k_5 v_5 h l_5 r_5)
  ** (single_tree_node root_pre k_4 v_4 h_6 l_4 r_4)
  ** (store_tree r_6 tr2_3)
  ** (store_tree l_6 tr1_3)
  ** (store_tree r_5 tr2_2)
  ** (store_tree l_5 tr1_2)
|--
  (“ ((h - h_2) = (0 : Int)) ”
  &&  (store_tree_shape root_pre))
  ||
  (EX k : Int, EX v : Int, EX h_3 : Int, EX l : Int, EX r : Int,
  “ ((h - h_2) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k v h_3 l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r))
  ||
  (EX k_2 : Int, EX v_2 : Int, EX h_4 : Int, EX l_2 : Int, EX r_2 : Int,
  “ ((h - h_2) <= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_2 v_2 h_4 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2))
  ||
  (EX k_3 : Int, EX v_3 : Int, EX h_5 : Int, EX l_3 : Int, EX r_3 : Int, EX x : Int,
  “ ((h - h_2) = x) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_3 v_3 h_5 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3))

noncomputable def balance_factor_return_wit_2 : Prop :=
  forall (root_pre : Int) (tr : tree) (k_4 : Int) (v_4 : Int) (h_5 : Int) (l_4 : Int) (r_4 : Int) (tr1 : tree) (tr2 : tree) (k_5 : Int) (v_5 : Int) (h : Int) (l_5 : Int) (r_5 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r_4 ≠ (0 : Int))) (PreH5 : (tr1 = empty)) (PreH6 : (l_4 = (0 : Int))) (PreH7 : (h_5 <= 255)) (PreH8 : (h_5 >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : ((0 : Int) <= 255)) (PreH11 : ((0 : Int) >= (0 : Int))) (PreH12 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r_4 k_5 v_5 h l_5 r_5)
  ** (single_tree_node root_pre k_4 v_4 h_5 l_4 r_4)
  ** (store_tree r_5 tr2_2)
  ** (store_tree l_5 tr1_2)
|--
  (“ (((0 : Int) - h) = (0 : Int)) ”
  &&  (store_tree_shape root_pre))
  ||
  (EX k : Int, EX v : Int, EX h_2 : Int, EX l : Int, EX r : Int,
  “ (((0 : Int) - h) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k v h_2 l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r))
  ||
  (EX k_2 : Int, EX v_2 : Int, EX h_3 : Int, EX l_2 : Int, EX r_2 : Int,
  “ (((0 : Int) - h) <= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2))
  ||
  (EX k_3 : Int, EX v_3 : Int, EX h_4 : Int, EX l_3 : Int, EX r_3 : Int, EX x : Int,
  “ (((0 : Int) - h) = x) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3))

noncomputable def balance_factor_return_wit_3 : Prop :=
  forall (root_pre : Int) (tr : tree) (k_4 : Int) (v_4 : Int) (h_5 : Int) (l_4 : Int) (r_4 : Int) (tr1 : tree) (tr2 : tree) (k_5 : Int) (v_5 : Int) (h : Int) (l_5 : Int) (r_5 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (r_4 = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l_4 ≠ (0 : Int))) (PreH6 : (h_5 <= 255)) (PreH7 : (h_5 >= (0 : Int))) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) (PreH11 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l_4 k_5 v_5 h l_5 r_5)
  ** (single_tree_node root_pre k_4 v_4 h_5 l_4 r_4)
  ** (store_tree r_5 tr2_2)
  ** (store_tree l_5 tr1_2)
  ** (store_tree r_4 tr2)
|--
  (“ ((h - (0 : Int)) = (0 : Int)) ”
  &&  (store_tree_shape root_pre))
  ||
  (EX k : Int, EX v : Int, EX h_2 : Int, EX l : Int, EX r : Int,
  “ ((h - (0 : Int)) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k v h_2 l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r))
  ||
  (EX k_2 : Int, EX v_2 : Int, EX h_3 : Int, EX l_2 : Int, EX r_2 : Int,
  “ ((h - (0 : Int)) <= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2))
  ||
  (EX k_3 : Int, EX v_3 : Int, EX h_4 : Int, EX l_3 : Int, EX r_3 : Int, EX x : Int,
  “ ((h - (0 : Int)) = x) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3))

noncomputable def balance_factor_return_wit_4 : Prop :=
  forall (root_pre : Int) (tr : tree) (k_4 : Int) (v_4 : Int) (h_4 : Int) (l_4 : Int) (r_4 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r_4 = (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l_4 = (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : ((0 : Int) <= 255)) (PreH8 : ((0 : Int) >= (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k_4 v_4 h_4 l_4 r_4)
  ** (store_tree r_4 tr2)
|--
  (“ (((0 : Int) - (0 : Int)) = (0 : Int)) ”
  &&  (store_tree_shape root_pre))
  ||
  (EX k : Int, EX v : Int, EX h : Int, EX l : Int, EX r : Int,
  “ (((0 : Int) - (0 : Int)) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r))
  ||
  (EX k_2 : Int, EX v_2 : Int, EX h_2 : Int, EX l_2 : Int, EX r_2 : Int,
  “ (((0 : Int) - (0 : Int)) <= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_2 v_2 h_2 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2))
  ||
  (EX k_3 : Int, EX v_3 : Int, EX h_3 : Int, EX l_3 : Int, EX r_3 : Int, EX x : Int,
  “ (((0 : Int) - (0 : Int)) = x) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  (single_tree_node root_pre k_3 v_3 h_3 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3))

noncomputable def balance_factor_return_wit_5 : Prop :=
  forall (root_pre : Int) (PreH1 : (root_pre = (0 : Int))) ,
  (store_tree_shape root_pre)
|--
  “ ((0 : Int) = (0 : Int)) ”
  &&  (store_tree_shape root_pre)

noncomputable def balance_factor_partial_solve_wit_1 : Prop :=
  forall (root_pre : Int) (PreH1 : (root_pre ≠ (0 : Int))) ,
  (store_tree_shape root_pre)
|--
  EX tr2 : tree, EX tr1 : tree, EX r : Int, EX l : Int, EX h : Int, EX v : Int, EX k : Int, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr2)
  ** (store_tree l tr1)

noncomputable def balance_factor_partial_solve_wit_2 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (l ≠ (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : ((0 : Int) <= 255)) (PreH6 : ((0 : Int) >= (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int,
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)

noncomputable def balance_factor_partial_solve_wit_3 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) (PreH10 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)

noncomputable def balance_factor_partial_solve_wit_4 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : ((0 : Int) <= 255)) (PreH9 : ((0 : Int) >= (0 : Int))) (PreH10 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)

noncomputable def balance_factor_partial_solve_wit_5 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (l = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : ((0 : Int) <= 255)) (PreH6 : ((0 : Int) >= (0 : Int))) (PreH7 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
|--
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr2)

noncomputable def balance_factor_partial_solve_wit_6 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (r ≠ (0 : Int))) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= (0 : Int))) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l ≠ (0 : Int))) (PreH6 : (h <= 255)) (PreH7 : (h >= (0 : Int))) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : ((0 : Int) <= 255)) (PreH10 : ((0 : Int) >= (0 : Int))) (PreH11 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r tr2)
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX r_3 : Int, EX l_3 : Int, EX h_3 : Int, EX v_3 : Int, EX k_3 : Int,
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def balance_factor_partial_solve_wit_7 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_3 : tree) (tr2_3 : tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (h <= 255)) (PreH10 : (h >= (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : ((0 : Int) <= 255)) (PreH13 : ((0 : Int) >= (0 : Int))) (PreH14 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_3)
  ** (store_tree l_3 tr1_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def balance_factor_partial_solve_wit_8 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (r ≠ (0 : Int))) (PreH2 : (tr1 = empty)) (PreH3 : (l = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : ((0 : Int) <= 255)) (PreH8 : ((0 : Int) >= (0 : Int))) (PreH9 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node root_pre k v h l r)
  ** (store_tree r tr2)
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int,
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def balance_factor_partial_solve_wit_9 : Prop :=
  forall (root_pre : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (tr1 = empty)) (PreH6 : (l = (0 : Int))) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : ((0 : Int) <= 255)) (PreH11 : ((0 : Int) >= (0 : Int))) (PreH12 : (root_pre ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node root_pre k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
|--
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr1 = empty) ” &&
  “ (l = (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ ((0 : Int) <= 255) ” &&
  “ ((0 : Int) >= (0 : Int)) ” &&
  “ (root_pre ≠ (0 : Int)) ”
  &&  ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((root_pre # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((root_pre # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((root_pre # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((root_pre # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((root_pre # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)

noncomputable def balance_safety_wit_1 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) ,
  ((( &( "rh" ) )) # Int |->_)
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_2 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) ,
  ((( &( "lh" ) )) # Int |->_)
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_3 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) ,
  (store_tree_shape p_pre_v)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_4 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval >= (0 : Int))) (PreH2 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_5 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval <= (0 : Int))) (PreH2 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_6 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (PreH1 : (retval = x)) (PreH2 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_7 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (retval : Int) (PreH1 : (retval > 1)) (PreH2 : (retval = (0 : Int))) ,
  (store_tree_shape p_pre_v)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_8 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval > 1)) (PreH2 : (retval <= (0 : Int))) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_9 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= (0 : Int))) (PreH6 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH7 : (l ≠ (0 : Int))) (PreH8 : (retval > 1)) (PreH9 : (retval >= (0 : Int))) (PreH10 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_10 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (l ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (retval > 1)) (PreH10 : (retval >= (0 : Int))) (PreH11 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_11 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (l ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (retval > 1)) (PreH10 : (retval >= (0 : Int))) (PreH11 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_12 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 = x)) (PreH2 : (l ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (retval > 1)) (PreH10 : (retval >= (0 : Int))) (PreH11 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_13 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= (0 : Int))) (PreH6 : (h_3 <= 255)) (PreH7 : (h_3 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (l ≠ (0 : Int))) (PreH12 : (retval > 1)) (PreH13 : (retval = x)) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_14 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (l ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_15 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (l ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_16 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 = x_2)) (PreH2 : (l ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_17 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (retval > 1)) (PreH10 : (retval >= (0 : Int))) (PreH11 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_18 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_19 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_20 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_21 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l ≠ (0 : Int))) (PreH9 : (retval > 1)) (PreH10 : (retval >= (0 : Int))) (PreH11 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_22 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_23 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_24 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 = x)) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_25 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_26 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_27 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_28 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 = x_2)) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_29 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_30 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_31 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_32 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_33 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval = x)) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def balance_safety_wit_34 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval <= (0 : Int))) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def balance_safety_wit_35 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval >= (0 : Int))) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def balance_safety_wit_36 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval = (0 : Int))) ,
  (store_tree_shape p_pre_v)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def balance_safety_wit_37 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval = (0 : Int))) ,
  (store_tree_shape p_pre_v)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_38 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval >= (0 : Int))) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_39 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval <= (0 : Int))) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_40 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (PreH1 : (retval <= 1)) (PreH2 : (retval = x)) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_non_empty_tree r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def balance_safety_wit_41 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (retval : Int) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = (0 : Int))) ,
  (store_tree_shape p_pre_v)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_42 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval >= (0 : Int))) (PreH4 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_43 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= (0 : Int))) (PreH6 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH7 : (r ≠ (0 : Int))) (PreH8 : (retval < (-1))) (PreH9 : (retval <= 1)) (PreH10 : (retval <= (0 : Int))) (PreH11 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_44 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (r ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_45 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (r ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_46 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 = x)) (PreH2 : (r ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_47 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 = (0 : Int))) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= (0 : Int))) (PreH6 : (h_3 <= 255)) (PreH7 : (h_3 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (l ≠ (0 : Int))) (PreH12 : (retval < (-1))) (PreH13 : (retval <= 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_48 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (r ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_49 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (r ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_50 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 = x_2)) (PreH2 : (r ≠ (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_51 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_52 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_53 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_54 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_55 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_56 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_57 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_58 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 = x)) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_59 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 = (0 : Int))) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= (0 : Int))) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l ≠ (0 : Int))) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_60 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_61 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_62 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 = x_2)) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def balance_safety_wit_63 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_64 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_65 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_safety_wit_66 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ False ”

noncomputable def balance_return_wit_1 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (store_tree_shape r)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_2 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_3 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_4 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = x)) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_5 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (store_tree_shape r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_6 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_7 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_8 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 <= (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = x_2)) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_9 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (r : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (l : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (retval_2 > (0 : Int))) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (retval_2 >= (0 : Int))) (PreH7 : (r ≠ (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (r ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval <= (0 : Int))) (PreH17 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_10 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (r : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (l : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (tr_2 : tree) (h_4 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_3 : Int) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (r_2 ≠ (0 : Int))) (PreH8 : (retval_2 > (0 : Int))) (PreH9 : (retval_2 >= (0 : Int))) (PreH10 : (retval_2 = x)) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (h <= 255)) (PreH13 : (h >= (0 : Int))) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= (0 : Int))) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (r ≠ (0 : Int))) (PreH18 : (retval < (-1))) (PreH19 : (retval <= 1)) (PreH20 : (retval <= (0 : Int))) (PreH21 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_11 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (l_2 : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = l_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (retval_2 > (0 : Int))) (PreH5 : (retval_2 >= (0 : Int))) (PreH6 : (retval_2 >= (0 : Int))) (PreH7 : (r ≠ (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (h_3 <= 255)) (PreH13 : (h_3 >= (0 : Int))) (PreH14 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH15 : (r ≠ (0 : Int))) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (l ≠ (0 : Int))) (PreH18 : (retval < (-1))) (PreH19 : (retval <= 1)) (PreH20 : (retval = x)) (PreH21 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l_2)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_12 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (l_2 : Int) (r_2 : Int) (x_2 : Int) (retval_2 : Int) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (retval_3 : Int) (PreH1 : (retval_3 = l_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= (0 : Int))) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (r_2 ≠ (0 : Int))) (PreH8 : (retval_2 > (0 : Int))) (PreH9 : (retval_2 >= (0 : Int))) (PreH10 : (retval_2 = x_2)) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (h <= 255)) (PreH13 : (h >= (0 : Int))) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= (0 : Int))) (PreH16 : (h_3 <= 255)) (PreH17 : (h_3 >= (0 : Int))) (PreH18 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH19 : (r ≠ (0 : Int))) (PreH20 : (tr = (make_tree (tr1) (tr2)))) (PreH21 : (l ≠ (0 : Int))) (PreH22 : (retval < (-1))) (PreH23 : (retval <= 1)) (PreH24 : (retval = x)) (PreH25 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l_2)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_13 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (r : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (r_2 : Int) (retval_2 : Int) (tr_2 : tree) (h_4 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_3 : Int) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (r_2 ≠ (0 : Int))) (PreH8 : (retval_2 < (0 : Int))) (PreH9 : (retval_2 <= (0 : Int))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (h <= 255)) (PreH12 : (h >= (0 : Int))) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= (0 : Int))) (PreH15 : (tr = (make_tree (tr1) (tr2)))) (PreH16 : (r ≠ (0 : Int))) (PreH17 : (retval < (-1))) (PreH18 : (retval <= 1)) (PreH19 : (retval <= (0 : Int))) (PreH20 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_14 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (r : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (l : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (tr_2 : tree) (h_4 : Int) (tr1_2 : tree) (tr2_2 : tree) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (retval_3 : Int) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (h_5 <= 255)) (PreH7 : (h_5 >= (0 : Int))) (PreH8 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH9 : (r_2 ≠ (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (l ≠ (0 : Int))) (PreH12 : (retval_2 < (0 : Int))) (PreH13 : (retval_2 = x)) (PreH14 : (r ≠ (0 : Int))) (PreH15 : (h <= 255)) (PreH16 : (h >= (0 : Int))) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= (0 : Int))) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (r ≠ (0 : Int))) (PreH21 : (retval < (-1))) (PreH22 : (retval <= 1)) (PreH23 : (retval <= (0 : Int))) (PreH24 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_15 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (r_2 : Int) (retval_2 : Int) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (retval_3 : Int) (PreH1 : (retval_3 = r)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= (0 : Int))) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (r_2 ≠ (0 : Int))) (PreH8 : (retval_2 < (0 : Int))) (PreH9 : (retval_2 <= (0 : Int))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (h <= 255)) (PreH12 : (h >= (0 : Int))) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= (0 : Int))) (PreH15 : (h_3 <= 255)) (PreH16 : (h_3 >= (0 : Int))) (PreH17 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH18 : (r ≠ (0 : Int))) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (l ≠ (0 : Int))) (PreH21 : (retval < (-1))) (PreH22 : (retval <= 1)) (PreH23 : (retval = x)) (PreH24 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_16 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (l_2 : Int) (r_2 : Int) (x_2 : Int) (retval_2 : Int) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (tr_4 : tree) (h_6 : Int) (tr1_4 : tree) (tr2_4 : tree) (retval_3 : Int) (PreH1 : (retval_3 = r)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= (0 : Int))) (PreH6 : (h_6 <= 255)) (PreH7 : (h_6 >= (0 : Int))) (PreH8 : (tr_4 = (make_tree (tr1_4) (tr2_4)))) (PreH9 : (r_2 ≠ (0 : Int))) (PreH10 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH11 : (l_2 ≠ (0 : Int))) (PreH12 : (retval_2 < (0 : Int))) (PreH13 : (retval_2 = x_2)) (PreH14 : (r ≠ (0 : Int))) (PreH15 : (h <= 255)) (PreH16 : (h >= (0 : Int))) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= (0 : Int))) (PreH19 : (h_3 <= 255)) (PreH20 : (h_3 >= (0 : Int))) (PreH21 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH22 : (r ≠ (0 : Int))) (PreH23 : (tr = (make_tree (tr1) (tr2)))) (PreH24 : (l ≠ (0 : Int))) (PreH25 : (retval < (-1))) (PreH26 : (retval <= 1)) (PreH27 : (retval = x)) (PreH28 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_17 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_18 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_19 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_20 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = x)) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_21 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (store_tree_shape l)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_22 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_23 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_24 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 >= (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = x_2)) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v_2 k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_25 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (r : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (retval_2 < (0 : Int))) (PreH5 : (retval_2 <= (0 : Int))) (PreH6 : (retval_2 <= (0 : Int))) (PreH7 : (l ≠ (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval >= (0 : Int))) (PreH16 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_26 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (l_2 : Int) (r : Int) (x : Int) (retval_2 : Int) (tr_2 : tree) (h_4 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_3 : Int) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l_2 ≠ (0 : Int))) (PreH8 : (retval_2 < (0 : Int))) (PreH9 : (retval_2 <= (0 : Int))) (PreH10 : (retval_2 = x)) (PreH11 : (l ≠ (0 : Int))) (PreH12 : (h <= 255)) (PreH13 : (h >= (0 : Int))) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= (0 : Int))) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (l ≠ (0 : Int))) (PreH18 : (retval > 1)) (PreH19 : (retval >= (0 : Int))) (PreH20 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_27 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (r_2 : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = r_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (retval_2 < (0 : Int))) (PreH5 : (retval_2 <= (0 : Int))) (PreH6 : (retval_2 <= (0 : Int))) (PreH7 : (l ≠ (0 : Int))) (PreH8 : (h <= 255)) (PreH9 : (h >= (0 : Int))) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= (0 : Int))) (PreH12 : (h_3 <= 255)) (PreH13 : (h_3 >= (0 : Int))) (PreH14 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH15 : (r ≠ (0 : Int))) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (l ≠ (0 : Int))) (PreH18 : (retval > 1)) (PreH19 : (retval = x)) (PreH20 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r_2)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_28 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (l_2 : Int) (r_2 : Int) (x_2 : Int) (retval_2 : Int) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (retval_3 : Int) (PreH1 : (retval_3 = r_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= (0 : Int))) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (l_2 ≠ (0 : Int))) (PreH8 : (retval_2 < (0 : Int))) (PreH9 : (retval_2 <= (0 : Int))) (PreH10 : (retval_2 = x_2)) (PreH11 : (l ≠ (0 : Int))) (PreH12 : (h <= 255)) (PreH13 : (h >= (0 : Int))) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= (0 : Int))) (PreH16 : (h_3 <= 255)) (PreH17 : (h_3 >= (0 : Int))) (PreH18 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH19 : (r ≠ (0 : Int))) (PreH20 : (tr = (make_tree (tr1) (tr2)))) (PreH21 : (l ≠ (0 : Int))) (PreH22 : (retval > 1)) (PreH23 : (retval = x)) (PreH24 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree r_2)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_29 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (l_2 : Int) (retval_2 : Int) (tr_2 : tree) (h_4 : Int) (tr1_2 : tree) (tr2_2 : tree) (retval_3 : Int) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l_2 ≠ (0 : Int))) (PreH8 : (retval_2 > (0 : Int))) (PreH9 : (retval_2 >= (0 : Int))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (h <= 255)) (PreH12 : (h >= (0 : Int))) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= (0 : Int))) (PreH15 : (tr = (make_tree (tr1) (tr2)))) (PreH16 : (l ≠ (0 : Int))) (PreH17 : (retval > 1)) (PreH18 : (retval >= (0 : Int))) (PreH19 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_30 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (h_3 : Int) (l_2 : Int) (r : Int) (x : Int) (retval_2 : Int) (tr_2 : tree) (h_4 : Int) (tr1_2 : tree) (tr2_2 : tree) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (retval_3 : Int) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= (0 : Int))) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= (0 : Int))) (PreH6 : (h_5 <= 255)) (PreH7 : (h_5 >= (0 : Int))) (PreH8 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (l_2 ≠ (0 : Int))) (PreH12 : (retval_2 > (0 : Int))) (PreH13 : (retval_2 = x)) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (h <= 255)) (PreH16 : (h >= (0 : Int))) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= (0 : Int))) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (l ≠ (0 : Int))) (PreH21 : (retval > 1)) (PreH22 : (retval >= (0 : Int))) (PreH23 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_31 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (l_2 : Int) (retval_2 : Int) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (retval_3 : Int) (PreH1 : (retval_3 = l)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= (0 : Int))) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (l_2 ≠ (0 : Int))) (PreH8 : (retval_2 > (0 : Int))) (PreH9 : (retval_2 >= (0 : Int))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (h <= 255)) (PreH12 : (h >= (0 : Int))) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= (0 : Int))) (PreH15 : (h_3 <= 255)) (PreH16 : (h_3 >= (0 : Int))) (PreH17 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH18 : (r ≠ (0 : Int))) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (l ≠ (0 : Int))) (PreH21 : (retval > 1)) (PreH22 : (retval = x)) (PreH23 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_32 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (h_4 : Int) (l_2 : Int) (r_2 : Int) (x_2 : Int) (retval_2 : Int) (tr_3 : tree) (h_5 : Int) (tr1_3 : tree) (tr2_3 : tree) (tr_4 : tree) (h_6 : Int) (tr1_4 : tree) (tr2_4 : tree) (retval_3 : Int) (PreH1 : (retval_3 = l)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= (0 : Int))) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= (0 : Int))) (PreH6 : (h_6 <= 255)) (PreH7 : (h_6 >= (0 : Int))) (PreH8 : (tr_4 = (make_tree (tr1_4) (tr2_4)))) (PreH9 : (r_2 ≠ (0 : Int))) (PreH10 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH11 : (l_2 ≠ (0 : Int))) (PreH12 : (retval_2 > (0 : Int))) (PreH13 : (retval_2 = x_2)) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (h <= 255)) (PreH16 : (h >= (0 : Int))) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= (0 : Int))) (PreH19 : (h_3 <= 255)) (PreH20 : (h_3 >= (0 : Int))) (PreH21 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH22 : (r ≠ (0 : Int))) (PreH23 : (tr = (make_tree (tr1) (tr2)))) (PreH24 : (l ≠ (0 : Int))) (PreH25 : (retval > 1)) (PreH26 : (retval = x)) (PreH27 : (p_pre_v_2 ≠ (0 : Int))) ,
  (store_non_empty_tree l)
  ** ((p_pre) # Ptr |-> (retval_3))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_33 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (retval : Int) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = (0 : Int))) ,
  (store_tree_shape p_pre_v_2)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_34 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval >= (0 : Int))) (PreH4 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_35 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval <= (0 : Int))) (PreH4 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_return_wit_36 : Prop :=
  forall (p_pre : Int) (p_pre_v_2 : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = x)) (PreH4 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (store_non_empty_tree l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def balance_partial_solve_wit_1 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) ,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)
|--
  (store_tree_shape p_pre_v)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_2 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval > 1)) (PreH2 : (retval >= (0 : Int))) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_2 : tree, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval >= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_3 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l ≠ (0 : Int))) (PreH7 : (retval > 1)) (PreH8 : (retval >= (0 : Int))) (PreH9 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval >= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (store_tree_shape l)
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_4 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (PreH1 : (retval > 1)) (PreH2 : (retval = x)) (PreH3 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_3 : Int, EX l_3 : Int, EX h_3 : Int, EX v_3 : Int, EX k_3 : Int, EX tr_2 : tree, EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_2)
  ** (store_tree l_3 tr1_2)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_5 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_3 : Int) (v_3 : Int) (h_2 : Int) (l_3 : Int) (r_3 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (h_3 <= 255)) (PreH6 : (h_3 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval = x)) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node l k_3 v_3 h_2 l_3 r_3)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** (store_tree r_3 tr2)
  ** (store_tree l_3 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (store_tree_shape l)
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_6_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_6_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_4 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l_2 ≠ (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval >= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_6 : Prop := balance_partial_solve_wit_6_pure -> balance_partial_solve_wit_6_aux

noncomputable def balance_partial_solve_wit_7_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 = x)) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_7_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 = x)) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l ≠ (0 : Int))) (PreH10 : (retval > 1)) (PreH11 : (retval >= (0 : Int))) (PreH12 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_4 : tree, EX tr2_2 : tree, EX tr1_2 : tree, EX h_4 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (tr_4 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r_2 ≠ (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l_2 ≠ (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 = x) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval >= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_7 : Prop := balance_partial_solve_wit_7_pure -> balance_partial_solve_wit_7_aux

noncomputable def balance_partial_solve_wit_8_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_8_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (l_3 ≠ (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_8 : Prop := balance_partial_solve_wit_8_pure -> balance_partial_solve_wit_8_aux

noncomputable def balance_partial_solve_wit_9_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 = x_2)) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_9_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 = x_2)) (PreH3 : (l ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_4 : tree, EX tr1_4 : tree, EX h_6 : Int, EX tr_4 : tree, EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (h_6 <= 255) ” &&
  “ (h_6 >= (0 : Int)) ” &&
  “ (tr_4 = (make_tree (tr1_4) (tr2_4))) ” &&
  “ (r_3 ≠ (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (l_3 ≠ (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 = x_2) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_tree_shape r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_9 : Prop := balance_partial_solve_wit_9_pure -> balance_partial_solve_wit_9_aux

noncomputable def balance_partial_solve_wit_10_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_10_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval >= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape r)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_10 : Prop := balance_partial_solve_wit_10_pure -> balance_partial_solve_wit_10_aux

noncomputable def balance_partial_solve_wit_11_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = x)) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_11_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = x)) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval > 1)) (PreH12 : (retval >= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree r tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_4 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l_2 ≠ (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (retval_2 = x) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval >= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape r)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_11 : Prop := balance_partial_solve_wit_11_pure -> balance_partial_solve_wit_11_aux

noncomputable def balance_partial_solve_wit_12_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_12_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 <= (0 : Int))) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape r)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_12 : Prop := balance_partial_solve_wit_12_pure -> balance_partial_solve_wit_12_aux

noncomputable def balance_partial_solve_wit_13_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = x_2)) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((( &( "lbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_13_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (retval_2 = x_2)) (PreH4 : (l ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2_2)
  ** (store_tree l_2 tr1_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (l_3 ≠ (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (retval_2 = x_2) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval > 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node l k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape r)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_13 : Prop := balance_partial_solve_wit_13_pure -> balance_partial_solve_wit_13_aux

noncomputable def balance_partial_solve_wit_14 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval <= (0 : Int))) (PreH4 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr_2 : tree, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_15 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r ≠ (0 : Int))) (PreH7 : (retval < (-1))) (PreH8 : (retval <= 1)) (PreH9 : (retval <= (0 : Int))) (PreH10 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (store_tree_shape r)
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_16 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = x)) (PreH4 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_non_empty_tree l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX r_3 : Int, EX l_3 : Int, EX h_3 : Int, EX v_3 : Int, EX k_3 : Int, EX tr_2 : tree, EX tr2 : tree, EX tr1 : tree, EX r_2 : Int, EX l_2 : Int, EX h_2 : Int, EX v_2 : Int, EX k_2 : Int, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** ((&((r # "tree")  ->ₛ "rchild")) # Ptr |-> (r_3))
  ** ((&((r # "tree")  ->ₛ "lchild")) # Ptr |-> (l_3))
  ** ((&((r # "tree")  ->ₛ "height")) # UChar |-> (h_3))
  ** ((&((r # "tree")  ->ₛ "value")) # Int |-> (v_3))
  ** ((&((r # "tree")  ->ₛ "key")) # Int |-> (k_3))
  ** (store_tree r_3 tr2_2)
  ** (store_tree l_3 tr1_2)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_17 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (k_3 : Int) (v_3 : Int) (h_3 : Int) (l_3 : Int) (r_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (PreH1 : (h <= 255)) (PreH2 : (h >= (0 : Int))) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= (0 : Int))) (PreH5 : (h_3 <= 255)) (PreH6 : (h_3 >= (0 : Int))) (PreH7 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (r ≠ (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (l ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval = x)) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3)
  ** (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (store_tree r_3 tr2_2)
  ** (store_tree l_3 tr1_2)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (store_tree_shape r)
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((l # "tree")  ->ₛ "rchild")) # Ptr |-> (r_2))
  ** ((&((l # "tree")  ->ₛ "lchild")) # Ptr |-> (l_2))
  ** ((&((l # "tree")  ->ₛ "height")) # UChar |-> (h_2))
  ** ((&((l # "tree")  ->ₛ "value")) # Int |-> (v_2))
  ** ((&((l # "tree")  ->ₛ "key")) # Int |-> (k_2))
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_18_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_18_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_4 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r_2 ≠ (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_18 : Prop := balance_partial_solve_wit_18_pure -> balance_partial_solve_wit_18_aux

noncomputable def balance_partial_solve_wit_19_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 = x)) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_19_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 = x)) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r ≠ (0 : Int))) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= (0 : Int))) (PreH13 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_4 : tree, EX tr2_2 : tree, EX tr1_2 : tree, EX h_4 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (tr_4 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r_2 ≠ (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (l_2 ≠ (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 = x) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_19 : Prop := balance_partial_solve_wit_19_pure -> balance_partial_solve_wit_19_aux

noncomputable def balance_partial_solve_wit_20_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_20_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 <= (0 : Int))) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r_3 ≠ (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 <= (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_20 : Prop := balance_partial_solve_wit_20_pure -> balance_partial_solve_wit_20_aux

noncomputable def balance_partial_solve_wit_21_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 = x_2)) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_21_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 < (0 : Int))) (PreH2 : (retval_2 = x_2)) (PreH3 : (r ≠ (0 : Int))) (PreH4 : (h <= 255)) (PreH5 : (h >= (0 : Int))) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= (0 : Int))) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= (0 : Int))) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r ≠ (0 : Int))) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l ≠ (0 : Int))) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_4 : tree, EX tr1_4 : tree, EX h_6 : Int, EX tr_4 : tree, EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (h_6 <= 255) ” &&
  “ (h_6 >= (0 : Int)) ” &&
  “ (tr_4 = (make_tree (tr1_4) (tr2_4))) ” &&
  “ (r_3 ≠ (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (l_3 ≠ (0 : Int)) ” &&
  “ (retval_2 < (0 : Int)) ” &&
  “ (retval_2 = x_2) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (store_tree_shape l)
  ** (store_non_empty_tree r)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_21 : Prop := balance_partial_solve_wit_21_pure -> balance_partial_solve_wit_21_aux

noncomputable def balance_partial_solve_wit_22_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_22_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_22 : Prop := balance_partial_solve_wit_22_pure -> balance_partial_solve_wit_22_aux

noncomputable def balance_partial_solve_wit_23_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = x)) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_23_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (retval : Int) (tr : tree) (tr_2 : tree) (h_2 : Int) (tr1 : tree) (tr2 : tree) (k_2 : Int) (v_2 : Int) (h_3 : Int) (l_2 : Int) (r_2 : Int) (x : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = x)) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r ≠ (0 : Int))) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= (0 : Int))) (PreH14 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_non_empty_tree l_2)
  ** (store_non_empty_tree r_2)
  ** (store_tree l tr)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_4 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r_2 ≠ (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (retval_2 = x) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1) (tr2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_2 v_2 h_3 l_2 r_2)
  ** (store_tree_shape l)
  ** (store_non_empty_tree l_2)
  ** (store_tree_shape r_2)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_23 : Prop := balance_partial_solve_wit_23_pure -> balance_partial_solve_wit_23_aux

noncomputable def balance_partial_solve_wit_24_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_24_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 >= (0 : Int))) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_24 : Prop := balance_partial_solve_wit_24_pure -> balance_partial_solve_wit_24_aux

noncomputable def balance_partial_solve_wit_25_pure : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = x_2)) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((( &( "rbf" ) )) # Int |-> (retval_2))
  ** ((( &( "bf" ) )) # Int |-> (retval))
  ** ((( &( "rh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "lh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ”

noncomputable def balance_partial_solve_wit_25_aux : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (x : Int) (retval : Int) (tr : tree) (k_2 : Int) (v_2 : Int) (h_2 : Int) (l_2 : Int) (r_2 : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_3 : Int) (tr1_2 : tree) (tr2_2 : tree) (k_3 : Int) (v_3 : Int) (h_4 : Int) (l_3 : Int) (r_3 : Int) (x_2 : Int) (retval_2 : Int) (PreH1 : (retval_2 > (0 : Int))) (PreH2 : (retval_2 >= (0 : Int))) (PreH3 : (retval_2 = x_2)) (PreH4 : (r ≠ (0 : Int))) (PreH5 : (h <= 255)) (PreH6 : (h >= (0 : Int))) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= (0 : Int))) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= (0 : Int))) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r ≠ (0 : Int))) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l ≠ (0 : Int))) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2)
  ** (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_non_empty_tree l_3)
  ** (store_non_empty_tree r_3)
  ** (store_tree r_2 tr2)
  ** (store_tree l_2 tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_3 : tree, EX tr1_3 : tree, EX h_5 : Int, EX tr_3 : tree,
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h_4 <= 255) ” &&
  “ (h_4 >= (0 : Int)) ” &&
  “ (h_5 <= 255) ” &&
  “ (h_5 >= (0 : Int)) ” &&
  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” &&
  “ (r_3 ≠ (0 : Int)) ” &&
  “ (retval_2 > (0 : Int)) ” &&
  “ (retval_2 >= (0 : Int)) ” &&
  “ (retval_2 = x_2) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (h_3 <= 255) ” &&
  “ (h_3 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (r ≠ (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (l ≠ (0 : Int)) ” &&
  “ (retval < (-1)) ” &&
  “ (retval <= 1) ” &&
  “ (retval = x) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (single_tree_node p_pre_v k v h l r)
  ** (single_tree_node r k_3 v_3 h_4 l_3 r_3)
  ** (store_tree_shape l)
  ** (store_non_empty_tree l_3)
  ** (store_tree_shape r_3)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def balance_partial_solve_wit_25 : Prop := balance_partial_solve_wit_25_pure -> balance_partial_solve_wit_25_aux

noncomputable def insert_safety_wit_1 : Prop :=
  forall (value_pre : Int) (key_pre : Int) (p_pre : Int) (p_pre_v : Int) ,
  ((( &( "root" ) )) # Ptr |-> (p_pre_v))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "key" ) )) # Int |-> (key_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_2 : Prop :=
  forall (value_pre : Int) (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v = (0 : Int))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (key_pre))
  ** ((&((retval # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "lchild")) # Ptr |->_)
  ** ((&((retval # "tree")  ->ₛ "rchild")) # Ptr |->_)
  ** ((( &( "root" ) )) # Ptr |-> (retval))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "key" ) )) # Int |-> (key_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_3 : Prop :=
  forall (value_pre : Int) (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v = (0 : Int))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (key_pre))
  ** ((&((retval # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "lchild")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "rchild")) # Ptr |->_)
  ** ((( &( "root" ) )) # Ptr |-> (retval))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "key" ) )) # Int |-> (key_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def insert_safety_wit_4 : Prop :=
  forall (value_pre : Int) (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v = (0 : Int))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (key_pre))
  ** ((&((retval # "tree")  ->ₛ "height")) # UChar |->_)
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "lchild")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "rchild")) # Ptr |-> ((0 : Int)))
  ** ((( &( "root" ) )) # Ptr |-> (retval))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "key" ) )) # Int |-> (key_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def insert_return_wit_1 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v_2 : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (key_pre <= k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v_2 ≠ (0 : Int))) ,
  (single_tree_node p_pre_v_2 k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v_2))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def insert_return_wit_2 : Prop :=
  forall (value_pre : Int) (key_pre : Int) (p_pre : Int) (p_pre_v_2 : Int) (tr : tree) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v_2 = (0 : Int))) ,
  ((&((retval # "tree")  ->ₛ "key")) # Int |-> (key_pre))
  ** ((&((retval # "tree")  ->ₛ "height")) # UChar |-> (1))
  ** ((&((retval # "tree")  ->ₛ "value")) # Int |-> (value_pre))
  ** ((&((retval # "tree")  ->ₛ "lchild")) # Ptr |-> ((0 : Int)))
  ** ((&((retval # "tree")  ->ₛ "rchild")) # Ptr |-> ((0 : Int)))
  ** ((p_pre) # Ptr |-> (retval))
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def insert_return_wit_3 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v_2 : Int) (tr : tree) (k : Int) (h : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (p_callee_v : Int) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (p_pre_v_2 ≠ (0 : Int))) (PreH5 : (key_pre < k)) (PreH6 : (h <= 255)) (PreH7 : (h >= (0 : Int))) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (p_pre_v_2 ≠ (0 : Int))) ,
  ((p_pre) # Ptr |-> (p_callee_v))
  ** (store_tree_shape p_callee_v)
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def insert_return_wit_4 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v_2 : Int) (tr : tree) (k : Int) (h : Int) (tr1 : tree) (tr2 : tree) (tr_2 : tree) (h_2 : Int) (tr1_2 : tree) (tr2_2 : tree) (p_callee_v : Int) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= (0 : Int))) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (p_pre_v_2 ≠ (0 : Int))) (PreH5 : (key_pre > k)) (PreH6 : (key_pre >= k)) (PreH7 : (h <= 255)) (PreH8 : (h >= (0 : Int))) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (p_pre_v_2 ≠ (0 : Int))) ,
  ((p_pre) # Ptr |-> (p_callee_v))
  ** (store_tree_shape p_callee_v)
|--
  EX p_pre_v : Int,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def insert_partial_solve_wit_1 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (PreH1 : (p_pre_v = (0 : Int))) ,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)
|--
  EX tr : tree,
  “ (tr = empty) ” &&
  “ (p_pre_v = (0 : Int)) ”
  &&  ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_2 : Prop :=
  forall (p_pre : Int) (p_pre_v : Int) (PreH1 : (p_pre_v ≠ (0 : Int))) ,
  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)
|--
  EX k : Int, EX tr2 : tree, EX tr1 : tree, EX r : Int, EX l : Int, EX h : Int, EX v : Int, EX tr : tree,
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_3 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (key_pre < k)) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (key_pre < k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** (store_tree_shape l)
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree r tr2)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_4 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (key_pre >= k)) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (key_pre >= k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_5 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (r : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (key_pre > k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l r)
  ** (store_tree r tr2)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (key_pre > k) ” &&
  “ (key_pre >= k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((&((p_pre_v # "tree")  ->ₛ "rchild")) # Ptr |-> (r))
  ** (store_tree_shape r)
  ** ((&((p_pre_v # "tree")  ->ₛ "lchild")) # Ptr |-> (l))
  ** ((&((p_pre_v # "tree")  ->ₛ "height")) # UChar |-> (h))
  ** ((&((p_pre_v # "tree")  ->ₛ "value")) # Int |-> (v))
  ** ((&((p_pre_v # "tree")  ->ₛ "key")) # Int |-> (k))
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_6 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (r : Int) (tr1 : tree) (tr2 : tree) (p_callee_v : Int) (PreH1 : (key_pre < k)) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h p_callee_v r)
  ** (store_tree_shape p_callee_v)
  ** (store_tree r tr2)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (key_pre < k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (store_non_empty_tree p_pre_v)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_7 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (v : Int) (h : Int) (l : Int) (tr1 : tree) (tr2 : tree) (p_callee_v : Int) (PreH1 : (key_pre > k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v ≠ (0 : Int))) ,
  (single_tree_node p_pre_v k v h l p_callee_v)
  ** (store_tree_shape p_callee_v)
  ** (store_tree l tr1)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  “ (key_pre > k) ” &&
  “ (key_pre >= k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  (store_non_empty_tree p_pre_v)
  ** ((p_pre) # Ptr |-> (p_pre_v))

noncomputable def insert_partial_solve_wit_8 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (h : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (key_pre < k)) (PreH2 : (h <= 255)) (PreH3 : (h >= (0 : Int))) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v ≠ (0 : Int))) ,
  (store_non_empty_tree p_pre_v)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_2 : Int, EX tr_2 : tree,
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (key_pre < k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)

noncomputable def insert_partial_solve_wit_9 : Prop :=
  forall (key_pre : Int) (p_pre : Int) (p_pre_v : Int) (tr : tree) (k : Int) (h : Int) (tr1 : tree) (tr2 : tree) (PreH1 : (key_pre > k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= (0 : Int))) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v ≠ (0 : Int))) ,
  (store_non_empty_tree p_pre_v)
  ** ((p_pre) # Ptr |-> (p_pre_v))
|--
  EX tr2_2 : tree, EX tr1_2 : tree, EX h_2 : Int, EX tr_2 : tree,
  “ (h_2 <= 255) ” &&
  “ (h_2 >= (0 : Int)) ” &&
  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ” &&
  “ (key_pre > k) ” &&
  “ (key_pre >= k) ” &&
  “ (h <= 255) ” &&
  “ (h >= (0 : Int)) ” &&
  “ (tr = (make_tree (tr1) (tr2))) ” &&
  “ (p_pre_v ≠ (0 : Int)) ”
  &&  ((p_pre) # Ptr |-> (p_pre_v))
  ** (store_tree_shape p_pre_v)


structure VC_Correct : Type where
  proof_of_update_height_safety_wit_1 : update_height_safety_wit_1
  proof_of_update_height_safety_wit_2 : update_height_safety_wit_2
  proof_of_update_height_safety_wit_3 : update_height_safety_wit_3
  proof_of_update_height_safety_wit_4 : update_height_safety_wit_4
  proof_of_update_height_safety_wit_5 : update_height_safety_wit_5
  proof_of_update_height_safety_wit_6 : update_height_safety_wit_6
  proof_of_update_height_safety_wit_7 : update_height_safety_wit_7
  proof_of_update_height_safety_wit_8 : update_height_safety_wit_8
  proof_of_update_height_safety_wit_9 : update_height_safety_wit_9
  proof_of_update_height_safety_wit_10 : update_height_safety_wit_10
  proof_of_update_height_safety_wit_11 : update_height_safety_wit_11
  proof_of_update_height_safety_wit_12 : update_height_safety_wit_12
  proof_of_update_height_safety_wit_13 : update_height_safety_wit_13
  proof_of_update_height_safety_wit_14 : update_height_safety_wit_14
  proof_of_update_height_safety_wit_15 : update_height_safety_wit_15
  proof_of_update_height_safety_wit_16 : update_height_safety_wit_16
  proof_of_update_height_safety_wit_17 : update_height_safety_wit_17
  proof_of_update_height_safety_wit_18 : update_height_safety_wit_18
  proof_of_update_height_return_wit_1 : update_height_return_wit_1
  proof_of_update_height_return_wit_2 : update_height_return_wit_2
  proof_of_update_height_return_wit_3 : update_height_return_wit_3
  proof_of_update_height_return_wit_4 : update_height_return_wit_4
  proof_of_update_height_return_wit_5 : update_height_return_wit_5
  proof_of_update_height_return_wit_6 : update_height_return_wit_6
  proof_of_update_height_partial_solve_wit_1 : update_height_partial_solve_wit_1
  proof_of_update_height_partial_solve_wit_2 : update_height_partial_solve_wit_2
  proof_of_update_height_partial_solve_wit_3 : update_height_partial_solve_wit_3
  proof_of_update_height_partial_solve_wit_4 : update_height_partial_solve_wit_4
  proof_of_update_height_partial_solve_wit_5 : update_height_partial_solve_wit_5
  proof_of_update_height_partial_solve_wit_6 : update_height_partial_solve_wit_6
  proof_of_update_height_partial_solve_wit_7 : update_height_partial_solve_wit_7
  proof_of_update_height_partial_solve_wit_8 : update_height_partial_solve_wit_8
  proof_of_update_height_partial_solve_wit_9 : update_height_partial_solve_wit_9
  proof_of_update_height_partial_solve_wit_10 : update_height_partial_solve_wit_10
  proof_of_update_height_partial_solve_wit_11 : update_height_partial_solve_wit_11
  proof_of_update_height_partial_solve_wit_12 : update_height_partial_solve_wit_12
  proof_of_update_height_partial_solve_wit_13 : update_height_partial_solve_wit_13
  proof_of_update_height_partial_solve_wit_14 : update_height_partial_solve_wit_14
  proof_of_update_height_partial_solve_wit_15 : update_height_partial_solve_wit_15
  proof_of_rotateR_return_wit_1 : rotateR_return_wit_1
  proof_of_rotateR_partial_solve_wit_1 : rotateR_partial_solve_wit_1
  proof_of_rotateR_partial_solve_wit_2 : rotateR_partial_solve_wit_2
  proof_of_rotateR_partial_solve_wit_3 : rotateR_partial_solve_wit_3
  proof_of_rotateR_partial_solve_wit_4 : rotateR_partial_solve_wit_4
  proof_of_rotateR_partial_solve_wit_5 : rotateR_partial_solve_wit_5
  proof_of_rotateR_partial_solve_wit_6 : rotateR_partial_solve_wit_6
  proof_of_rotateL_return_wit_1 : rotateL_return_wit_1
  proof_of_rotateL_partial_solve_wit_1 : rotateL_partial_solve_wit_1
  proof_of_rotateL_partial_solve_wit_2 : rotateL_partial_solve_wit_2
  proof_of_rotateL_partial_solve_wit_3 : rotateL_partial_solve_wit_3
  proof_of_rotateL_partial_solve_wit_4 : rotateL_partial_solve_wit_4
  proof_of_rotateL_partial_solve_wit_5 : rotateL_partial_solve_wit_5
  proof_of_rotateL_partial_solve_wit_6 : rotateL_partial_solve_wit_6
  proof_of_rotateRL_return_wit_1 : rotateRL_return_wit_1
  proof_of_rotateRL_partial_solve_wit_1 : rotateRL_partial_solve_wit_1
  proof_of_rotateRL_partial_solve_wit_2_pure : rotateRL_partial_solve_wit_2_pure
  proof_of_rotateRL_partial_solve_wit_2 : rotateRL_partial_solve_wit_2
  proof_of_rotateRL_partial_solve_wit_3 : rotateRL_partial_solve_wit_3
  proof_of_rotateRL_partial_solve_wit_4_pure : rotateRL_partial_solve_wit_4_pure
  proof_of_rotateRL_partial_solve_wit_4 : rotateRL_partial_solve_wit_4
  proof_of_rotateLR_return_wit_1 : rotateLR_return_wit_1
  proof_of_rotateLR_partial_solve_wit_1 : rotateLR_partial_solve_wit_1
  proof_of_rotateLR_partial_solve_wit_2_pure : rotateLR_partial_solve_wit_2_pure
  proof_of_rotateLR_partial_solve_wit_2 : rotateLR_partial_solve_wit_2
  proof_of_rotateLR_partial_solve_wit_3 : rotateLR_partial_solve_wit_3
  proof_of_rotateLR_partial_solve_wit_4_pure : rotateLR_partial_solve_wit_4_pure
  proof_of_rotateLR_partial_solve_wit_4 : rotateLR_partial_solve_wit_4
  proof_of_balance_factor_safety_wit_1 : balance_factor_safety_wit_1
  proof_of_balance_factor_safety_wit_2 : balance_factor_safety_wit_2
  proof_of_balance_factor_safety_wit_3 : balance_factor_safety_wit_3
  proof_of_balance_factor_safety_wit_4 : balance_factor_safety_wit_4
  proof_of_balance_factor_safety_wit_5 : balance_factor_safety_wit_5
  proof_of_balance_factor_safety_wit_6 : balance_factor_safety_wit_6
  proof_of_balance_factor_safety_wit_7 : balance_factor_safety_wit_7
  proof_of_balance_factor_safety_wit_8 : balance_factor_safety_wit_8
  proof_of_balance_factor_safety_wit_9 : balance_factor_safety_wit_9
  proof_of_balance_factor_safety_wit_10 : balance_factor_safety_wit_10
  proof_of_balance_factor_safety_wit_11 : balance_factor_safety_wit_11
  proof_of_balance_factor_return_wit_1 : balance_factor_return_wit_1
  proof_of_balance_factor_return_wit_2 : balance_factor_return_wit_2
  proof_of_balance_factor_return_wit_3 : balance_factor_return_wit_3
  proof_of_balance_factor_return_wit_4 : balance_factor_return_wit_4
  proof_of_balance_factor_return_wit_5 : balance_factor_return_wit_5
  proof_of_balance_factor_partial_solve_wit_1 : balance_factor_partial_solve_wit_1
  proof_of_balance_factor_partial_solve_wit_2 : balance_factor_partial_solve_wit_2
  proof_of_balance_factor_partial_solve_wit_3 : balance_factor_partial_solve_wit_3
  proof_of_balance_factor_partial_solve_wit_4 : balance_factor_partial_solve_wit_4
  proof_of_balance_factor_partial_solve_wit_5 : balance_factor_partial_solve_wit_5
  proof_of_balance_factor_partial_solve_wit_6 : balance_factor_partial_solve_wit_6
  proof_of_balance_factor_partial_solve_wit_7 : balance_factor_partial_solve_wit_7
  proof_of_balance_factor_partial_solve_wit_8 : balance_factor_partial_solve_wit_8
  proof_of_balance_factor_partial_solve_wit_9 : balance_factor_partial_solve_wit_9
  proof_of_balance_safety_wit_1 : balance_safety_wit_1
  proof_of_balance_safety_wit_2 : balance_safety_wit_2
  proof_of_balance_safety_wit_3 : balance_safety_wit_3
  proof_of_balance_safety_wit_4 : balance_safety_wit_4
  proof_of_balance_safety_wit_5 : balance_safety_wit_5
  proof_of_balance_safety_wit_6 : balance_safety_wit_6
  proof_of_balance_safety_wit_7 : balance_safety_wit_7
  proof_of_balance_safety_wit_8 : balance_safety_wit_8
  proof_of_balance_safety_wit_9 : balance_safety_wit_9
  proof_of_balance_safety_wit_10 : balance_safety_wit_10
  proof_of_balance_safety_wit_11 : balance_safety_wit_11
  proof_of_balance_safety_wit_12 : balance_safety_wit_12
  proof_of_balance_safety_wit_13 : balance_safety_wit_13
  proof_of_balance_safety_wit_14 : balance_safety_wit_14
  proof_of_balance_safety_wit_15 : balance_safety_wit_15
  proof_of_balance_safety_wit_16 : balance_safety_wit_16
  proof_of_balance_safety_wit_17 : balance_safety_wit_17
  proof_of_balance_safety_wit_18 : balance_safety_wit_18
  proof_of_balance_safety_wit_19 : balance_safety_wit_19
  proof_of_balance_safety_wit_20 : balance_safety_wit_20
  proof_of_balance_safety_wit_21 : balance_safety_wit_21
  proof_of_balance_safety_wit_22 : balance_safety_wit_22
  proof_of_balance_safety_wit_23 : balance_safety_wit_23
  proof_of_balance_safety_wit_24 : balance_safety_wit_24
  proof_of_balance_safety_wit_25 : balance_safety_wit_25
  proof_of_balance_safety_wit_26 : balance_safety_wit_26
  proof_of_balance_safety_wit_27 : balance_safety_wit_27
  proof_of_balance_safety_wit_28 : balance_safety_wit_28
  proof_of_balance_safety_wit_29 : balance_safety_wit_29
  proof_of_balance_safety_wit_30 : balance_safety_wit_30
  proof_of_balance_safety_wit_31 : balance_safety_wit_31
  proof_of_balance_safety_wit_32 : balance_safety_wit_32
  proof_of_balance_safety_wit_33 : balance_safety_wit_33
  proof_of_balance_safety_wit_34 : balance_safety_wit_34
  proof_of_balance_safety_wit_35 : balance_safety_wit_35
  proof_of_balance_safety_wit_36 : balance_safety_wit_36
  proof_of_balance_safety_wit_37 : balance_safety_wit_37
  proof_of_balance_safety_wit_38 : balance_safety_wit_38
  proof_of_balance_safety_wit_39 : balance_safety_wit_39
  proof_of_balance_safety_wit_40 : balance_safety_wit_40
  proof_of_balance_safety_wit_41 : balance_safety_wit_41
  proof_of_balance_safety_wit_42 : balance_safety_wit_42
  proof_of_balance_safety_wit_43 : balance_safety_wit_43
  proof_of_balance_safety_wit_44 : balance_safety_wit_44
  proof_of_balance_safety_wit_45 : balance_safety_wit_45
  proof_of_balance_safety_wit_46 : balance_safety_wit_46
  proof_of_balance_safety_wit_47 : balance_safety_wit_47
  proof_of_balance_safety_wit_48 : balance_safety_wit_48
  proof_of_balance_safety_wit_49 : balance_safety_wit_49
  proof_of_balance_safety_wit_50 : balance_safety_wit_50
  proof_of_balance_safety_wit_51 : balance_safety_wit_51
  proof_of_balance_safety_wit_52 : balance_safety_wit_52
  proof_of_balance_safety_wit_53 : balance_safety_wit_53
  proof_of_balance_safety_wit_54 : balance_safety_wit_54
  proof_of_balance_safety_wit_55 : balance_safety_wit_55
  proof_of_balance_safety_wit_56 : balance_safety_wit_56
  proof_of_balance_safety_wit_57 : balance_safety_wit_57
  proof_of_balance_safety_wit_58 : balance_safety_wit_58
  proof_of_balance_safety_wit_59 : balance_safety_wit_59
  proof_of_balance_safety_wit_60 : balance_safety_wit_60
  proof_of_balance_safety_wit_61 : balance_safety_wit_61
  proof_of_balance_safety_wit_62 : balance_safety_wit_62
  proof_of_balance_safety_wit_63 : balance_safety_wit_63
  proof_of_balance_safety_wit_64 : balance_safety_wit_64
  proof_of_balance_safety_wit_65 : balance_safety_wit_65
  proof_of_balance_safety_wit_66 : balance_safety_wit_66
  proof_of_balance_return_wit_1 : balance_return_wit_1
  proof_of_balance_return_wit_2 : balance_return_wit_2
  proof_of_balance_return_wit_3 : balance_return_wit_3
  proof_of_balance_return_wit_4 : balance_return_wit_4
  proof_of_balance_return_wit_5 : balance_return_wit_5
  proof_of_balance_return_wit_6 : balance_return_wit_6
  proof_of_balance_return_wit_7 : balance_return_wit_7
  proof_of_balance_return_wit_8 : balance_return_wit_8
  proof_of_balance_return_wit_9 : balance_return_wit_9
  proof_of_balance_return_wit_10 : balance_return_wit_10
  proof_of_balance_return_wit_11 : balance_return_wit_11
  proof_of_balance_return_wit_12 : balance_return_wit_12
  proof_of_balance_return_wit_13 : balance_return_wit_13
  proof_of_balance_return_wit_14 : balance_return_wit_14
  proof_of_balance_return_wit_15 : balance_return_wit_15
  proof_of_balance_return_wit_16 : balance_return_wit_16
  proof_of_balance_return_wit_17 : balance_return_wit_17
  proof_of_balance_return_wit_18 : balance_return_wit_18
  proof_of_balance_return_wit_19 : balance_return_wit_19
  proof_of_balance_return_wit_20 : balance_return_wit_20
  proof_of_balance_return_wit_21 : balance_return_wit_21
  proof_of_balance_return_wit_22 : balance_return_wit_22
  proof_of_balance_return_wit_23 : balance_return_wit_23
  proof_of_balance_return_wit_24 : balance_return_wit_24
  proof_of_balance_return_wit_25 : balance_return_wit_25
  proof_of_balance_return_wit_26 : balance_return_wit_26
  proof_of_balance_return_wit_27 : balance_return_wit_27
  proof_of_balance_return_wit_28 : balance_return_wit_28
  proof_of_balance_return_wit_29 : balance_return_wit_29
  proof_of_balance_return_wit_30 : balance_return_wit_30
  proof_of_balance_return_wit_31 : balance_return_wit_31
  proof_of_balance_return_wit_32 : balance_return_wit_32
  proof_of_balance_return_wit_33 : balance_return_wit_33
  proof_of_balance_return_wit_34 : balance_return_wit_34
  proof_of_balance_return_wit_35 : balance_return_wit_35
  proof_of_balance_return_wit_36 : balance_return_wit_36
  proof_of_balance_partial_solve_wit_1 : balance_partial_solve_wit_1
  proof_of_balance_partial_solve_wit_2 : balance_partial_solve_wit_2
  proof_of_balance_partial_solve_wit_3 : balance_partial_solve_wit_3
  proof_of_balance_partial_solve_wit_4 : balance_partial_solve_wit_4
  proof_of_balance_partial_solve_wit_5 : balance_partial_solve_wit_5
  proof_of_balance_partial_solve_wit_6_pure : balance_partial_solve_wit_6_pure
  proof_of_balance_partial_solve_wit_6 : balance_partial_solve_wit_6
  proof_of_balance_partial_solve_wit_7_pure : balance_partial_solve_wit_7_pure
  proof_of_balance_partial_solve_wit_7 : balance_partial_solve_wit_7
  proof_of_balance_partial_solve_wit_8_pure : balance_partial_solve_wit_8_pure
  proof_of_balance_partial_solve_wit_8 : balance_partial_solve_wit_8
  proof_of_balance_partial_solve_wit_9_pure : balance_partial_solve_wit_9_pure
  proof_of_balance_partial_solve_wit_9 : balance_partial_solve_wit_9
  proof_of_balance_partial_solve_wit_10_pure : balance_partial_solve_wit_10_pure
  proof_of_balance_partial_solve_wit_10 : balance_partial_solve_wit_10
  proof_of_balance_partial_solve_wit_11_pure : balance_partial_solve_wit_11_pure
  proof_of_balance_partial_solve_wit_11 : balance_partial_solve_wit_11
  proof_of_balance_partial_solve_wit_12_pure : balance_partial_solve_wit_12_pure
  proof_of_balance_partial_solve_wit_12 : balance_partial_solve_wit_12
  proof_of_balance_partial_solve_wit_13_pure : balance_partial_solve_wit_13_pure
  proof_of_balance_partial_solve_wit_13 : balance_partial_solve_wit_13
  proof_of_balance_partial_solve_wit_14 : balance_partial_solve_wit_14
  proof_of_balance_partial_solve_wit_15 : balance_partial_solve_wit_15
  proof_of_balance_partial_solve_wit_16 : balance_partial_solve_wit_16
  proof_of_balance_partial_solve_wit_17 : balance_partial_solve_wit_17
  proof_of_balance_partial_solve_wit_18_pure : balance_partial_solve_wit_18_pure
  proof_of_balance_partial_solve_wit_18 : balance_partial_solve_wit_18
  proof_of_balance_partial_solve_wit_19_pure : balance_partial_solve_wit_19_pure
  proof_of_balance_partial_solve_wit_19 : balance_partial_solve_wit_19
  proof_of_balance_partial_solve_wit_20_pure : balance_partial_solve_wit_20_pure
  proof_of_balance_partial_solve_wit_20 : balance_partial_solve_wit_20
  proof_of_balance_partial_solve_wit_21_pure : balance_partial_solve_wit_21_pure
  proof_of_balance_partial_solve_wit_21 : balance_partial_solve_wit_21
  proof_of_balance_partial_solve_wit_22_pure : balance_partial_solve_wit_22_pure
  proof_of_balance_partial_solve_wit_22 : balance_partial_solve_wit_22
  proof_of_balance_partial_solve_wit_23_pure : balance_partial_solve_wit_23_pure
  proof_of_balance_partial_solve_wit_23 : balance_partial_solve_wit_23
  proof_of_balance_partial_solve_wit_24_pure : balance_partial_solve_wit_24_pure
  proof_of_balance_partial_solve_wit_24 : balance_partial_solve_wit_24
  proof_of_balance_partial_solve_wit_25_pure : balance_partial_solve_wit_25_pure
  proof_of_balance_partial_solve_wit_25 : balance_partial_solve_wit_25
  proof_of_insert_safety_wit_1 : insert_safety_wit_1
  proof_of_insert_safety_wit_2 : insert_safety_wit_2
  proof_of_insert_safety_wit_3 : insert_safety_wit_3
  proof_of_insert_safety_wit_4 : insert_safety_wit_4
  proof_of_insert_return_wit_1 : insert_return_wit_1
  proof_of_insert_return_wit_2 : insert_return_wit_2
  proof_of_insert_return_wit_3 : insert_return_wit_3
  proof_of_insert_return_wit_4 : insert_return_wit_4
  proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1
  proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2
  proof_of_insert_partial_solve_wit_3 : insert_partial_solve_wit_3
  proof_of_insert_partial_solve_wit_4 : insert_partial_solve_wit_4
  proof_of_insert_partial_solve_wit_5 : insert_partial_solve_wit_5
  proof_of_insert_partial_solve_wit_6 : insert_partial_solve_wit_6
  proof_of_insert_partial_solve_wit_7 : insert_partial_solve_wit_7
  proof_of_insert_partial_solve_wit_8 : insert_partial_solve_wit_8
  proof_of_insert_partial_solve_wit_9 : insert_partial_solve_wit_9

end SimpleC.EE.QCP_demos_LLM.generated.avl_insert_goal
