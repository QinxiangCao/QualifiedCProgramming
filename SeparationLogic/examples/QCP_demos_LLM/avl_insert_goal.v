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
Require Import SimpleC.EE.QCP_demos_LLM.avl_shape.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import avl_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import avl_strategy_proof.

(*----- Function update_height -----*)

Definition update_height_safety_wit_1 := 
forall (root_pre: Z) ,
  ((( &( "rh" ) )) # UChar  |->_)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
  **  (store_non_empty_tree root_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_height_safety_wit_2 := 
forall (root_pre: Z) ,
  ((( &( "lh" ) )) # UChar  |->_)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
  **  (store_non_empty_tree root_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_height_safety_wit_3 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (tr = (make_tree (tr1) (tr2)))) (PreH4 : (root_pre <> 0)) (PreH5 : (0 <= 255)) (PreH6 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_height_safety_wit_4 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre <> 0)) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_height_safety_wit_5 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (tr1 = empty)) (PreH2 : (l = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (root_pre <> 0)) (PreH7 : (0 <= 255)) (PreH8 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_height_safety_wit_6 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (0 > h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r <> 0)) (PreH6 : (tr1 = empty)) (PreH7 : (l = 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h_2)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ False ”
.

Definition update_height_safety_wit_7 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h <= 255)) (PreH7 : (h >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h l_2 r_2 )
  **  (single_tree_node root_pre k v h_2 l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h_3)
  **  ((( &( "lh" ) )) # UChar  |-> h)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((h + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h + 1 )) ”
.

Definition update_height_safety_wit_8 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h <= 255)) (PreH11 : (h >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h_3)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_height_safety_wit_9 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h > 0)) (PreH2 : (r = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l <> 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h l_2 r_2 )
  **  (single_tree_node root_pre k v h_2 l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((h + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h + 1 )) ”
.

Definition update_height_safety_wit_10 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 > 0)) (PreH2 : (r = 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l <> 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_height_safety_wit_11 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_3 <= h)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_3 <= 255)) (PreH7 : (h_3 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node root_pre k v h_2 l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h)
  **  ((( &( "lh" ) )) # UChar  |-> h_3)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((h + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h + 1 )) ”
.

Definition update_height_safety_wit_12 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 <= h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h <= 255)) (PreH11 : (h >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h_3)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_height_safety_wit_13 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (0 <= h)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r <> 0)) (PreH6 : (tr1 = empty)) (PreH7 : (l = 0)) (PreH8 : (h_2 <= 255)) (PreH9 : (h_2 >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node r k_2 v_2 h l_2 r_2 )
  **  (single_tree_node root_pre k v h_2 l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((h + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h + 1 )) ”
.

Definition update_height_safety_wit_14 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (0 <= h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r <> 0)) (PreH6 : (tr1 = empty)) (PreH7 : (l = 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h_2)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_height_safety_wit_15 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 0)) (PreH2 : (r = 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l <> 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition update_height_safety_wit_16 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 0)) (PreH2 : (r = 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l <> 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_height_safety_wit_17 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (r = 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre <> 0)) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition update_height_safety_wit_18 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (r = 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre <> 0)) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_height_return_wit_1 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h <= 255)) (PreH11 : (h >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_2 + 1 )) (8)) l r )
  **  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  (store_non_empty_tree root_pre )
.

Definition update_height_return_wit_2 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (tr2 = empty)) (PreH2 : (h_2 > 0)) (PreH3 : (r = 0)) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= 0)) (PreH6 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l <> 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_2 + 1 )) (8)) l r )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  (store_non_empty_tree root_pre )
.

Definition update_height_return_wit_3 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 <= h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h <= 255)) (PreH11 : (h >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_3 + 1 )) (8)) l r )
  **  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  (store_non_empty_tree root_pre )
.

Definition update_height_return_wit_4 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (0 <= h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r <> 0)) (PreH6 : (tr1 = empty)) (PreH7 : (l = 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node root_pre k v (unsigned_last_nbits ((h_2 + 1 )) (8)) l r )
  **  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  (store_non_empty_tree root_pre )
.

Definition update_height_return_wit_5 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (tr2 = empty)) (PreH2 : (h_2 <= 0)) (PreH3 : (r = 0)) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= 0)) (PreH6 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l <> 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node root_pre k v (0 + 1 ) l r )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  (store_non_empty_tree root_pre )
.

Definition update_height_return_wit_6 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (tr2 = empty)) (PreH2 : (r = 0)) (PreH3 : (tr1 = empty)) (PreH4 : (l = 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre <> 0)) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) ,
  (single_tree_node root_pre k v (0 + 1 ) l r )
|--
  (store_non_empty_tree root_pre )
.

Definition update_height_partial_solve_wit_1 := 
forall (root_pre: Z) ,
  (store_non_empty_tree root_pre )
|--
  EX (tr2: tree)  (tr1: tree)  (r: Z)  (l: Z)  (h: Z)  (v: Z)  (k: Z)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
.

Definition update_height_partial_solve_wit_2 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (l <> 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (root_pre <> 0)) (PreH6 : (0 <= 255)) (PreH7 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z) ,
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
.

Definition update_height_partial_solve_wit_3 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre <> 0)) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
.

Definition update_height_partial_solve_wit_4 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (root_pre <> 0)) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
.

Definition update_height_partial_solve_wit_5 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (l = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (root_pre <> 0)) (PreH6 : (0 <= 255)) (PreH7 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
|--
  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr2 )
.

Definition update_height_partial_solve_wit_6 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (r <> 0)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= 0)) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l <> 0)) (PreH6 : (h <= 255)) (PreH7 : (h >= 0)) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (root_pre <> 0)) (PreH10 : (0 <= 255)) (PreH11 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (r_3: Z)  (l_3: Z)  (h_3: Z)  (v_3: Z)  (k_3: Z) ,
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_7 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r <> 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l <> 0)) (PreH9 : (h <= 255)) (PreH10 : (h >= 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (root_pre <> 0)) (PreH13 : (0 <= 255)) (PreH14 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_8 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (r <> 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre <> 0)) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z) ,
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_9 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r <> 0)) (PreH5 : (tr1 = empty)) (PreH6 : (l = 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_10 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 > h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h <= 255)) (PreH11 : (h >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (h_2 > h_3) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_11 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 > 0)) (PreH2 : (r = 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l <> 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  “ (tr2 = empty) ” 
  &&  “ (h_2 > 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_12 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 <= h_3)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH5 : (r <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (l <> 0)) (PreH10 : (h <= 255)) (PreH11 : (h >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (root_pre <> 0)) (PreH14 : (0 <= 255)) (PreH15 : (0 >= 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (h_2 <= h_3) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_13 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (0 <= h_2)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= 0)) (PreH4 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r <> 0)) (PreH6 : (tr1 = empty)) (PreH7 : (l = 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (root_pre <> 0)) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (0 <= h_2) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_14 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 0)) (PreH2 : (r = 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH6 : (l <> 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (root_pre <> 0)) (PreH11 : (0 <= 255)) (PreH12 : (0 >= 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  “ (tr2 = empty) ” 
  &&  “ (h_2 <= 0) ” 
  &&  “ (r = 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition update_height_partial_solve_wit_15 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (r = 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (root_pre <> 0)) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
|--
  “ (tr2 = empty) ” 
  &&  “ (r = 0) ” 
  &&  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
.

(*----- Function rotateR -----*)

Definition rotateR_return_wit_1 := 
forall (root_pre: Z) (h: Z) (l: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (root_pre <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (root_pre <> 0)) ,
  (store_non_empty_tree l )
|--
  “ (l = l) ”
  &&  (store_non_empty_tree l )
.

Definition rotateR_partial_solve_wit_1 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (PreH1 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
|--
  EX (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr_2: tree)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
.

Definition rotateR_partial_solve_wit_2 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
.

Definition rotateR_partial_solve_wit_3 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
.

Definition rotateR_partial_solve_wit_4 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h r_2 r )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |->_)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> r_2)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
.

Definition rotateR_partial_solve_wit_5 := 
forall (root_pre: Z) (h: Z) (v_2: Z) (k_2: Z) (r: Z) (l: Z) (tr_2: tree) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (l <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node l k v h_2 l_2 root_pre )
  **  (single_tree_node root_pre k_2 v_2 h r_2 r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr_2 )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (store_non_empty_tree root_pre )
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> root_pre)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree l_2 tr1 )
.

Definition rotateR_partial_solve_wit_6 := 
forall (root_pre: Z) (h: Z) (l: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (l <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node l k v h_2 l_2 root_pre )
  **  (store_non_empty_tree root_pre )
  **  (store_tree l_2 tr1 )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_3: Z)  (tr_2: tree) ,
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (store_non_empty_tree l )
.

(*----- Function rotateL -----*)

Definition rotateL_return_wit_1 := 
forall (root_pre: Z) (h: Z) (r: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (root_pre <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (root_pre <> 0)) ,
  (store_non_empty_tree r )
|--
  “ (r = r) ”
  &&  (store_non_empty_tree r )
.

Definition rotateL_partial_solve_wit_1 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (PreH1 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
|--
  EX (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr_2: tree)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
.

Definition rotateL_partial_solve_wit_2 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
.

Definition rotateL_partial_solve_wit_3 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
.

Definition rotateL_partial_solve_wit_4 := 
forall (root_pre: Z) (h: Z) (v: Z) (k: Z) (r: Z) (l: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l l_2 )
  **  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |->_)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> l_2)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
.

Definition rotateL_partial_solve_wit_5 := 
forall (root_pre: Z) (h: Z) (v_2: Z) (k_2: Z) (r: Z) (l: Z) (tr_2: tree) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (r <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node r k v h_2 root_pre r_2 )
  **  (single_tree_node root_pre k_2 v_2 h l l_2 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr_2 )
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (store_non_empty_tree root_pre )
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> root_pre)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r_2 tr2 )
.

Definition rotateL_partial_solve_wit_6 := 
forall (root_pre: Z) (h: Z) (r: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (r <> 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node r k v h_2 root_pre r_2 )
  **  (store_non_empty_tree root_pre )
  **  (store_tree r_2 tr2 )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_3: Z)  (tr_2: tree) ,
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (store_non_empty_tree r )
.

(*----- Function rotateRL -----*)

Definition rotateRL_return_wit_1 := 
forall (root_pre: Z) (l1: Z) (h1: Z) (r: Z) (h: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval: Z) (PreH1 : (retval = l1)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l1 <> 0)) (PreH6 : (retval_2 = l1)) (PreH7 : (h1 <= 255)) (PreH8 : (h1 >= 0)) (PreH9 : (h <= 255)) (PreH10 : (h >= 0)) (PreH11 : (h_2 <= 255)) (PreH12 : (h_2 >= 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l1 <> 0)) (PreH15 : (root_pre <> 0)) (PreH16 : (r <> 0)) ,
  (store_non_empty_tree l1 )
|--
  “ (retval = l1) ”
  &&  (store_non_empty_tree l1 )
.

Definition rotateRL_partial_solve_wit_1 := 
forall (root_pre: Z) (r1: Z) (l1: Z) (h1: Z) (v1: Z) (k1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (PreH1 : (root_pre <> 0)) (PreH2 : (r <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (single_tree_node r k1 v1 h1 l1 r1 )
  **  (store_tree_shape l )
  **  (store_non_empty_tree l1 )
  **  (store_tree_shape r1 )
|--
  EX (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr_3: tree)  (tr_2: tree)  (tr: tree) ,
  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (r <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r1)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l1)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h1)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v1)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k1)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l1)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l1)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l1)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l1)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l1)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r1 tr_2 )
  **  (store_tree l tr )
.

Definition rotateRL_partial_solve_wit_2_pure := 
forall (root_pre: Z) (r1: Z) (l1: Z) (h1: Z) (v1: Z) (k1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (tr_3: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (l1 <> 0)) (PreH9 : (root_pre <> 0)) (PreH10 : (r <> 0)) ,
  (single_tree_node l1 k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (single_tree_node r k1 v1 h1 l1 r1 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r1 tr_2 )
  **  (store_tree l tr )
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (r <> 0) ”
.

Definition rotateRL_partial_solve_wit_2_aux := 
forall (root_pre: Z) (r1: Z) (l1: Z) (h1: Z) (v1: Z) (k1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (tr_3: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (l1 <> 0)) (PreH9 : (root_pre <> 0)) (PreH10 : (r <> 0)) ,
  (single_tree_node l1 k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (single_tree_node r k1 v1 h1 l1 r1 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r1 tr_2 )
  **  (store_tree l tr )
|--
  “ (r <> 0) ” 
  &&  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (r <> 0) ”
  &&  (single_tree_node r k1 v1 h1 l1 r1 )
  **  (store_non_empty_tree l1 )
  **  (store_tree_shape r1 )
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree l tr )
.

Definition rotateRL_partial_solve_wit_2 := rotateRL_partial_solve_wit_2_pure -> rotateRL_partial_solve_wit_2_aux.

Definition rotateRL_partial_solve_wit_3 := 
forall (root_pre: Z) (l1: Z) (h1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval: Z) (PreH1 : (retval = l1)) (PreH2 : (h1 <= 255)) (PreH3 : (h1 >= 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l1 <> 0)) (PreH10 : (root_pre <> 0)) (PreH11 : (r <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_non_empty_tree l1 )
  **  (store_tree l tr )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_2: Z)  (l_2: Z)  (h_3: Z)  (v_2: Z)  (k_2: Z)  (tr_3: tree) ,
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l1 <> 0) ” 
  &&  “ (retval = l1) ” 
  &&  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (r <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l1)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l1)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l1)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((l1)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l1)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree l tr )
.

Definition rotateRL_partial_solve_wit_4_pure := 
forall (root_pre: Z) (l1: Z) (h1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval: Z) (tr_3: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l1 <> 0)) (PreH5 : (retval = l1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (l1 <> 0)) (PreH14 : (root_pre <> 0)) (PreH15 : (r <> 0)) ,
  ((( &( "temp" ) )) # Ptr  |->_)
  **  (single_tree_node root_pre k v h l retval )
  **  (single_tree_node l1 k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree l tr )
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (root_pre <> 0) ”
.

Definition rotateRL_partial_solve_wit_4_aux := 
forall (root_pre: Z) (l1: Z) (h1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval: Z) (tr_3: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l1 <> 0)) (PreH5 : (retval = l1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (l1 <> 0)) (PreH14 : (root_pre <> 0)) (PreH15 : (r <> 0)) ,
  (single_tree_node root_pre k v h l retval )
  **  (single_tree_node l1 k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree l tr )
|--
  “ (root_pre <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l1 <> 0) ” 
  &&  “ (retval = l1) ” 
  &&  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (r <> 0) ”
  &&  (single_tree_node root_pre k v h l l1 )
  **  (store_tree_shape l )
  **  (store_non_empty_tree l1 )
.

Definition rotateRL_partial_solve_wit_4 := rotateRL_partial_solve_wit_4_pure -> rotateRL_partial_solve_wit_4_aux.

(*----- Function rotateLR -----*)

Definition rotateLR_return_wit_1 := 
forall (root_pre: Z) (r1: Z) (h1: Z) (l: Z) (h: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval: Z) (PreH1 : (retval = r1)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (r1 <> 0)) (PreH6 : (retval_2 = r1)) (PreH7 : (h1 <= 255)) (PreH8 : (h1 >= 0)) (PreH9 : (h <= 255)) (PreH10 : (h >= 0)) (PreH11 : (h_2 <= 255)) (PreH12 : (h_2 >= 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (r1 <> 0)) (PreH15 : (root_pre <> 0)) (PreH16 : (l <> 0)) ,
  (store_non_empty_tree r1 )
|--
  “ (retval = r1) ”
  &&  (store_non_empty_tree r1 )
.

Definition rotateLR_partial_solve_wit_1 := 
forall (root_pre: Z) (r1: Z) (l1: Z) (h1: Z) (v1: Z) (k1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (PreH1 : (root_pre <> 0)) (PreH2 : (l <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (single_tree_node l k1 v1 h1 l1 r1 )
  **  (store_tree_shape r )
  **  (store_tree_shape l1 )
  **  (store_non_empty_tree r1 )
|--
  EX (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr_3: tree)  (tr_2: tree)  (tr: tree) ,
  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (l <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r1)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l1)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h1)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v1)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k1)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r1)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r1)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r1)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r1)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r1)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l1 tr_2 )
  **  (store_tree r tr )
.

Definition rotateLR_partial_solve_wit_2_pure := 
forall (root_pre: Z) (r1: Z) (l1: Z) (h1: Z) (v1: Z) (k1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (tr_3: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (r1 <> 0)) (PreH9 : (root_pre <> 0)) (PreH10 : (l <> 0)) ,
  (single_tree_node r1 k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (single_tree_node l k1 v1 h1 l1 r1 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l1 tr_2 )
  **  (store_tree r tr )
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (l <> 0) ”
.

Definition rotateLR_partial_solve_wit_2_aux := 
forall (root_pre: Z) (r1: Z) (l1: Z) (h1: Z) (v1: Z) (k1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (tr_3: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h1 <= 255)) (PreH2 : (h1 >= 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_3 = (make_tree (tr1) (tr2)))) (PreH8 : (r1 <> 0)) (PreH9 : (root_pre <> 0)) (PreH10 : (l <> 0)) ,
  (single_tree_node r1 k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (single_tree_node l k1 v1 h1 l1 r1 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l1 tr_2 )
  **  (store_tree r tr )
|--
  “ (l <> 0) ” 
  &&  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (l <> 0) ”
  &&  (single_tree_node l k1 v1 h1 l1 r1 )
  **  (store_tree_shape l1 )
  **  (store_non_empty_tree r1 )
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr )
.

Definition rotateLR_partial_solve_wit_2 := rotateLR_partial_solve_wit_2_pure -> rotateLR_partial_solve_wit_2_aux.

Definition rotateLR_partial_solve_wit_3 := 
forall (root_pre: Z) (r1: Z) (h1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval: Z) (PreH1 : (retval = r1)) (PreH2 : (h1 <= 255)) (PreH3 : (h1 >= 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r1 <> 0)) (PreH10 : (root_pre <> 0)) (PreH11 : (l <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_non_empty_tree r1 )
  **  (store_tree r tr )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_2: Z)  (l_2: Z)  (h_3: Z)  (v_2: Z)  (k_2: Z)  (tr_3: tree) ,
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r1 <> 0) ” 
  &&  “ (retval = r1) ” 
  &&  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (l <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |->_)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r1)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r1)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r1)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r1)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r1)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr )
.

Definition rotateLR_partial_solve_wit_4_pure := 
forall (root_pre: Z) (r1: Z) (h1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval: Z) (tr_3: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r1 <> 0)) (PreH5 : (retval = r1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (r1 <> 0)) (PreH14 : (root_pre <> 0)) (PreH15 : (l <> 0)) ,
  ((( &( "temp" ) )) # Ptr  |->_)
  **  (single_tree_node root_pre k v h retval r )
  **  (single_tree_node r1 k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr )
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (root_pre <> 0) ”
.

Definition rotateLR_partial_solve_wit_4_aux := 
forall (root_pre: Z) (r1: Z) (h1: Z) (r: Z) (l: Z) (h: Z) (v: Z) (k: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval: Z) (tr_3: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr_3 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r1 <> 0)) (PreH5 : (retval = r1)) (PreH6 : (h1 <= 255)) (PreH7 : (h1 >= 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH13 : (r1 <> 0)) (PreH14 : (root_pre <> 0)) (PreH15 : (l <> 0)) ,
  (single_tree_node root_pre k v h retval r )
  **  (single_tree_node r1 k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr )
|--
  “ (root_pre <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r1 <> 0) ” 
  &&  “ (retval = r1) ” 
  &&  “ (h1 <= 255) ” 
  &&  “ (h1 >= 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r1 <> 0) ” 
  &&  “ (root_pre <> 0) ” 
  &&  “ (l <> 0) ”
  &&  (single_tree_node root_pre k v h r1 r )
  **  (store_non_empty_tree r1 )
  **  (store_tree_shape r )
.

Definition rotateLR_partial_solve_wit_4 := rotateLR_partial_solve_wit_4_pure -> rotateLR_partial_solve_wit_4_aux.

(*----- Function balance_factor -----*)

Definition balance_factor_safety_wit_1 := 
forall (root_pre: Z) ,
  ((( &( "rh" ) )) # UChar  |->_)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
  **  (store_tree_shape root_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_2 := 
forall (root_pre: Z) ,
  ((( &( "lh" ) )) # UChar  |->_)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
  **  (store_tree_shape root_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_3 := 
forall (root_pre: Z) ,
  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
  **  (store_tree_shape root_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_4 := 
forall (root_pre: Z) (PreH1 : (root_pre = 0)) ,
  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
  **  (store_tree_shape root_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_5 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (tr = (make_tree (tr1) (tr2)))) (PreH4 : (0 <= 255)) (PreH5 : (0 >= 0)) (PreH6 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_6 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) (PreH10 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h_2)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_7 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (tr1 = empty)) (PreH2 : (l = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (0 <= 255)) (PreH7 : (0 >= 0)) (PreH8 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_factor_safety_wit_8 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (r = 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (0 <= 255)) (PreH8 : (0 >= 0)) (PreH9 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition balance_factor_safety_wit_9 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (r = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l <> 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) (PreH11 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h l_2 r_2 )
  **  (single_tree_node root_pre k v h_2 l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
  **  ((( &( "rh" ) )) # UChar  |-> 0)
  **  ((( &( "lh" ) )) # UChar  |-> h)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((h - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h - 0 )) ”
.

Definition balance_factor_safety_wit_10 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_2: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r <> 0)) (PreH5 : (tr1 = empty)) (PreH6 : (l = 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (0 <= 255)) (PreH11 : (0 >= 0)) (PreH12 : (root_pre <> 0)) ,
  (single_tree_node r k_2 v_2 h l_2 r_2 )
  **  (single_tree_node root_pre k v h_2 l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h)
  **  ((( &( "lh" ) )) # UChar  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((0 - h ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - h )) ”
.

Definition balance_factor_safety_wit_11 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h_3: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_2: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l <> 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) (PreH14 : (root_pre <> 0)) ,
  (single_tree_node r k_3 v_3 h_2 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h l_2 r_2 )
  **  (single_tree_node root_pre k v h_3 l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "rh" ) )) # UChar  |-> h_2)
  **  ((( &( "lh" ) )) # UChar  |-> h)
  **  ((( &( "root" ) )) # Ptr  |-> root_pre)
|--
  “ ((h - h_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h - h_2 )) ”
.

Definition balance_factor_return_wit_1 := 
forall (root_pre: Z) (tr: tree) (k_4: Z) (v_4: Z) (h_6: Z) (l_4: Z) (r_4: Z) (tr1: tree) (tr2: tree) (k_5: Z) (v_5: Z) (h: Z) (l_5: Z) (r_5: Z) (tr1_2: tree) (tr2_2: tree) (k_6: Z) (v_6: Z) (h_2: Z) (l_6: Z) (r_6: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r_4 <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l_4 <> 0)) (PreH9 : (h_6 <= 255)) (PreH10 : (h_6 >= 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) (PreH14 : (root_pre <> 0)) ,
  (single_tree_node r_4 k_6 v_6 h_2 l_6 r_6 )
  **  (single_tree_node l_4 k_5 v_5 h l_5 r_5 )
  **  (single_tree_node root_pre k_4 v_4 h_6 l_4 r_4 )
  **  (store_tree r_6 tr2_3 )
  **  (store_tree l_6 tr1_3 )
  **  (store_tree r_5 tr2_2 )
  **  (store_tree l_5 tr1_2 )
|--
  (“ ((h - h_2 ) = 0) ”
  &&  (store_tree_shape root_pre ))
  ||
  (EX (k: Z)  (v: Z)  (h_3: Z)  (l: Z)  (r: Z) ,
  “ ((h - h_2 ) >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k v h_3 l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r ))
  ||
  (EX (k_2: Z)  (v_2: Z)  (h_4: Z)  (l_2: Z)  (r_2: Z) ,
  “ ((h - h_2 ) <= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_2 v_2 h_4 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 ))
  ||
  (EX (k_3: Z)  (v_3: Z)  (h_5: Z)  (l_3: Z)  (r_3: Z)  (x: Z) ,
  “ ((h - h_2 ) = x) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_3 v_3 h_5 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 ))
.

Definition balance_factor_return_wit_2 := 
forall (root_pre: Z) (tr: tree) (k_4: Z) (v_4: Z) (h_5: Z) (l_4: Z) (r_4: Z) (tr1: tree) (tr2: tree) (k_5: Z) (v_5: Z) (h: Z) (l_5: Z) (r_5: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r_4 <> 0)) (PreH5 : (tr1 = empty)) (PreH6 : (l_4 = 0)) (PreH7 : (h_5 <= 255)) (PreH8 : (h_5 >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (0 <= 255)) (PreH11 : (0 >= 0)) (PreH12 : (root_pre <> 0)) ,
  (single_tree_node r_4 k_5 v_5 h l_5 r_5 )
  **  (single_tree_node root_pre k_4 v_4 h_5 l_4 r_4 )
  **  (store_tree r_5 tr2_2 )
  **  (store_tree l_5 tr1_2 )
|--
  (“ ((0 - h ) = 0) ”
  &&  (store_tree_shape root_pre ))
  ||
  (EX (k: Z)  (v: Z)  (h_2: Z)  (l: Z)  (r: Z) ,
  “ ((0 - h ) >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k v h_2 l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r ))
  ||
  (EX (k_2: Z)  (v_2: Z)  (h_3: Z)  (l_2: Z)  (r_2: Z) ,
  “ ((0 - h ) <= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 ))
  ||
  (EX (k_3: Z)  (v_3: Z)  (h_4: Z)  (l_3: Z)  (r_3: Z)  (x: Z) ,
  “ ((0 - h ) = x) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 ))
.

Definition balance_factor_return_wit_3 := 
forall (root_pre: Z) (tr: tree) (k_4: Z) (v_4: Z) (h_5: Z) (l_4: Z) (r_4: Z) (tr1: tree) (tr2: tree) (k_5: Z) (v_5: Z) (h: Z) (l_5: Z) (r_5: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (r_4 = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l_4 <> 0)) (PreH6 : (h_5 <= 255)) (PreH7 : (h_5 >= 0)) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) (PreH11 : (root_pre <> 0)) ,
  (single_tree_node l_4 k_5 v_5 h l_5 r_5 )
  **  (single_tree_node root_pre k_4 v_4 h_5 l_4 r_4 )
  **  (store_tree r_5 tr2_2 )
  **  (store_tree l_5 tr1_2 )
  **  (store_tree r_4 tr2 )
|--
  (“ ((h - 0 ) = 0) ”
  &&  (store_tree_shape root_pre ))
  ||
  (EX (k: Z)  (v: Z)  (h_2: Z)  (l: Z)  (r: Z) ,
  “ ((h - 0 ) >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k v h_2 l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r ))
  ||
  (EX (k_2: Z)  (v_2: Z)  (h_3: Z)  (l_2: Z)  (r_2: Z) ,
  “ ((h - 0 ) <= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 ))
  ||
  (EX (k_3: Z)  (v_3: Z)  (h_4: Z)  (l_3: Z)  (r_3: Z)  (x: Z) ,
  “ ((h - 0 ) = x) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 ))
.

Definition balance_factor_return_wit_4 := 
forall (root_pre: Z) (tr: tree) (k_4: Z) (v_4: Z) (h_4: Z) (l_4: Z) (r_4: Z) (tr1: tree) (tr2: tree) (PreH1 : (r_4 = 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l_4 = 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (0 <= 255)) (PreH8 : (0 >= 0)) (PreH9 : (root_pre <> 0)) ,
  (single_tree_node root_pre k_4 v_4 h_4 l_4 r_4 )
  **  (store_tree r_4 tr2 )
|--
  (“ ((0 - 0 ) = 0) ”
  &&  (store_tree_shape root_pre ))
  ||
  (EX (k: Z)  (v: Z)  (h: Z)  (l: Z)  (r: Z) ,
  “ ((0 - 0 ) >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r ))
  ||
  (EX (k_2: Z)  (v_2: Z)  (h_2: Z)  (l_2: Z)  (r_2: Z) ,
  “ ((0 - 0 ) <= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_2 v_2 h_2 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 ))
  ||
  (EX (k_3: Z)  (v_3: Z)  (h_3: Z)  (l_3: Z)  (r_3: Z)  (x: Z) ,
  “ ((0 - 0 ) = x) ” 
  &&  “ (root_pre <> 0) ”
  &&  (single_tree_node root_pre k_3 v_3 h_3 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 ))
.

Definition balance_factor_return_wit_5 := 
forall (root_pre: Z) (PreH1 : (root_pre = 0)) ,
  (store_tree_shape root_pre )
|--
  “ (0 = 0) ”
  &&  (store_tree_shape root_pre )
.

Definition balance_factor_partial_solve_wit_1 := 
forall (root_pre: Z) (PreH1 : (root_pre <> 0)) ,
  (store_tree_shape root_pre )
|--
  EX (tr2: tree)  (tr1: tree)  (r: Z)  (l: Z)  (h: Z)  (v: Z)  (k: Z)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
.

Definition balance_factor_partial_solve_wit_2 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (l <> 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (0 <= 255)) (PreH6 : (0 >= 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z) ,
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
.

Definition balance_factor_partial_solve_wit_3 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) (PreH10 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
.

Definition balance_factor_partial_solve_wit_4 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (tr = (make_tree (tr1) (tr2)))) (PreH8 : (0 <= 255)) (PreH9 : (0 >= 0)) (PreH10 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
.

Definition balance_factor_partial_solve_wit_5 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (l = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (0 <= 255)) (PreH6 : (0 >= 0)) (PreH7 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
|--
  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr2 )
.

Definition balance_factor_partial_solve_wit_6 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (r <> 0)) (PreH2 : (h_2 <= 255)) (PreH3 : (h_2 >= 0)) (PreH4 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH5 : (l <> 0)) (PreH6 : (h <= 255)) (PreH7 : (h >= 0)) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (0 <= 255)) (PreH10 : (0 >= 0)) (PreH11 : (root_pre <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r tr2 )
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (r_3: Z)  (l_3: Z)  (h_3: Z)  (v_3: Z)  (k_3: Z) ,
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition balance_factor_partial_solve_wit_7 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_3: tree) (tr2_3: tree) (PreH1 : (h_3 <= 255)) (PreH2 : (h_3 >= 0)) (PreH3 : (tr2 = (make_tree (tr1_3) (tr2_3)))) (PreH4 : (r <> 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr1 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (l <> 0)) (PreH9 : (h <= 255)) (PreH10 : (h >= 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (0 <= 255)) (PreH13 : (0 >= 0)) (PreH14 : (root_pre <> 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr1 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_3 )
  **  (store_tree l_3 tr1_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition balance_factor_partial_solve_wit_8 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (r <> 0)) (PreH2 : (tr1 = empty)) (PreH3 : (l = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (tr = (make_tree (tr1) (tr2)))) (PreH7 : (0 <= 255)) (PreH8 : (0 >= 0)) (PreH9 : (root_pre <> 0)) ,
  (single_tree_node root_pre k v h l r )
  **  (store_tree r tr2 )
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z) ,
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

Definition balance_factor_partial_solve_wit_9 := 
forall (root_pre: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (r <> 0)) (PreH5 : (tr1 = empty)) (PreH6 : (l = 0)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (0 <= 255)) (PreH11 : (0 >= 0)) (PreH12 : (root_pre <> 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node root_pre k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
|--
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr1 = empty) ” 
  &&  “ (l = 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (0 <= 255) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (root_pre <> 0) ”
  &&  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((root_pre)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((root_pre)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((root_pre)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((root_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((root_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
.

(*----- Function balance -----*)

Definition balance_safety_wit_1 := 
forall (p_pre: Z) (p_pre_v: Z) ,
  ((( &( "rh" ) )) # Int  |->_)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_2 := 
forall (p_pre: Z) (p_pre_v: Z) ,
  ((( &( "lh" ) )) # Int  |->_)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_3 := 
forall (p_pre: Z) (p_pre_v: Z) (retval: Z) (PreH1 : (retval = 0)) ,
  (store_tree_shape p_pre_v )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_4 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_5 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_6 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (PreH1 : (retval = x)) (PreH2 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_7 := 
forall (p_pre: Z) (p_pre_v: Z) (retval: Z) (PreH1 : (retval > 1)) (PreH2 : (retval = 0)) ,
  (store_tree_shape p_pre_v )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_8 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval > 1)) (PreH2 : (retval <= 0)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_9 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= 0)) (PreH6 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH7 : (l <> 0)) (PreH8 : (retval > 1)) (PreH9 : (retval >= 0)) (PreH10 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_10 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (l <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l <> 0)) (PreH9 : (retval > 1)) (PreH10 : (retval >= 0)) (PreH11 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_11 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (l <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l <> 0)) (PreH9 : (retval > 1)) (PreH10 : (retval >= 0)) (PreH11 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_12 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 = x)) (PreH2 : (l <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l <> 0)) (PreH9 : (retval > 1)) (PreH10 : (retval >= 0)) (PreH11 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_13 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= 0)) (PreH6 : (h_3 <= 255)) (PreH7 : (h_3 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (r <> 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (l <> 0)) (PreH12 : (retval > 1)) (PreH13 : (retval = x)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_14 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (l <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_15 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (l <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_16 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 = x_2)) (PreH2 : (l <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_17 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l <> 0)) (PreH9 : (retval > 1)) (PreH10 : (retval >= 0)) (PreH11 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_18 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_19 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_20 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_21 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (l <> 0)) (PreH9 : (retval > 1)) (PreH10 : (retval >= 0)) (PreH11 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_22 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_23 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_24 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 = x)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_25 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval > 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_26 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_27 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_28 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 = x_2)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_29 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_30 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_31 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_32 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_33 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval = x)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition balance_safety_wit_34 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval <= 0)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition balance_safety_wit_35 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval >= 0)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition balance_safety_wit_36 := 
forall (p_pre: Z) (p_pre_v: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval = 0)) ,
  (store_tree_shape p_pre_v )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition balance_safety_wit_37 := 
forall (p_pre: Z) (p_pre_v: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval = 0)) ,
  (store_tree_shape p_pre_v )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_38 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval >= 0)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_39 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval <= 0)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_40 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (PreH1 : (retval <= 1)) (PreH2 : (retval = x)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_non_empty_tree r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balance_safety_wit_41 := 
forall (p_pre: Z) (p_pre_v: Z) (retval: Z) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) ,
  (store_tree_shape p_pre_v )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_42 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval >= 0)) (PreH4 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_43 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= 0)) (PreH6 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH7 : (r <> 0)) (PreH8 : (retval < (-1))) (PreH9 : (retval <= 1)) (PreH10 : (retval <= 0)) (PreH11 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_44 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (r <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r <> 0)) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_45 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (r <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r <> 0)) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_46 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 = x)) (PreH2 : (r <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r <> 0)) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_47 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (h_2 <= 255)) (PreH5 : (h_2 >= 0)) (PreH6 : (h_3 <= 255)) (PreH7 : (h_3 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH9 : (r <> 0)) (PreH10 : (tr = (make_tree (tr1) (tr2)))) (PreH11 : (l <> 0)) (PreH12 : (retval < (-1))) (PreH13 : (retval <= 1)) (PreH14 : (retval = x)) (PreH15 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_48 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (r <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_49 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (r <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_50 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 = x_2)) (PreH2 : (r <> 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_51 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r <> 0)) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_52 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_53 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_54 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_55 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH8 : (r <> 0)) (PreH9 : (retval < (-1))) (PreH10 : (retval <= 1)) (PreH11 : (retval <= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_56 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_57 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_58 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 = x)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_59 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (h_2 <= 255)) (PreH6 : (h_2 >= 0)) (PreH7 : (h_3 <= 255)) (PreH8 : (h_3 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH10 : (r <> 0)) (PreH11 : (tr = (make_tree (tr1) (tr2)))) (PreH12 : (l <> 0)) (PreH13 : (retval < (-1))) (PreH14 : (retval <= 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_60 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_61 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_62 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 = x_2)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balance_safety_wit_63 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_64 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_65 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_safety_wit_66 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ False ”
.

Definition balance_return_wit_1 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_tree_shape r )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_2 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_3 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_4 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = x)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_5 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_tree_shape r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_6 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v_2 <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_7 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v_2 <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_8 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 <= 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = x_2)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v_2 <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_9 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (r: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (l: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (retval_2 > 0)) (PreH5 : (retval_2 >= 0)) (PreH6 : (retval_2 >= 0)) (PreH7 : (r <> 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (r <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval <= 0)) (PreH17 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_10 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (r: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (l: Z) (r_2: Z) (x: Z) (retval_2: Z) (tr_2: tree) (h_4: Z) (tr1_2: tree) (tr2_2: tree) (retval_3: Z) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (r_2 <> 0)) (PreH8 : (retval_2 > 0)) (PreH9 : (retval_2 >= 0)) (PreH10 : (retval_2 = x)) (PreH11 : (r <> 0)) (PreH12 : (h <= 255)) (PreH13 : (h >= 0)) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= 0)) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (r <> 0)) (PreH18 : (retval < (-1))) (PreH19 : (retval <= 1)) (PreH20 : (retval <= 0)) (PreH21 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_11 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (l_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = l_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (retval_2 > 0)) (PreH5 : (retval_2 >= 0)) (PreH6 : (retval_2 >= 0)) (PreH7 : (r <> 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (h_3 <= 255)) (PreH13 : (h_3 >= 0)) (PreH14 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH15 : (r <> 0)) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (l <> 0)) (PreH18 : (retval < (-1))) (PreH19 : (retval <= 1)) (PreH20 : (retval = x)) (PreH21 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l_2 )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_12 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (l_2: Z) (r_2: Z) (x_2: Z) (retval_2: Z) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (retval_3: Z) (PreH1 : (retval_3 = l_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= 0)) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (r_2 <> 0)) (PreH8 : (retval_2 > 0)) (PreH9 : (retval_2 >= 0)) (PreH10 : (retval_2 = x_2)) (PreH11 : (r <> 0)) (PreH12 : (h <= 255)) (PreH13 : (h >= 0)) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= 0)) (PreH16 : (h_3 <= 255)) (PreH17 : (h_3 >= 0)) (PreH18 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH19 : (r <> 0)) (PreH20 : (tr = (make_tree (tr1) (tr2)))) (PreH21 : (l <> 0)) (PreH22 : (retval < (-1))) (PreH23 : (retval <= 1)) (PreH24 : (retval = x)) (PreH25 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l_2 )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_13 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (r: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (r_2: Z) (retval_2: Z) (tr_2: tree) (h_4: Z) (tr1_2: tree) (tr2_2: tree) (retval_3: Z) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (r_2 <> 0)) (PreH8 : (retval_2 < 0)) (PreH9 : (retval_2 <= 0)) (PreH10 : (r <> 0)) (PreH11 : (h <= 255)) (PreH12 : (h >= 0)) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= 0)) (PreH15 : (tr = (make_tree (tr1) (tr2)))) (PreH16 : (r <> 0)) (PreH17 : (retval < (-1))) (PreH18 : (retval <= 1)) (PreH19 : (retval <= 0)) (PreH20 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_14 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (r: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (l: Z) (r_2: Z) (x: Z) (retval_2: Z) (tr_2: tree) (h_4: Z) (tr1_2: tree) (tr2_2: tree) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (retval_3: Z) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (h_5 <= 255)) (PreH7 : (h_5 >= 0)) (PreH8 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH9 : (r_2 <> 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (l <> 0)) (PreH12 : (retval_2 < 0)) (PreH13 : (retval_2 = x)) (PreH14 : (r <> 0)) (PreH15 : (h <= 255)) (PreH16 : (h >= 0)) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= 0)) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (r <> 0)) (PreH21 : (retval < (-1))) (PreH22 : (retval <= 1)) (PreH23 : (retval <= 0)) (PreH24 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_15 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (r_2: Z) (retval_2: Z) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (retval_3: Z) (PreH1 : (retval_3 = r)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= 0)) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (r_2 <> 0)) (PreH8 : (retval_2 < 0)) (PreH9 : (retval_2 <= 0)) (PreH10 : (r <> 0)) (PreH11 : (h <= 255)) (PreH12 : (h >= 0)) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= 0)) (PreH15 : (h_3 <= 255)) (PreH16 : (h_3 >= 0)) (PreH17 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH18 : (r <> 0)) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (l <> 0)) (PreH21 : (retval < (-1))) (PreH22 : (retval <= 1)) (PreH23 : (retval = x)) (PreH24 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_16 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (l_2: Z) (r_2: Z) (x_2: Z) (retval_2: Z) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (tr_4: tree) (h_6: Z) (tr1_4: tree) (tr2_4: tree) (retval_3: Z) (PreH1 : (retval_3 = r)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= 0)) (PreH6 : (h_6 <= 255)) (PreH7 : (h_6 >= 0)) (PreH8 : (tr_4 = (make_tree (tr1_4) (tr2_4)))) (PreH9 : (r_2 <> 0)) (PreH10 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH11 : (l_2 <> 0)) (PreH12 : (retval_2 < 0)) (PreH13 : (retval_2 = x_2)) (PreH14 : (r <> 0)) (PreH15 : (h <= 255)) (PreH16 : (h >= 0)) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= 0)) (PreH19 : (h_3 <= 255)) (PreH20 : (h_3 >= 0)) (PreH21 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH22 : (r <> 0)) (PreH23 : (tr = (make_tree (tr1) (tr2)))) (PreH24 : (l <> 0)) (PreH25 : (retval < (-1))) (PreH26 : (retval <= 1)) (PreH27 : (retval = x)) (PreH28 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_17 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_18 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_19 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_20 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = x)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_21 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v_2 <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_tree_shape l )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_22 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_23 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_24 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 >= 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = x_2)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v_2 <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v_2 k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_25 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (r: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <= 0)) (PreH6 : (retval_2 <= 0)) (PreH7 : (l <> 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval >= 0)) (PreH16 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_26 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (l_2: Z) (r: Z) (x: Z) (retval_2: Z) (tr_2: tree) (h_4: Z) (tr1_2: tree) (tr2_2: tree) (retval_3: Z) (PreH1 : (retval_3 = r)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l_2 <> 0)) (PreH8 : (retval_2 < 0)) (PreH9 : (retval_2 <= 0)) (PreH10 : (retval_2 = x)) (PreH11 : (l <> 0)) (PreH12 : (h <= 255)) (PreH13 : (h >= 0)) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= 0)) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (l <> 0)) (PreH18 : (retval > 1)) (PreH19 : (retval >= 0)) (PreH20 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_27 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (r_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = r_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (retval_2 < 0)) (PreH5 : (retval_2 <= 0)) (PreH6 : (retval_2 <= 0)) (PreH7 : (l <> 0)) (PreH8 : (h <= 255)) (PreH9 : (h >= 0)) (PreH10 : (h_2 <= 255)) (PreH11 : (h_2 >= 0)) (PreH12 : (h_3 <= 255)) (PreH13 : (h_3 >= 0)) (PreH14 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH15 : (r <> 0)) (PreH16 : (tr = (make_tree (tr1) (tr2)))) (PreH17 : (l <> 0)) (PreH18 : (retval > 1)) (PreH19 : (retval = x)) (PreH20 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r_2 )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_28 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (l_2: Z) (r_2: Z) (x_2: Z) (retval_2: Z) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (retval_3: Z) (PreH1 : (retval_3 = r_2)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= 0)) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (l_2 <> 0)) (PreH8 : (retval_2 < 0)) (PreH9 : (retval_2 <= 0)) (PreH10 : (retval_2 = x_2)) (PreH11 : (l <> 0)) (PreH12 : (h <= 255)) (PreH13 : (h >= 0)) (PreH14 : (h_2 <= 255)) (PreH15 : (h_2 >= 0)) (PreH16 : (h_3 <= 255)) (PreH17 : (h_3 >= 0)) (PreH18 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH19 : (r <> 0)) (PreH20 : (tr = (make_tree (tr1) (tr2)))) (PreH21 : (l <> 0)) (PreH22 : (retval > 1)) (PreH23 : (retval = x)) (PreH24 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree r_2 )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_29 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (l_2: Z) (retval_2: Z) (tr_2: tree) (h_4: Z) (tr1_2: tree) (tr2_2: tree) (retval_3: Z) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH7 : (l_2 <> 0)) (PreH8 : (retval_2 > 0)) (PreH9 : (retval_2 >= 0)) (PreH10 : (l <> 0)) (PreH11 : (h <= 255)) (PreH12 : (h >= 0)) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= 0)) (PreH15 : (tr = (make_tree (tr1) (tr2)))) (PreH16 : (l <> 0)) (PreH17 : (retval > 1)) (PreH18 : (retval >= 0)) (PreH19 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_30 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (h_3: Z) (l_2: Z) (r: Z) (x: Z) (retval_2: Z) (tr_2: tree) (h_4: Z) (tr1_2: tree) (tr2_2: tree) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (retval_3: Z) (PreH1 : (retval_3 = l)) (PreH2 : (h_3 <= 255)) (PreH3 : (h_3 >= 0)) (PreH4 : (h_4 <= 255)) (PreH5 : (h_4 >= 0)) (PreH6 : (h_5 <= 255)) (PreH7 : (h_5 >= 0)) (PreH8 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH9 : (r <> 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (l_2 <> 0)) (PreH12 : (retval_2 > 0)) (PreH13 : (retval_2 = x)) (PreH14 : (l <> 0)) (PreH15 : (h <= 255)) (PreH16 : (h >= 0)) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= 0)) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (l <> 0)) (PreH21 : (retval > 1)) (PreH22 : (retval >= 0)) (PreH23 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_31 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (l_2: Z) (retval_2: Z) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (retval_3: Z) (PreH1 : (retval_3 = l)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= 0)) (PreH6 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH7 : (l_2 <> 0)) (PreH8 : (retval_2 > 0)) (PreH9 : (retval_2 >= 0)) (PreH10 : (l <> 0)) (PreH11 : (h <= 255)) (PreH12 : (h >= 0)) (PreH13 : (h_2 <= 255)) (PreH14 : (h_2 >= 0)) (PreH15 : (h_3 <= 255)) (PreH16 : (h_3 >= 0)) (PreH17 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH18 : (r <> 0)) (PreH19 : (tr = (make_tree (tr1) (tr2)))) (PreH20 : (l <> 0)) (PreH21 : (retval > 1)) (PreH22 : (retval = x)) (PreH23 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_32 := 
forall (p_pre: Z) (p_pre_v_2: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (h_4: Z) (l_2: Z) (r_2: Z) (x_2: Z) (retval_2: Z) (tr_3: tree) (h_5: Z) (tr1_3: tree) (tr2_3: tree) (tr_4: tree) (h_6: Z) (tr1_4: tree) (tr2_4: tree) (retval_3: Z) (PreH1 : (retval_3 = l)) (PreH2 : (h_4 <= 255)) (PreH3 : (h_4 >= 0)) (PreH4 : (h_5 <= 255)) (PreH5 : (h_5 >= 0)) (PreH6 : (h_6 <= 255)) (PreH7 : (h_6 >= 0)) (PreH8 : (tr_4 = (make_tree (tr1_4) (tr2_4)))) (PreH9 : (r_2 <> 0)) (PreH10 : (tr_3 = (make_tree (tr1_3) (tr2_3)))) (PreH11 : (l_2 <> 0)) (PreH12 : (retval_2 > 0)) (PreH13 : (retval_2 = x_2)) (PreH14 : (l <> 0)) (PreH15 : (h <= 255)) (PreH16 : (h >= 0)) (PreH17 : (h_2 <= 255)) (PreH18 : (h_2 >= 0)) (PreH19 : (h_3 <= 255)) (PreH20 : (h_3 >= 0)) (PreH21 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH22 : (r <> 0)) (PreH23 : (tr = (make_tree (tr1) (tr2)))) (PreH24 : (l <> 0)) (PreH25 : (retval > 1)) (PreH26 : (retval = x)) (PreH27 : (p_pre_v_2 <> 0)) ,
  (store_non_empty_tree l )
  **  ((p_pre) # Ptr  |-> retval_3)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_33 := 
forall (p_pre: Z) (p_pre_v_2: Z) (retval: Z) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) ,
  (store_tree_shape p_pre_v_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_34 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval >= 0)) (PreH4 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_35 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval <= 0)) (PreH4 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_return_wit_36 := 
forall (p_pre: Z) (p_pre_v_2: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (PreH1 : (retval >= (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = x)) (PreH4 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_non_empty_tree l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition balance_partial_solve_wit_1 := 
forall (p_pre: Z) (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
|--
  (store_tree_shape p_pre_v )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_2 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval > 1)) (PreH2 : (retval >= 0)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr_2: tree)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_3 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (l <> 0)) (PreH7 : (retval > 1)) (PreH8 : (retval >= 0)) (PreH9 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (store_tree_shape l )
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_4 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (PreH1 : (retval > 1)) (PreH2 : (retval = x)) (PreH3 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_3: Z)  (l_3: Z)  (h_3: Z)  (v_3: Z)  (k_3: Z)  (tr_2: tree)  (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_2 )
  **  (store_tree l_3 tr1_2 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_5 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_3: Z) (v_3: Z) (h_2: Z) (l_3: Z) (r_3: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (h_3 <= 255)) (PreH6 : (h_3 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (r <> 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval = x)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node l k_3 v_3 h_2 l_3 r_3 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  (store_tree r_3 tr2 )
  **  (store_tree l_3 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (store_tree_shape l )
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_6_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_6_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_4: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l_2 <> 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_6 := balance_partial_solve_wit_6_pure -> balance_partial_solve_wit_6_aux.

Definition balance_partial_solve_wit_7_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 = x)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_7_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 = x)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (l <> 0)) (PreH10 : (retval > 1)) (PreH11 : (retval >= 0)) (PreH12 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_4: tree)  (tr2_2: tree)  (tr1_2: tree)  (h_4: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (tr_4 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r_2 <> 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l_2 <> 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 = x) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_7 := balance_partial_solve_wit_7_pure -> balance_partial_solve_wit_7_aux.

Definition balance_partial_solve_wit_8_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_8_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (l_3 <> 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_8 := balance_partial_solve_wit_8_pure -> balance_partial_solve_wit_8_aux.

Definition balance_partial_solve_wit_9_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 = x_2)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_9_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 = x_2)) (PreH3 : (l <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval > 1)) (PreH15 : (retval = x)) (PreH16 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_4: tree)  (tr1_4: tree)  (h_6: Z)  (tr_4: tree)  (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (h_6 <= 255) ” 
  &&  “ (h_6 >= 0) ” 
  &&  “ (tr_4 = (make_tree (tr1_4) (tr2_4))) ” 
  &&  “ (r_3 <> 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (l_3 <> 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 = x_2) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_tree_shape r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_9 := balance_partial_solve_wit_9_pure -> balance_partial_solve_wit_9_aux.

Definition balance_partial_solve_wit_10_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ”
.

Definition balance_partial_solve_wit_10_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape r )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_10 := balance_partial_solve_wit_10_pure -> balance_partial_solve_wit_10_aux.

Definition balance_partial_solve_wit_11_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = x)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ”
.

Definition balance_partial_solve_wit_11_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = x)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval > 1)) (PreH12 : (retval >= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree r tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_4: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l_2 <> 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (retval_2 = x) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape r )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_11 := balance_partial_solve_wit_11_pure -> balance_partial_solve_wit_11_aux.

Definition balance_partial_solve_wit_12_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ”
.

Definition balance_partial_solve_wit_12_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 <= 0)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape r )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_12 := balance_partial_solve_wit_12_pure -> balance_partial_solve_wit_12_aux.

Definition balance_partial_solve_wit_13_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = x_2)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((( &( "lbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ”
.

Definition balance_partial_solve_wit_13_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (h_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (retval_2 = x_2)) (PreH4 : (l <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval > 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2_2 )
  **  (store_tree l_2 tr1_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (l_3 <> 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (retval_2 = x_2) ” 
  &&  “ (l <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval > 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node l k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape r )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_13 := balance_partial_solve_wit_13_pure -> balance_partial_solve_wit_13_aux.

Definition balance_partial_solve_wit_14 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval <= 0)) (PreH4 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr_2: tree)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_15 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH6 : (r <> 0)) (PreH7 : (retval < (-1))) (PreH8 : (retval <= 1)) (PreH9 : (retval <= 0)) (PreH10 : (p_pre_v <> 0)) ,
  (single_tree_node r k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (store_tree_shape r )
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_16 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (PreH1 : (retval < (-1))) (PreH2 : (retval <= 1)) (PreH3 : (retval = x)) (PreH4 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_non_empty_tree l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (r_3: Z)  (l_3: Z)  (h_3: Z)  (v_3: Z)  (k_3: Z)  (tr_2: tree)  (tr2: tree)  (tr1: tree)  (r_2: Z)  (l_2: Z)  (h_2: Z)  (v_2: Z)  (k_2: Z)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  ((&((r)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_3)
  **  ((&((r)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_3)
  **  ((&((r)  # "tree" ->ₛ "height")) # UChar  |-> h_3)
  **  ((&((r)  # "tree" ->ₛ "value")) # Int  |-> v_3)
  **  ((&((r)  # "tree" ->ₛ "key")) # Int  |-> k_3)
  **  (store_tree r_3 tr2_2 )
  **  (store_tree l_3 tr1_2 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_17 := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (k_3: Z) (v_3: Z) (h_3: Z) (l_3: Z) (r_3: Z) (tr1_2: tree) (tr2_2: tree) (PreH1 : (h <= 255)) (PreH2 : (h >= 0)) (PreH3 : (h_2 <= 255)) (PreH4 : (h_2 >= 0)) (PreH5 : (h_3 <= 255)) (PreH6 : (h_3 >= 0)) (PreH7 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH8 : (r <> 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (l <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval = x)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node r k_3 v_3 h_3 l_3 r_3 )
  **  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r_3 tr2_2 )
  **  (store_tree l_3 tr1_2 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (store_tree_shape r )
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((l)  # "tree" ->ₛ "rchild")) # Ptr  |-> r_2)
  **  ((&((l)  # "tree" ->ₛ "lchild")) # Ptr  |-> l_2)
  **  ((&((l)  # "tree" ->ₛ "height")) # UChar  |-> h_2)
  **  ((&((l)  # "tree" ->ₛ "value")) # Int  |-> v_2)
  **  ((&((l)  # "tree" ->ₛ "key")) # Int  |-> k_2)
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_18_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_18_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_4: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r_2 <> 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_18 := balance_partial_solve_wit_18_pure -> balance_partial_solve_wit_18_aux.

Definition balance_partial_solve_wit_19_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 = x)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_19_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 = x)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH9 : (r <> 0)) (PreH10 : (retval < (-1))) (PreH11 : (retval <= 1)) (PreH12 : (retval <= 0)) (PreH13 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_4: tree)  (tr2_2: tree)  (tr1_2: tree)  (h_4: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (tr_4 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r_2 <> 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (l_2 <> 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 = x) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_19 := balance_partial_solve_wit_19_pure -> balance_partial_solve_wit_19_aux.

Definition balance_partial_solve_wit_20_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_20_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 <= 0)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r_3 <> 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 <= 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_20 := balance_partial_solve_wit_20_pure -> balance_partial_solve_wit_20_aux.

Definition balance_partial_solve_wit_21_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 = x_2)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ”
.

Definition balance_partial_solve_wit_21_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 < 0)) (PreH2 : (retval_2 = x_2)) (PreH3 : (r <> 0)) (PreH4 : (h <= 255)) (PreH5 : (h >= 0)) (PreH6 : (h_2 <= 255)) (PreH7 : (h_2 >= 0)) (PreH8 : (h_3 <= 255)) (PreH9 : (h_3 >= 0)) (PreH10 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH11 : (r <> 0)) (PreH12 : (tr = (make_tree (tr1) (tr2)))) (PreH13 : (l <> 0)) (PreH14 : (retval < (-1))) (PreH15 : (retval <= 1)) (PreH16 : (retval = x)) (PreH17 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_4: tree)  (tr1_4: tree)  (h_6: Z)  (tr_4: tree)  (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (h_6 <= 255) ” 
  &&  “ (h_6 >= 0) ” 
  &&  “ (tr_4 = (make_tree (tr1_4) (tr2_4))) ” 
  &&  “ (r_3 <> 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (l_3 <> 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (retval_2 = x_2) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (store_tree_shape l )
  **  (store_non_empty_tree r )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_21 := balance_partial_solve_wit_21_pure -> balance_partial_solve_wit_21_aux.

Definition balance_partial_solve_wit_22_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ”
.

Definition balance_partial_solve_wit_22_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_22 := balance_partial_solve_wit_22_pure -> balance_partial_solve_wit_22_aux.

Definition balance_partial_solve_wit_23_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = x)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ”
.

Definition balance_partial_solve_wit_23_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (retval: Z) (tr: tree) (tr_2: tree) (h_2: Z) (tr1: tree) (tr2: tree) (k_2: Z) (v_2: Z) (h_3: Z) (l_2: Z) (r_2: Z) (x: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = x)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (tr_2 = (make_tree (tr1) (tr2)))) (PreH10 : (r <> 0)) (PreH11 : (retval < (-1))) (PreH12 : (retval <= 1)) (PreH13 : (retval <= 0)) (PreH14 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_non_empty_tree l_2 )
  **  (store_non_empty_tree r_2 )
  **  (store_tree l tr )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_4: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r_2 <> 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval_2 = x) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1) (tr2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_2 v_2 h_3 l_2 r_2 )
  **  (store_tree_shape l )
  **  (store_non_empty_tree l_2 )
  **  (store_tree_shape r_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_23 := balance_partial_solve_wit_23_pure -> balance_partial_solve_wit_23_aux.

Definition balance_partial_solve_wit_24_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ”
.

Definition balance_partial_solve_wit_24_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 >= 0)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_24 := balance_partial_solve_wit_24_pure -> balance_partial_solve_wit_24_aux.

Definition balance_partial_solve_wit_25_pure := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = x_2)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((( &( "rbf" ) )) # Int  |-> retval_2)
  **  ((( &( "bf" ) )) # Int  |-> retval)
  **  ((( &( "rh" ) )) # Int  |-> 0)
  **  ((( &( "lh" ) )) # Int  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ”
.

Definition balance_partial_solve_wit_25_aux := 
forall (p_pre: Z) (p_pre_v: Z) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (x: Z) (retval: Z) (tr: tree) (k_2: Z) (v_2: Z) (h_2: Z) (l_2: Z) (r_2: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_3: Z) (tr1_2: tree) (tr2_2: tree) (k_3: Z) (v_3: Z) (h_4: Z) (l_3: Z) (r_3: Z) (x_2: Z) (retval_2: Z) (PreH1 : (retval_2 > 0)) (PreH2 : (retval_2 >= 0)) (PreH3 : (retval_2 = x_2)) (PreH4 : (r <> 0)) (PreH5 : (h <= 255)) (PreH6 : (h >= 0)) (PreH7 : (h_2 <= 255)) (PreH8 : (h_2 >= 0)) (PreH9 : (h_3 <= 255)) (PreH10 : (h_3 >= 0)) (PreH11 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH12 : (r <> 0)) (PreH13 : (tr = (make_tree (tr1) (tr2)))) (PreH14 : (l <> 0)) (PreH15 : (retval < (-1))) (PreH16 : (retval <= 1)) (PreH17 : (retval = x)) (PreH18 : (p_pre_v <> 0)) ,
  (single_tree_node l k_2 v_2 h_2 l_2 r_2 )
  **  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_non_empty_tree l_3 )
  **  (store_non_empty_tree r_3 )
  **  (store_tree r_2 tr2 )
  **  (store_tree l_2 tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_3: tree)  (tr1_3: tree)  (h_5: Z)  (tr_3: tree) ,
  “ (p_pre_v <> 0) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h_4 <= 255) ” 
  &&  “ (h_4 >= 0) ” 
  &&  “ (h_5 <= 255) ” 
  &&  “ (h_5 >= 0) ” 
  &&  “ (tr_3 = (make_tree (tr1_3) (tr2_3))) ” 
  &&  “ (r_3 <> 0) ” 
  &&  “ (retval_2 > 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval_2 = x_2) ” 
  &&  “ (r <> 0) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (h_3 <= 255) ” 
  &&  “ (h_3 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (r <> 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (l <> 0) ” 
  &&  “ (retval < (-1)) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = x) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (single_tree_node p_pre_v k v h l r )
  **  (single_tree_node r k_3 v_3 h_4 l_3 r_3 )
  **  (store_tree_shape l )
  **  (store_non_empty_tree l_3 )
  **  (store_tree_shape r_3 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition balance_partial_solve_wit_25 := balance_partial_solve_wit_25_pure -> balance_partial_solve_wit_25_aux.

(*----- Function insert -----*)

Definition insert_safety_wit_1 := 
forall (value_pre: Z) (key_pre: Z) (p_pre: Z) (p_pre_v: Z) ,
  ((( &( "root" ) )) # Ptr  |-> p_pre_v)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "key" ) )) # Int  |-> key_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_2 := 
forall (value_pre: Z) (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v = 0)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> key_pre)
  **  ((&((retval)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "lchild")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "rchild")) # Ptr  |->_)
  **  ((( &( "root" ) )) # Ptr  |-> retval)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "key" ) )) # Int  |-> key_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_3 := 
forall (value_pre: Z) (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v = 0)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> key_pre)
  **  ((&((retval)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "lchild")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "rchild")) # Ptr  |->_)
  **  ((( &( "root" ) )) # Ptr  |-> retval)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "key" ) )) # Int  |-> key_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition insert_safety_wit_4 := 
forall (value_pre: Z) (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v = 0)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> key_pre)
  **  ((&((retval)  # "tree" ->ₛ "height")) # UChar  |->_)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "lchild")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "rchild")) # Ptr  |-> 0)
  **  ((( &( "root" ) )) # Ptr  |-> retval)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "key" ) )) # Int  |-> key_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition insert_return_wit_1 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v_2: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (key_pre <= k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v_2 <> 0)) ,
  (single_tree_node p_pre_v_2 k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v_2)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition insert_return_wit_2 := 
forall (value_pre: Z) (key_pre: Z) (p_pre: Z) (p_pre_v_2: Z) (tr: tree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = empty)) (PreH3 : (p_pre_v_2 = 0)) ,
  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> key_pre)
  **  ((&((retval)  # "tree" ->ₛ "height")) # UChar  |-> 1)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "lchild")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "rchild")) # Ptr  |-> 0)
  **  ((p_pre) # Ptr  |-> retval)
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition insert_return_wit_3 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v_2: Z) (tr: tree) (k: Z) (h: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_2: Z) (tr1_2: tree) (tr2_2: tree) (p_callee_v: Z) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (p_pre_v_2 <> 0)) (PreH5 : (key_pre < k)) (PreH6 : (h <= 255)) (PreH7 : (h >= 0)) (PreH8 : (tr = (make_tree (tr1) (tr2)))) (PreH9 : (p_pre_v_2 <> 0)) ,
  ((p_pre) # Ptr  |-> p_callee_v)
  **  (store_tree_shape p_callee_v )
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition insert_return_wit_4 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v_2: Z) (tr: tree) (k: Z) (h: Z) (tr1: tree) (tr2: tree) (tr_2: tree) (h_2: Z) (tr1_2: tree) (tr2_2: tree) (p_callee_v: Z) (PreH1 : (h_2 <= 255)) (PreH2 : (h_2 >= 0)) (PreH3 : (tr_2 = (make_tree (tr1_2) (tr2_2)))) (PreH4 : (p_pre_v_2 <> 0)) (PreH5 : (key_pre > k)) (PreH6 : (key_pre >= k)) (PreH7 : (h <= 255)) (PreH8 : (h >= 0)) (PreH9 : (tr = (make_tree (tr1) (tr2)))) (PreH10 : (p_pre_v_2 <> 0)) ,
  ((p_pre) # Ptr  |-> p_callee_v)
  **  (store_tree_shape p_callee_v )
|--
  EX (p_pre_v: Z) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition insert_partial_solve_wit_1 := 
forall (p_pre: Z) (p_pre_v: Z) (PreH1 : (p_pre_v = 0)) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
|--
  EX (tr: tree) ,
  “ (tr = empty) ” 
  &&  “ (p_pre_v = 0) ”
  &&  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_2 := 
forall (p_pre: Z) (p_pre_v: Z) (PreH1 : (p_pre_v <> 0)) ,
  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
|--
  EX (k: Z)  (tr2: tree)  (tr1: tree)  (r: Z)  (l: Z)  (h: Z)  (v: Z)  (tr: tree) ,
  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_3 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (key_pre < k)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (key_pre < k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  (store_tree_shape l )
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree r tr2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_4 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (key_pre >= k)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (key_pre >= k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_5 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (r: Z) (tr1: tree) (tr2: tree) (PreH1 : (key_pre > k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l r )
  **  (store_tree r tr2 )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (key_pre > k) ” 
  &&  “ (key_pre >= k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((&((p_pre_v)  # "tree" ->ₛ "rchild")) # Ptr  |-> r)
  **  (store_tree_shape r )
  **  ((&((p_pre_v)  # "tree" ->ₛ "lchild")) # Ptr  |-> l)
  **  ((&((p_pre_v)  # "tree" ->ₛ "height")) # UChar  |-> h)
  **  ((&((p_pre_v)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((p_pre_v)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_6 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (r: Z) (tr1: tree) (tr2: tree) (p_callee_v: Z) (PreH1 : (key_pre < k)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h p_callee_v r )
  **  (store_tree_shape p_callee_v )
  **  (store_tree r tr2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (key_pre < k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (store_non_empty_tree p_pre_v )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_7 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (v: Z) (h: Z) (l: Z) (tr1: tree) (tr2: tree) (p_callee_v: Z) (PreH1 : (key_pre > k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v <> 0)) ,
  (single_tree_node p_pre_v k v h l p_callee_v )
  **  (store_tree_shape p_callee_v )
  **  (store_tree l tr1 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  “ (key_pre > k) ” 
  &&  “ (key_pre >= k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  (store_non_empty_tree p_pre_v )
  **  ((p_pre) # Ptr  |-> p_pre_v)
.

Definition insert_partial_solve_wit_8 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (h: Z) (tr1: tree) (tr2: tree) (PreH1 : (key_pre < k)) (PreH2 : (h <= 255)) (PreH3 : (h >= 0)) (PreH4 : (tr = (make_tree (tr1) (tr2)))) (PreH5 : (p_pre_v <> 0)) ,
  (store_non_empty_tree p_pre_v )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_2: Z)  (tr_2: tree) ,
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (p_pre_v <> 0) ” 
  &&  “ (key_pre < k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Definition insert_partial_solve_wit_9 := 
forall (key_pre: Z) (p_pre: Z) (p_pre_v: Z) (tr: tree) (k: Z) (h: Z) (tr1: tree) (tr2: tree) (PreH1 : (key_pre > k)) (PreH2 : (key_pre >= k)) (PreH3 : (h <= 255)) (PreH4 : (h >= 0)) (PreH5 : (tr = (make_tree (tr1) (tr2)))) (PreH6 : (p_pre_v <> 0)) ,
  (store_non_empty_tree p_pre_v )
  **  ((p_pre) # Ptr  |-> p_pre_v)
|--
  EX (tr2_2: tree)  (tr1_2: tree)  (h_2: Z)  (tr_2: tree) ,
  “ (h_2 <= 255) ” 
  &&  “ (h_2 >= 0) ” 
  &&  “ (tr_2 = (make_tree (tr1_2) (tr2_2))) ” 
  &&  “ (p_pre_v <> 0) ” 
  &&  “ (key_pre > k) ” 
  &&  “ (key_pre >= k) ” 
  &&  “ (h <= 255) ” 
  &&  “ (h >= 0) ” 
  &&  “ (tr = (make_tree (tr1) (tr2))) ” 
  &&  “ (p_pre_v <> 0) ”
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (store_tree_shape p_pre_v )
.

Module Type VC_Correct.

Include avl_Strategy_Correct.

Axiom proof_of_update_height_safety_wit_1 : update_height_safety_wit_1.
Axiom proof_of_update_height_safety_wit_2 : update_height_safety_wit_2.
Axiom proof_of_update_height_safety_wit_3 : update_height_safety_wit_3.
Axiom proof_of_update_height_safety_wit_4 : update_height_safety_wit_4.
Axiom proof_of_update_height_safety_wit_5 : update_height_safety_wit_5.
Axiom proof_of_update_height_safety_wit_6 : update_height_safety_wit_6.
Axiom proof_of_update_height_safety_wit_7 : update_height_safety_wit_7.
Axiom proof_of_update_height_safety_wit_8 : update_height_safety_wit_8.
Axiom proof_of_update_height_safety_wit_9 : update_height_safety_wit_9.
Axiom proof_of_update_height_safety_wit_10 : update_height_safety_wit_10.
Axiom proof_of_update_height_safety_wit_11 : update_height_safety_wit_11.
Axiom proof_of_update_height_safety_wit_12 : update_height_safety_wit_12.
Axiom proof_of_update_height_safety_wit_13 : update_height_safety_wit_13.
Axiom proof_of_update_height_safety_wit_14 : update_height_safety_wit_14.
Axiom proof_of_update_height_safety_wit_15 : update_height_safety_wit_15.
Axiom proof_of_update_height_safety_wit_16 : update_height_safety_wit_16.
Axiom proof_of_update_height_safety_wit_17 : update_height_safety_wit_17.
Axiom proof_of_update_height_safety_wit_18 : update_height_safety_wit_18.
Axiom proof_of_update_height_return_wit_1 : update_height_return_wit_1.
Axiom proof_of_update_height_return_wit_2 : update_height_return_wit_2.
Axiom proof_of_update_height_return_wit_3 : update_height_return_wit_3.
Axiom proof_of_update_height_return_wit_4 : update_height_return_wit_4.
Axiom proof_of_update_height_return_wit_5 : update_height_return_wit_5.
Axiom proof_of_update_height_return_wit_6 : update_height_return_wit_6.
Axiom proof_of_update_height_partial_solve_wit_1 : update_height_partial_solve_wit_1.
Axiom proof_of_update_height_partial_solve_wit_2 : update_height_partial_solve_wit_2.
Axiom proof_of_update_height_partial_solve_wit_3 : update_height_partial_solve_wit_3.
Axiom proof_of_update_height_partial_solve_wit_4 : update_height_partial_solve_wit_4.
Axiom proof_of_update_height_partial_solve_wit_5 : update_height_partial_solve_wit_5.
Axiom proof_of_update_height_partial_solve_wit_6 : update_height_partial_solve_wit_6.
Axiom proof_of_update_height_partial_solve_wit_7 : update_height_partial_solve_wit_7.
Axiom proof_of_update_height_partial_solve_wit_8 : update_height_partial_solve_wit_8.
Axiom proof_of_update_height_partial_solve_wit_9 : update_height_partial_solve_wit_9.
Axiom proof_of_update_height_partial_solve_wit_10 : update_height_partial_solve_wit_10.
Axiom proof_of_update_height_partial_solve_wit_11 : update_height_partial_solve_wit_11.
Axiom proof_of_update_height_partial_solve_wit_12 : update_height_partial_solve_wit_12.
Axiom proof_of_update_height_partial_solve_wit_13 : update_height_partial_solve_wit_13.
Axiom proof_of_update_height_partial_solve_wit_14 : update_height_partial_solve_wit_14.
Axiom proof_of_update_height_partial_solve_wit_15 : update_height_partial_solve_wit_15.
Axiom proof_of_rotateR_return_wit_1 : rotateR_return_wit_1.
Axiom proof_of_rotateR_partial_solve_wit_1 : rotateR_partial_solve_wit_1.
Axiom proof_of_rotateR_partial_solve_wit_2 : rotateR_partial_solve_wit_2.
Axiom proof_of_rotateR_partial_solve_wit_3 : rotateR_partial_solve_wit_3.
Axiom proof_of_rotateR_partial_solve_wit_4 : rotateR_partial_solve_wit_4.
Axiom proof_of_rotateR_partial_solve_wit_5 : rotateR_partial_solve_wit_5.
Axiom proof_of_rotateR_partial_solve_wit_6 : rotateR_partial_solve_wit_6.
Axiom proof_of_rotateL_return_wit_1 : rotateL_return_wit_1.
Axiom proof_of_rotateL_partial_solve_wit_1 : rotateL_partial_solve_wit_1.
Axiom proof_of_rotateL_partial_solve_wit_2 : rotateL_partial_solve_wit_2.
Axiom proof_of_rotateL_partial_solve_wit_3 : rotateL_partial_solve_wit_3.
Axiom proof_of_rotateL_partial_solve_wit_4 : rotateL_partial_solve_wit_4.
Axiom proof_of_rotateL_partial_solve_wit_5 : rotateL_partial_solve_wit_5.
Axiom proof_of_rotateL_partial_solve_wit_6 : rotateL_partial_solve_wit_6.
Axiom proof_of_rotateRL_return_wit_1 : rotateRL_return_wit_1.
Axiom proof_of_rotateRL_partial_solve_wit_1 : rotateRL_partial_solve_wit_1.
Axiom proof_of_rotateRL_partial_solve_wit_2_pure : rotateRL_partial_solve_wit_2_pure.
Axiom proof_of_rotateRL_partial_solve_wit_2 : rotateRL_partial_solve_wit_2.
Axiom proof_of_rotateRL_partial_solve_wit_3 : rotateRL_partial_solve_wit_3.
Axiom proof_of_rotateRL_partial_solve_wit_4_pure : rotateRL_partial_solve_wit_4_pure.
Axiom proof_of_rotateRL_partial_solve_wit_4 : rotateRL_partial_solve_wit_4.
Axiom proof_of_rotateLR_return_wit_1 : rotateLR_return_wit_1.
Axiom proof_of_rotateLR_partial_solve_wit_1 : rotateLR_partial_solve_wit_1.
Axiom proof_of_rotateLR_partial_solve_wit_2_pure : rotateLR_partial_solve_wit_2_pure.
Axiom proof_of_rotateLR_partial_solve_wit_2 : rotateLR_partial_solve_wit_2.
Axiom proof_of_rotateLR_partial_solve_wit_3 : rotateLR_partial_solve_wit_3.
Axiom proof_of_rotateLR_partial_solve_wit_4_pure : rotateLR_partial_solve_wit_4_pure.
Axiom proof_of_rotateLR_partial_solve_wit_4 : rotateLR_partial_solve_wit_4.
Axiom proof_of_balance_factor_safety_wit_1 : balance_factor_safety_wit_1.
Axiom proof_of_balance_factor_safety_wit_2 : balance_factor_safety_wit_2.
Axiom proof_of_balance_factor_safety_wit_3 : balance_factor_safety_wit_3.
Axiom proof_of_balance_factor_safety_wit_4 : balance_factor_safety_wit_4.
Axiom proof_of_balance_factor_safety_wit_5 : balance_factor_safety_wit_5.
Axiom proof_of_balance_factor_safety_wit_6 : balance_factor_safety_wit_6.
Axiom proof_of_balance_factor_safety_wit_7 : balance_factor_safety_wit_7.
Axiom proof_of_balance_factor_safety_wit_8 : balance_factor_safety_wit_8.
Axiom proof_of_balance_factor_safety_wit_9 : balance_factor_safety_wit_9.
Axiom proof_of_balance_factor_safety_wit_10 : balance_factor_safety_wit_10.
Axiom proof_of_balance_factor_safety_wit_11 : balance_factor_safety_wit_11.
Axiom proof_of_balance_factor_return_wit_1 : balance_factor_return_wit_1.
Axiom proof_of_balance_factor_return_wit_2 : balance_factor_return_wit_2.
Axiom proof_of_balance_factor_return_wit_3 : balance_factor_return_wit_3.
Axiom proof_of_balance_factor_return_wit_4 : balance_factor_return_wit_4.
Axiom proof_of_balance_factor_return_wit_5 : balance_factor_return_wit_5.
Axiom proof_of_balance_factor_partial_solve_wit_1 : balance_factor_partial_solve_wit_1.
Axiom proof_of_balance_factor_partial_solve_wit_2 : balance_factor_partial_solve_wit_2.
Axiom proof_of_balance_factor_partial_solve_wit_3 : balance_factor_partial_solve_wit_3.
Axiom proof_of_balance_factor_partial_solve_wit_4 : balance_factor_partial_solve_wit_4.
Axiom proof_of_balance_factor_partial_solve_wit_5 : balance_factor_partial_solve_wit_5.
Axiom proof_of_balance_factor_partial_solve_wit_6 : balance_factor_partial_solve_wit_6.
Axiom proof_of_balance_factor_partial_solve_wit_7 : balance_factor_partial_solve_wit_7.
Axiom proof_of_balance_factor_partial_solve_wit_8 : balance_factor_partial_solve_wit_8.
Axiom proof_of_balance_factor_partial_solve_wit_9 : balance_factor_partial_solve_wit_9.
Axiom proof_of_balance_safety_wit_1 : balance_safety_wit_1.
Axiom proof_of_balance_safety_wit_2 : balance_safety_wit_2.
Axiom proof_of_balance_safety_wit_3 : balance_safety_wit_3.
Axiom proof_of_balance_safety_wit_4 : balance_safety_wit_4.
Axiom proof_of_balance_safety_wit_5 : balance_safety_wit_5.
Axiom proof_of_balance_safety_wit_6 : balance_safety_wit_6.
Axiom proof_of_balance_safety_wit_7 : balance_safety_wit_7.
Axiom proof_of_balance_safety_wit_8 : balance_safety_wit_8.
Axiom proof_of_balance_safety_wit_9 : balance_safety_wit_9.
Axiom proof_of_balance_safety_wit_10 : balance_safety_wit_10.
Axiom proof_of_balance_safety_wit_11 : balance_safety_wit_11.
Axiom proof_of_balance_safety_wit_12 : balance_safety_wit_12.
Axiom proof_of_balance_safety_wit_13 : balance_safety_wit_13.
Axiom proof_of_balance_safety_wit_14 : balance_safety_wit_14.
Axiom proof_of_balance_safety_wit_15 : balance_safety_wit_15.
Axiom proof_of_balance_safety_wit_16 : balance_safety_wit_16.
Axiom proof_of_balance_safety_wit_17 : balance_safety_wit_17.
Axiom proof_of_balance_safety_wit_18 : balance_safety_wit_18.
Axiom proof_of_balance_safety_wit_19 : balance_safety_wit_19.
Axiom proof_of_balance_safety_wit_20 : balance_safety_wit_20.
Axiom proof_of_balance_safety_wit_21 : balance_safety_wit_21.
Axiom proof_of_balance_safety_wit_22 : balance_safety_wit_22.
Axiom proof_of_balance_safety_wit_23 : balance_safety_wit_23.
Axiom proof_of_balance_safety_wit_24 : balance_safety_wit_24.
Axiom proof_of_balance_safety_wit_25 : balance_safety_wit_25.
Axiom proof_of_balance_safety_wit_26 : balance_safety_wit_26.
Axiom proof_of_balance_safety_wit_27 : balance_safety_wit_27.
Axiom proof_of_balance_safety_wit_28 : balance_safety_wit_28.
Axiom proof_of_balance_safety_wit_29 : balance_safety_wit_29.
Axiom proof_of_balance_safety_wit_30 : balance_safety_wit_30.
Axiom proof_of_balance_safety_wit_31 : balance_safety_wit_31.
Axiom proof_of_balance_safety_wit_32 : balance_safety_wit_32.
Axiom proof_of_balance_safety_wit_33 : balance_safety_wit_33.
Axiom proof_of_balance_safety_wit_34 : balance_safety_wit_34.
Axiom proof_of_balance_safety_wit_35 : balance_safety_wit_35.
Axiom proof_of_balance_safety_wit_36 : balance_safety_wit_36.
Axiom proof_of_balance_safety_wit_37 : balance_safety_wit_37.
Axiom proof_of_balance_safety_wit_38 : balance_safety_wit_38.
Axiom proof_of_balance_safety_wit_39 : balance_safety_wit_39.
Axiom proof_of_balance_safety_wit_40 : balance_safety_wit_40.
Axiom proof_of_balance_safety_wit_41 : balance_safety_wit_41.
Axiom proof_of_balance_safety_wit_42 : balance_safety_wit_42.
Axiom proof_of_balance_safety_wit_43 : balance_safety_wit_43.
Axiom proof_of_balance_safety_wit_44 : balance_safety_wit_44.
Axiom proof_of_balance_safety_wit_45 : balance_safety_wit_45.
Axiom proof_of_balance_safety_wit_46 : balance_safety_wit_46.
Axiom proof_of_balance_safety_wit_47 : balance_safety_wit_47.
Axiom proof_of_balance_safety_wit_48 : balance_safety_wit_48.
Axiom proof_of_balance_safety_wit_49 : balance_safety_wit_49.
Axiom proof_of_balance_safety_wit_50 : balance_safety_wit_50.
Axiom proof_of_balance_safety_wit_51 : balance_safety_wit_51.
Axiom proof_of_balance_safety_wit_52 : balance_safety_wit_52.
Axiom proof_of_balance_safety_wit_53 : balance_safety_wit_53.
Axiom proof_of_balance_safety_wit_54 : balance_safety_wit_54.
Axiom proof_of_balance_safety_wit_55 : balance_safety_wit_55.
Axiom proof_of_balance_safety_wit_56 : balance_safety_wit_56.
Axiom proof_of_balance_safety_wit_57 : balance_safety_wit_57.
Axiom proof_of_balance_safety_wit_58 : balance_safety_wit_58.
Axiom proof_of_balance_safety_wit_59 : balance_safety_wit_59.
Axiom proof_of_balance_safety_wit_60 : balance_safety_wit_60.
Axiom proof_of_balance_safety_wit_61 : balance_safety_wit_61.
Axiom proof_of_balance_safety_wit_62 : balance_safety_wit_62.
Axiom proof_of_balance_safety_wit_63 : balance_safety_wit_63.
Axiom proof_of_balance_safety_wit_64 : balance_safety_wit_64.
Axiom proof_of_balance_safety_wit_65 : balance_safety_wit_65.
Axiom proof_of_balance_safety_wit_66 : balance_safety_wit_66.
Axiom proof_of_balance_return_wit_1 : balance_return_wit_1.
Axiom proof_of_balance_return_wit_2 : balance_return_wit_2.
Axiom proof_of_balance_return_wit_3 : balance_return_wit_3.
Axiom proof_of_balance_return_wit_4 : balance_return_wit_4.
Axiom proof_of_balance_return_wit_5 : balance_return_wit_5.
Axiom proof_of_balance_return_wit_6 : balance_return_wit_6.
Axiom proof_of_balance_return_wit_7 : balance_return_wit_7.
Axiom proof_of_balance_return_wit_8 : balance_return_wit_8.
Axiom proof_of_balance_return_wit_9 : balance_return_wit_9.
Axiom proof_of_balance_return_wit_10 : balance_return_wit_10.
Axiom proof_of_balance_return_wit_11 : balance_return_wit_11.
Axiom proof_of_balance_return_wit_12 : balance_return_wit_12.
Axiom proof_of_balance_return_wit_13 : balance_return_wit_13.
Axiom proof_of_balance_return_wit_14 : balance_return_wit_14.
Axiom proof_of_balance_return_wit_15 : balance_return_wit_15.
Axiom proof_of_balance_return_wit_16 : balance_return_wit_16.
Axiom proof_of_balance_return_wit_17 : balance_return_wit_17.
Axiom proof_of_balance_return_wit_18 : balance_return_wit_18.
Axiom proof_of_balance_return_wit_19 : balance_return_wit_19.
Axiom proof_of_balance_return_wit_20 : balance_return_wit_20.
Axiom proof_of_balance_return_wit_21 : balance_return_wit_21.
Axiom proof_of_balance_return_wit_22 : balance_return_wit_22.
Axiom proof_of_balance_return_wit_23 : balance_return_wit_23.
Axiom proof_of_balance_return_wit_24 : balance_return_wit_24.
Axiom proof_of_balance_return_wit_25 : balance_return_wit_25.
Axiom proof_of_balance_return_wit_26 : balance_return_wit_26.
Axiom proof_of_balance_return_wit_27 : balance_return_wit_27.
Axiom proof_of_balance_return_wit_28 : balance_return_wit_28.
Axiom proof_of_balance_return_wit_29 : balance_return_wit_29.
Axiom proof_of_balance_return_wit_30 : balance_return_wit_30.
Axiom proof_of_balance_return_wit_31 : balance_return_wit_31.
Axiom proof_of_balance_return_wit_32 : balance_return_wit_32.
Axiom proof_of_balance_return_wit_33 : balance_return_wit_33.
Axiom proof_of_balance_return_wit_34 : balance_return_wit_34.
Axiom proof_of_balance_return_wit_35 : balance_return_wit_35.
Axiom proof_of_balance_return_wit_36 : balance_return_wit_36.
Axiom proof_of_balance_partial_solve_wit_1 : balance_partial_solve_wit_1.
Axiom proof_of_balance_partial_solve_wit_2 : balance_partial_solve_wit_2.
Axiom proof_of_balance_partial_solve_wit_3 : balance_partial_solve_wit_3.
Axiom proof_of_balance_partial_solve_wit_4 : balance_partial_solve_wit_4.
Axiom proof_of_balance_partial_solve_wit_5 : balance_partial_solve_wit_5.
Axiom proof_of_balance_partial_solve_wit_6_pure : balance_partial_solve_wit_6_pure.
Axiom proof_of_balance_partial_solve_wit_6 : balance_partial_solve_wit_6.
Axiom proof_of_balance_partial_solve_wit_7_pure : balance_partial_solve_wit_7_pure.
Axiom proof_of_balance_partial_solve_wit_7 : balance_partial_solve_wit_7.
Axiom proof_of_balance_partial_solve_wit_8_pure : balance_partial_solve_wit_8_pure.
Axiom proof_of_balance_partial_solve_wit_8 : balance_partial_solve_wit_8.
Axiom proof_of_balance_partial_solve_wit_9_pure : balance_partial_solve_wit_9_pure.
Axiom proof_of_balance_partial_solve_wit_9 : balance_partial_solve_wit_9.
Axiom proof_of_balance_partial_solve_wit_10_pure : balance_partial_solve_wit_10_pure.
Axiom proof_of_balance_partial_solve_wit_10 : balance_partial_solve_wit_10.
Axiom proof_of_balance_partial_solve_wit_11_pure : balance_partial_solve_wit_11_pure.
Axiom proof_of_balance_partial_solve_wit_11 : balance_partial_solve_wit_11.
Axiom proof_of_balance_partial_solve_wit_12_pure : balance_partial_solve_wit_12_pure.
Axiom proof_of_balance_partial_solve_wit_12 : balance_partial_solve_wit_12.
Axiom proof_of_balance_partial_solve_wit_13_pure : balance_partial_solve_wit_13_pure.
Axiom proof_of_balance_partial_solve_wit_13 : balance_partial_solve_wit_13.
Axiom proof_of_balance_partial_solve_wit_14 : balance_partial_solve_wit_14.
Axiom proof_of_balance_partial_solve_wit_15 : balance_partial_solve_wit_15.
Axiom proof_of_balance_partial_solve_wit_16 : balance_partial_solve_wit_16.
Axiom proof_of_balance_partial_solve_wit_17 : balance_partial_solve_wit_17.
Axiom proof_of_balance_partial_solve_wit_18_pure : balance_partial_solve_wit_18_pure.
Axiom proof_of_balance_partial_solve_wit_18 : balance_partial_solve_wit_18.
Axiom proof_of_balance_partial_solve_wit_19_pure : balance_partial_solve_wit_19_pure.
Axiom proof_of_balance_partial_solve_wit_19 : balance_partial_solve_wit_19.
Axiom proof_of_balance_partial_solve_wit_20_pure : balance_partial_solve_wit_20_pure.
Axiom proof_of_balance_partial_solve_wit_20 : balance_partial_solve_wit_20.
Axiom proof_of_balance_partial_solve_wit_21_pure : balance_partial_solve_wit_21_pure.
Axiom proof_of_balance_partial_solve_wit_21 : balance_partial_solve_wit_21.
Axiom proof_of_balance_partial_solve_wit_22_pure : balance_partial_solve_wit_22_pure.
Axiom proof_of_balance_partial_solve_wit_22 : balance_partial_solve_wit_22.
Axiom proof_of_balance_partial_solve_wit_23_pure : balance_partial_solve_wit_23_pure.
Axiom proof_of_balance_partial_solve_wit_23 : balance_partial_solve_wit_23.
Axiom proof_of_balance_partial_solve_wit_24_pure : balance_partial_solve_wit_24_pure.
Axiom proof_of_balance_partial_solve_wit_24 : balance_partial_solve_wit_24.
Axiom proof_of_balance_partial_solve_wit_25_pure : balance_partial_solve_wit_25_pure.
Axiom proof_of_balance_partial_solve_wit_25 : balance_partial_solve_wit_25.
Axiom proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Axiom proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Axiom proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Axiom proof_of_insert_safety_wit_4 : insert_safety_wit_4.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_return_wit_3 : insert_return_wit_3.
Axiom proof_of_insert_return_wit_4 : insert_return_wit_4.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Axiom proof_of_insert_partial_solve_wit_3 : insert_partial_solve_wit_3.
Axiom proof_of_insert_partial_solve_wit_4 : insert_partial_solve_wit_4.
Axiom proof_of_insert_partial_solve_wit_5 : insert_partial_solve_wit_5.
Axiom proof_of_insert_partial_solve_wit_6 : insert_partial_solve_wit_6.
Axiom proof_of_insert_partial_solve_wit_7 : insert_partial_solve_wit_7.
Axiom proof_of_insert_partial_solve_wit_8 : insert_partial_solve_wit_8.
Axiom proof_of_insert_partial_solve_wit_9 : insert_partial_solve_wit_9.

End VC_Correct.
