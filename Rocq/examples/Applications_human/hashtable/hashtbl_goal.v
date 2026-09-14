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
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_strategy_goal.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_strategy_proof.

(*----- Function create_bucks -----*)

Definition create_bucks_safety_wit_1 := 
forall (h_pre: Z) (content: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bucket_cells_nonnull retval )) ,
  (PtrArray.full retval 211 content )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition create_bucks_safety_wit_2 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 211)) (PreH3 : (bucket_cells_nonnull bucks_base )) (PreH4 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH5 : (retval <> 0)) (PreH6 : (bucket_cells_nonnull retval )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition create_bucks_safety_wit_3 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) (PreH1 : (i < 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base )) (PreH5 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition create_bucks_safety_wit_4 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) (PreH1 : (i < 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base )) (PreH5 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  (PtrArray.full bucks_base 211 (replace_Znth (i) (0) (content)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition create_bucks_entail_wit_1 := 
(
forall (h_pre: Z) (content_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bucket_cells_nonnull retval )) ,
  (PtrArray.full retval 211 content_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> retval)
|--
  EX (content: (@list Z))  (bucks_base: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 211) ” 
  &&  “ (bucket_cells_nonnull bucks_base ) ” 
  &&  “ ((sublist (0) (0) (content)) = (zeros (0))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (bucket_cells_nonnull retval ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
) \/
(
forall (content_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bucket_cells_nonnull retval )) ,
  TT && emp 
|--
  “ ((sublist (0) (0) (content_2)) = (zeros (0))) ”
  &&  emp
).

Definition create_bucks_entail_wit_1_split_goal_1 := 
forall (content_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (bucket_cells_nonnull retval )) ,
  ((sublist (0) (0) (content_2)) = (zeros (0)))
.

Definition create_bucks_entail_wit_2 := 
(
forall (h_pre: Z) (retval: Z) (content_2: (@list Z)) (bucks_base_2: Z) (i: Z) (PreH1 : (i < 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base_2 )) (PreH5 : ((sublist (0) (i) (content_2)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  (PtrArray.full bucks_base_2 211 (replace_Znth (i) (0) (content_2)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base_2)
|--
  EX (content: (@list Z))  (bucks_base: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 211) ” 
  &&  “ (bucket_cells_nonnull bucks_base ) ” 
  &&  “ ((sublist (0) ((i + 1 )) (content)) = (zeros ((i + 1 )))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (bucket_cells_nonnull retval ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
) \/
(
forall (retval: Z) (content_2: (@list Z)) (bucks_base_2: Z) (i: Z) (PreH1 : (i < 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base_2 )) (PreH5 : ((sublist (0) (i) (content_2)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  TT && emp 
|--
  “ ((sublist (0) ((i + 1 )) ((replace_Znth (i) (0) (content_2)))) = (zeros ((i + 1 )))) ”
  &&  emp
).

Definition create_bucks_entail_wit_2_split_goal_1 := 
forall (retval: Z) (content_2: (@list Z)) (bucks_base_2: Z) (i: Z) (PreH1 : (i < 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base_2 )) (PreH5 : ((sublist (0) (i) (content_2)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  ((sublist (0) ((i + 1 )) ((replace_Znth (i) (0) (content_2)))) = (zeros ((i + 1 ))))
.

Definition create_bucks_return_wit_1 := 
(
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base_2: Z) (i: Z) (PreH1 : (i >= 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base_2 )) (PreH5 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base_2)
  **  (PtrArray.full bucks_base_2 211 content )
|--
  EX (bucks_base: Z) ,
  “ (bucket_cells_nonnull bucks_base ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 (zeros (211)) )
) \/
(
forall (retval: Z) (content: (@list Z)) (bucks_base_2: Z) (i: Z) (PreH1 : (i >= 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base_2 )) (PreH5 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  TT && emp 
|--
  “ (content = (zeros (211))) ”
  &&  emp
).

Definition create_bucks_return_wit_1_split_goal_1 := 
forall (retval: Z) (content: (@list Z)) (bucks_base_2: Z) (i: Z) (PreH1 : (i >= 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base_2 )) (PreH5 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  (content = (zeros (211)))
.

Definition create_bucks_partial_solve_wit_1 := 
forall (h_pre: Z) (bucks_random: Z) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_random)
|--
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_random)
.

Definition create_bucks_partial_solve_wit_2 := 
forall (h_pre: Z) (retval: Z) (content: (@list Z)) (bucks_base: Z) (i: Z) (PreH1 : (i < 211)) (PreH2 : (0 <= i)) (PreH3 : (i <= 211)) (PreH4 : (bucket_cells_nonnull bucks_base )) (PreH5 : ((sublist (0) (i) (content)) = (zeros (i)))) (PreH6 : (retval <> 0)) (PreH7 : (bucket_cells_nonnull retval )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 content )
|--
  “ (i < 211) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 211) ” 
  &&  “ (bucket_cells_nonnull bucks_base ) ” 
  &&  “ ((sublist (0) (i) (content)) = (zeros (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (bucket_cells_nonnull retval ) ”
  &&  (((bucks_base + (i * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_base i 0 211 content )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
.

(*----- Function init_hashtbl -----*)

Definition init_hashtbl_safety_wit_1 := 
forall (h_pre: Z) (top_ph: Z) (bucks_ph: Z) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition init_hashtbl_safety_wit_2 := 
forall (h_pre: Z) (top_ph: Z) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition init_hashtbl_return_wit_1 := 
(
forall (h_pre: Z) (bucks_base: Z) (PreH1 : (bucket_cells_nonnull bucks_base )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 (zeros (211)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  (store_hash_skeleton h_pre empty_map )
) \/
(
forall (h_pre: Z) (bucks_base: Z) (PreH1 : (bucket_cells_nonnull bucks_base )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 (zeros (211)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  (store_hash_skeleton h_pre empty_map )
).

Definition init_hashtbl_return_wit_1_split_goal_spatial := 
forall (h_pre: Z) (bucks_base: Z) (PreH1 : (bucket_cells_nonnull bucks_base )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_base)
  **  (PtrArray.full bucks_base 211 (zeros (211)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  (store_hash_skeleton h_pre empty_map )
.

Definition init_hashtbl_partial_solve_wit_1 := 
forall (h_pre: Z) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
|--
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
.

(*----- Function create_hashtbl -----*)

Definition create_hashtbl_entail_wit_1 := 
forall (top_ph_2: Z) (bucks_ph_2: Z) (retval: Z) (PreH1 : (retval <> 0)) ,
  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
|--
  EX (top_ph: Z)  (bucks_ph: Z) ,
  “ (retval <> 0) ”
  &&  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
.

Definition create_hashtbl_return_wit_1 := 
(
forall (retval: Z) (PreH1 : (retval <> 0)) ,
  (store_hash_skeleton retval empty_map )
|--
  (store_hash_skeleton retval empty_map )
  **  (store_map store_uint empty_map )
) \/
(
forall (retval: Z) (PreH1 : (retval <> 0)) ,
  (store_hash_skeleton retval empty_map )
|--
  (store_hash_skeleton retval empty_map )
  **  (store_map store_uint empty_map )
).

Definition create_hashtbl_return_wit_1_split_goal_spatial := 
forall (retval: Z) (PreH1 : (retval <> 0)) ,
  (store_hash_skeleton retval empty_map )
|--
  (store_hash_skeleton retval empty_map )
  **  (store_map store_uint empty_map )
.

Definition create_hashtbl_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition create_hashtbl_partial_solve_wit_2 := 
forall (retval: Z) (top_ph: Z) (bucks_ph: Z) (PreH1 : (retval <> 0)) ,
  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
|--
  “ (retval <> 0) ”
  &&  ((&((retval)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  ((&((retval)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
.

(*----- Function hashtbl_add -----*)

Definition hashtbl_add_safety_wit_1 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : ((m1 (k)) = None)) ,
  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  (store_map store_uint m2 )
|--
  “ (211 <> 0) ”
.

Definition hashtbl_add_safety_wit_2 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : ((m1 (k)) = None)) ,
  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  (store_map store_uint m2 )
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition hashtbl_add_safety_wit_3 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH3 : (0 <= (retval % ( 211 ) ))) (PreH4 : ((retval % ( 211 ) ) < 211)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (retval = (hash_string_k (k)))) (PreH8 : (node_value_map m_node m1 )) (PreH9 : (contain_all_addrs m_node l )) (PreH10 : (repr_all_heads lh b )) (PreH11 : (contain_all_correct_addrs m_node b )) (PreH12 : (bucket_cells_nonnull bucks_ph )) (PreH13 : ((m1 (k)) = None)) ,
  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((( &( "ind" ) )) # UInt  |-> (retval % ( 211 ) ))
  **  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |-> retval_2)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_add_safety_wit_4 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH3 : (0 <= (retval % ( 211 ) ))) (PreH4 : ((retval % ( 211 ) ) < 211)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (retval = (hash_string_k (k)))) (PreH8 : (node_value_map m_node m1 )) (PreH9 : (contain_all_addrs m_node l )) (PreH10 : (repr_all_heads lh b )) (PreH11 : (contain_all_correct_addrs m_node b )) (PreH12 : (bucket_cells_nonnull bucks_ph )) (PreH13 : ((m1 (k)) = None)) ,
  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((( &( "ind" ) )) # UInt  |-> (retval % ( 211 ) ))
  **  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |-> retval_2)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_add_entail_wit_1 := 
(
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : ((m1 (k)) = None)) ,
  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
) \/
(
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : ((m1 (k)) = None)) ,
  TT && emp 
|--
  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ”
  &&  emp
).

Definition hashtbl_add_entail_wit_1_split_goal_1 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : ((m1 (k)) = None)) ,
  ((retval % ( 211 ) ) < 211)
.

Definition hashtbl_add_entail_wit_1_split_goal_2 := 
forall (k: (@list Z)) (m1: ((@list Z) -> (@option Z))) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : ((m1 (k)) = None)) ,
  (0 <= (retval % ( 211 ) ))
.

Definition hashtbl_add_return_wit_1 := 
(
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (top_ph = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH4 : (0 <= (retval % ( 211 ) ))) (PreH5 : ((retval % ( 211 ) ) < 211)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval = (hash_string_k (k)))) (PreH9 : (node_value_map m_node m1 )) (PreH10 : (contain_all_addrs m_node l )) (PreH11 : (repr_all_heads lh b )) (PreH12 : (contain_all_correct_addrs m_node b )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : ((m1 (k)) = None)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  EX (p: Z) ,
  (store_hash_skeleton h_pre (KP.insert_map (m1) (k) (&((p)  # "blist" ->ₛ "val"))) )
  **  (store_map store_uint (PV.insert_map (m2) (&((p)  # "blist" ->ₛ "val")) (val_pre)) )
) \/
(
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (val_pre <= UINT_MAX)) (PreH2 : (val_pre >= 0)) (PreH3 : (top_ph = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH6 : (0 <= (retval % ( 211 ) ))) (PreH7 : ((retval % ( 211 ) ) < 211)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= UINT_MAX)) (PreH10 : (retval = (hash_string_k (k)))) (PreH11 : (node_value_map m_node m1 )) (PreH12 : (contain_all_addrs m_node l )) (PreH13 : (repr_all_heads lh b )) (PreH14 : (contain_all_correct_addrs m_node b )) (PreH15 : (bucket_cells_nonnull bucks_ph )) (PreH16 : ((m1 (k)) = None)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  EX (p: Z) ,
  (store_hash_skeleton h_pre (KP.insert_map (m1) (k) (&((p)  # "blist" ->ₛ "val"))) )
  **  (store_map store_uint (PV.insert_map (m2) (&((p)  # "blist" ->ₛ "val")) (val_pre)) )
).

Definition hashtbl_add_return_wit_2 := 
(
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) (PreH1 : (l = (cons (top_ph) (l_tail)))) (PreH2 : (top_ph <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH5 : (0 <= (retval % ( 211 ) ))) (PreH6 : ((retval % ( 211 ) ) < 211)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= UINT_MAX)) (PreH9 : (retval = (hash_string_k (k)))) (PreH10 : (node_value_map m_node m1 )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b )) (PreH13 : (contain_all_correct_addrs m_node b )) (PreH14 : (bucket_cells_nonnull bucks_ph )) (PreH15 : ((m1 (k)) = None)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (dll top_down top_ph l_tail )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  EX (p: Z) ,
  (store_hash_skeleton h_pre (KP.insert_map (m1) (k) (&((p)  # "blist" ->ₛ "val"))) )
  **  (store_map store_uint (PV.insert_map (m2) (&((p)  # "blist" ->ₛ "val")) (val_pre)) )
) \/
(
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) (PreH1 : (val_pre <= UINT_MAX)) (PreH2 : (val_pre >= 0)) (PreH3 : (l = (cons (top_ph) (l_tail)))) (PreH4 : (top_ph <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH7 : (0 <= (retval % ( 211 ) ))) (PreH8 : ((retval % ( 211 ) ) < 211)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= UINT_MAX)) (PreH11 : (retval = (hash_string_k (k)))) (PreH12 : (node_value_map m_node m1 )) (PreH13 : (contain_all_addrs m_node l )) (PreH14 : (repr_all_heads lh b )) (PreH15 : (contain_all_correct_addrs m_node b )) (PreH16 : (bucket_cells_nonnull bucks_ph )) (PreH17 : ((m1 (k)) = None)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth ((retval % ( 211 ) )) (retval_2) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (dll top_down top_ph l_tail )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  EX (p: Z) ,
  (store_hash_skeleton h_pre (KP.insert_map (m1) (k) (&((p)  # "blist" ->ₛ "val"))) )
  **  (store_map store_uint (PV.insert_map (m2) (&((p)  # "blist" ->ₛ "val")) (val_pre)) )
).

Definition hashtbl_add_partial_solve_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (PreH1 : ((m1 (k)) = None)) ,
  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
|--
  “ ((m1 (k)) = None) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
.

Definition hashtbl_add_partial_solve_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m_node m1 )) (PreH2 : (contain_all_addrs m_node l )) (PreH3 : (repr_all_heads lh b )) (PreH4 : (contain_all_correct_addrs m_node b )) (PreH5 : (bucket_cells_nonnull bucks_ph )) (PreH6 : ((m1 (k)) = None)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
|--
  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_partial_solve_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= (retval % ( 211 ) ))) (PreH2 : ((retval % ( 211 ) ) < 211)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval = (hash_string_k (k)))) (PreH6 : (node_value_map m_node m1 )) (PreH7 : (contain_all_addrs m_node l )) (PreH8 : (repr_all_heads lh b )) (PreH9 : (contain_all_correct_addrs m_node b )) (PreH10 : (bucket_cells_nonnull bucks_ph )) (PreH11 : ((m1 (k)) = None)) ,
  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_partial_solve_wit_4_pure := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (top_ph <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH4 : (0 <= (retval % ( 211 ) ))) (PreH5 : ((retval % ( 211 ) ) < 211)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval = (hash_string_k (k)))) (PreH9 : (node_value_map m_node m1 )) (PreH10 : (contain_all_addrs m_node l )) (PreH11 : (repr_all_heads lh b )) (PreH12 : (contain_all_correct_addrs m_node b )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : ((m1 (k)) = None)) ,
  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((( &( "ind" ) )) # UInt  |-> (retval % ( 211 ) ))
  **  (store_string key_pre k )
  **  ((( &( "buc" ) )) # Ptr  |-> retval_2)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "val" ) )) # UInt  |-> val_pre)
  **  (store_map store_uint m2 )
|--
  “ (top_ph <> 0) ”
.

Definition hashtbl_add_partial_solve_wit_4_aux := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (top_ph <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH4 : (0 <= (retval % ( 211 ) ))) (PreH5 : ((retval % ( 211 ) ) < 211)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval = (hash_string_k (k)))) (PreH9 : (node_value_map m_node m1 )) (PreH10 : (contain_all_addrs m_node l )) (PreH11 : (repr_all_heads lh b )) (PreH12 : (contain_all_correct_addrs m_node b )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : ((m1 (k)) = None)) ,
  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (top_ph <> 0) ” 
  &&  “ (top_ph <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (&((retval_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  (dll top_ph 0 l )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_partial_solve_wit_4 := hashtbl_add_partial_solve_wit_4_pure -> hashtbl_add_partial_solve_wit_4_aux.

Definition hashtbl_add_partial_solve_wit_5 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) (PreH1 : (l = (cons (top_ph) (l_tail)))) (PreH2 : (top_ph <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH5 : (0 <= (retval % ( 211 ) ))) (PreH6 : ((retval % ( 211 ) ) < 211)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= UINT_MAX)) (PreH9 : (retval = (hash_string_k (k)))) (PreH10 : (node_value_map m_node m1 )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b )) (PreH13 : (contain_all_correct_addrs m_node b )) (PreH14 : (bucket_cells_nonnull bucks_ph )) (PreH15 : ((m1 (k)) = None)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (dll top_down top_ph l_tail )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (l = (cons (top_ph) (l_tail))) ” 
  &&  “ (top_ph <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (&((retval_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (dll top_down top_ph l_tail )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_partial_solve_wit_6 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (top_ph = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH4 : (0 <= (retval % ( 211 ) ))) (PreH5 : ((retval % ( 211 ) ) < 211)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval = (hash_string_k (k)))) (PreH9 : (node_value_map m_node m1 )) (PreH10 : (contain_all_addrs m_node l )) (PreH11 : (repr_all_heads lh b )) (PreH12 : (contain_all_correct_addrs m_node b )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : ((m1 (k)) = None)) ,
  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (top_ph = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (&((retval_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_partial_solve_wit_7 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (PreH1 : (top_ph = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH4 : (0 <= (retval % ( 211 ) ))) (PreH5 : ((retval % ( 211 ) ) < 211)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval = (hash_string_k (k)))) (PreH9 : (node_value_map m_node m1 )) (PreH10 : (contain_all_addrs m_node l )) (PreH11 : (repr_all_heads lh b )) (PreH12 : (contain_all_correct_addrs m_node b )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : ((m1 (k)) = None)) ,
  (PtrArray.full bucks_ph 211 lh )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (top_ph = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (&((retval_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_partial_solve_wit_8 := 
forall (val_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_ph: Z) (bucks_ph: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (retval_2: Z) (top_down: Z) (l_tail: (@list Z)) (PreH1 : (l = (cons (top_ph) (l_tail)))) (PreH2 : (top_ph <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (&((retval_2)  # "blist" ->ₛ "next") <> 0)) (PreH5 : (0 <= (retval % ( 211 ) ))) (PreH6 : ((retval % ( 211 ) ) < 211)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= UINT_MAX)) (PreH9 : (retval = (hash_string_k (k)))) (PreH10 : (node_value_map m_node m1 )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b )) (PreH13 : (contain_all_correct_addrs m_node b )) (PreH14 : (bucket_cells_nonnull bucks_ph )) (PreH15 : ((m1 (k)) = None)) ,
  (PtrArray.full bucks_ph 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (dll top_down top_ph l_tail )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
|--
  “ (l = (cons (top_ph) (l_tail))) ” 
  &&  “ (top_ph <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (&((retval_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((m1 (k)) = None) ”
  &&  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> retval_2)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> retval_2)
  **  (dll top_down top_ph l_tail )
  **  ((&((retval_2)  # "blist" ->ₛ "key")) # Ptr  |-> key_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "val")) # UInt  |-> val_pre)
  **  ((&((retval_2)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth (retval % ( 211 ) ) lh 0))
  **  ((&((retval_2)  # "blist" ->ₛ "down")) # Ptr  |-> top_ph)
  **  ((&((retval_2)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
.

Definition hashtbl_add_which_implies_wit_1 := 
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (top_ph: Z)  (bucks_ph: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
) \/
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (top_ph: Z)  (bucks_ph: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
).

Definition hashtbl_add_which_implies_wit_2 := 
(
forall (l: (@list Z)) (top_ph: Z) (h: Z) (PreH1 : (top_ph <> 0)) ,
  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  (dll top_ph 0 l )
|--
  EX (top_down: Z)  (l_tail: (@list Z)) ,
  “ (l = (cons (top_ph) (l_tail))) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (dll top_down top_ph l_tail )
) \/
(
forall (l: (@list Z)) (top_ph: Z) (PreH1 : (top_ph <> 0)) ,
  (dll top_ph 0 l )
|--
  EX (top_down: Z)  (l_tail: (@list Z)) ,
  “ (l = (cons (top_ph) (l_tail))) ”
  &&  ((&((top_ph)  # "blist" ->ₛ "down")) # Ptr  |-> top_down)
  **  ((&((top_ph)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (dll top_down top_ph l_tail )
).

(*----- Function hashtbl_find -----*)

Definition hashtbl_find_safety_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  “ (211 <> 0) ”
.

Definition hashtbl_find_safety_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition hashtbl_find_safety_wit_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (0 <= ind)) (PreH2 : (ind < 211)) (PreH3 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH4 : (map_composable m1 m2 )) (PreH5 : (node_value_map m_node m1 )) (PreH6 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH7 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH8 : (contain_all_addrs m_node l )) (PreH9 : (repr_all_heads lh b )) (PreH10 : (contain_all_correct_addrs m_node b )) (PreH11 : (not_key k l1 m_node )) (PreH12 : (bucket_cells_nonnull bucks_ph )) (PreH13 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_find_safety_wit_4 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval = 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ False ”
.

Definition hashtbl_find_safety_wit_5 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ False ”
.

Definition hashtbl_find_safety_wit_6 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ False ”
.

Definition hashtbl_find_safety_wit_7 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ False ”
.

Definition hashtbl_find_safety_wit_8 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (i_v) ((replace_Znth (ind) (p_next) (lh)))) )
  **  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_find_safety_wit_9 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (i_v) ((replace_Znth (ind) (h_val) (lh)))) )
  **  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (h_val) (lh)) 0))
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_find_safety_wit_10 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v = 0)) (PreH2 : (0 <= ind)) (PreH3 : (ind < 211)) (PreH4 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH5 : (map_composable m1 m2 )) (PreH6 : (node_value_map m_node m1 )) (PreH7 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH8 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH9 : (contain_all_addrs m_node l )) (PreH10 : (repr_all_heads lh b )) (PreH11 : (contain_all_correct_addrs m_node b )) (PreH12 : (not_key k l1 m_node )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_find_safety_wit_11 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v = 0)) (PreH2 : (0 <= ind)) (PreH3 : (ind < 211)) (PreH4 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH5 : (map_composable m1 m2 )) (PreH6 : (node_value_map m_node m1 )) (PreH7 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH8 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH9 : (contain_all_addrs m_node l )) (PreH10 : (repr_all_heads lh b )) (PreH11 : (contain_all_correct_addrs m_node b )) (PreH12 : (not_key k l1 m_node )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "valid" ) )) # Ptr  |-> valid_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_find_entail_wit_1 := 
(
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval = (hash_string_k (k))) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (map_composable m1 m2 ) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
) \/
(
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : (map_composable m1 m2 )) ,
  TT && emp 
|--
  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ”
  &&  emp
).

Definition hashtbl_find_entail_wit_1_split_goal_1 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : (map_composable m1 m2 )) ,
  ((retval % ( 211 ) ) < 211)
.

Definition hashtbl_find_entail_wit_1_split_goal_2 := 
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m1 )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m_node b )) (PreH8 : (bucket_cells_nonnull bucks_ph )) (PreH9 : (map_composable m1 m2 )) ,
  (0 <= (retval % ( 211 ) ))
.

Definition hashtbl_find_entail_wit_2 := 
(
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (bucks_ph: Z) (top_ph_2: Z) (m_node_2: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= (retval % ( 211 ) ))) (PreH2 : ((retval % ( 211 ) ) < 211)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval = (hash_string_k (k)))) (PreH6 : (node_value_map m_node_2 m1 )) (PreH7 : (contain_all_addrs m_node_2 l_2 )) (PreH8 : (repr_all_heads lh_2 b_2 )) (PreH9 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH10 : (bucket_cells_nonnull bucks_ph )) (PreH11 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.full bucks_ph 211 lh_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m_node_2 )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
|--
  EX (i_v: Z)  (l1: (@list Z))  (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph_2: Z)  (top_ph: Z)  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ ((b ((retval % ( 211 ) ))) = (Some ((pair ((Znth ((retval % ( 211 ) )) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth ((retval % ( 211 ) )) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph_2 ) ” 
  &&  “ ((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph_2 (retval % ( 211 ) ) 0 211 lh )
  **  (store_map_missing_i store_sll b (retval % ( 211 ) ) )
  **  (store_map store_name m_node )
  **  (sllbseg (bucks_ph_2 + ((retval % ( 211 ) ) * sizeof(PTR))) (bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR))) l1 )
  **  (((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (bucks_ph: Z) (top_ph_2: Z) (m_node_2: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= (retval % ( 211 ) ))) (PreH2 : ((retval % ( 211 ) ) < 211)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval = (hash_string_k (k)))) (PreH6 : (node_value_map m_node_2 m1 )) (PreH7 : (contain_all_addrs m_node_2 l_2 )) (PreH8 : (repr_all_heads lh_2 b_2 )) (PreH9 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH10 : (bucket_cells_nonnull bucks_ph )) (PreH11 : (map_composable m1 m2 )) ,
  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh_2 )
  **  (store_string key_pre k )
  **  (dll top_ph_2 0 l_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m_node_2 )
  **  (store_map store_uint m2 )
|--
  EX (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ ((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ ((b ((retval % ( 211 ) ))) = (Some ((pair ((Znth ((retval % ( 211 ) )) (lh) (0))) ((app ((@nil Z)) (l2))))))) ” 
  &&  “ ((Znth (0) ((app ((@nil Z)) (l2))) (0)) = (Znth ((retval % ( 211 ) )) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k (@nil Z) m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ ((bucks_ph + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ”
  &&  (dll top_ph_2 0 l )
  **  (PtrArray.missing_i bucks_ph (retval % ( 211 ) ) 0 211 lh )
  **  (store_map_missing_i store_sll b (retval % ( 211 ) ) )
  **  (store_map store_name m_node )
  **  (sll (Znth (retval % ( 211 ) ) lh_2 0) l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
).

Definition hashtbl_find_entail_wit_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i_v_3: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (lh_2: (@list Z)) (l_2: (@list Z)) (bucks_ph_2: Z) (top_ph_2: Z) (m_node_2: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v_3 <> 0)) (PreH2 : (0 <= ind)) (PreH3 : (ind < 211)) (PreH4 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH5 : (map_composable m1 m2 )) (PreH6 : (node_value_map m_node_2 m1 )) (PreH7 : ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2)))))))) (PreH8 : ((Znth (0) ((app (l1_2) (l2_2))) (0)) = (Znth (ind) (lh_2) (0)))) (PreH9 : (contain_all_addrs m_node_2 l_2 )) (PreH10 : (repr_all_heads lh_2 b_2 )) (PreH11 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH12 : (not_key k l1_2 m_node_2 )) (PreH13 : (bucket_cells_nonnull bucks_ph_2 )) (PreH14 : (i <> 0)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.missing_i bucks_ph_2 ind 0 211 lh_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (store_map store_name m_node_2 )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR))) i l1_2 )
  **  ((i) # Ptr  |-> i_v_3)
  **  (sll i_v_3 l2_2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  (EX (p_next: Z)  (kp: Z)  (vp: Z)  (h_val: Z)  (t_l1: (@list Z))  (l1: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (k_cur: (@list Z))  (i_v: Z)  (l_tail: (@list Z))  (l2: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ”
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
  ||
  (EX (p_next: Z)  (kp: Z)  (vp: Z)  (l1: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (k_cur: (@list Z))  (i_v_2: Z)  (l_tail: (@list Z))  (l2: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ”
  &&  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_4_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval = 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval = 0) ” 
  &&  “ (k <> k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval = 0) ”
  &&  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_entail_wit_4_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval_3 = 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (k <> k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval = 0) ”
  &&  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z)  (i_v_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (k <> k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_4_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v_2) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v_2)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval_2 = 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval_2 = 0) ” 
  &&  “ (k <> k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_entail_wit_4_4 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v_2) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v_2)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval_3 = 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  (EX (retval: Z)  (h_val: Z)  (t_l1: (@list Z))  (i_v: Z) ,
  “ (retval = 0) ” 
  &&  “ (k <> k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval = 0) ”
  &&  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (k <> k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval_3 <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z)  (i_v_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_entail_wit_5_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v_2) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v_2)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval_3 <> 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  (EX (retval: Z)  (h_val: Z)  (t_l1: (@list Z))  (i_v: Z) ,
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail ))
.

Definition hashtbl_find_entail_wit_5_4 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v_2) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v_2)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval_2 <> 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval_2 = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v_2) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v_2))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_entail_wit_6_1 := 
(
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node_2: ((@list Z) -> (@option Z))) (l1_2: (@list Z)) (l2_2: (@list Z)) (top_ph_2: Z) (bucks_ph_2: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node_2 m1 )) (PreH8 : (l2_2 = (cons (i_v_2) (l_tail)))) (PreH9 : ((m_node_2 (k_cur)) = (Some (i_v_2)))) (PreH10 : ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2)))))))) (PreH11 : ((Znth (0) ((app (l1_2) (l2_2))) (0)) = (Znth (ind) (lh_2) (0)))) (PreH12 : (l1_2 <> (@nil Z))) (PreH13 : (l1_2 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh_2) (0)))) (PreH15 : (contain_all_addrs m_node_2 l_2 )) (PreH16 : (repr_all_heads lh_2 b_2 )) (PreH17 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH18 : (not_key k l1_2 m_node_2 )) (PreH19 : (bucket_cells_nonnull bucks_ph_2 )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval = 0)) ,
  (PtrArray.full bucks_ph_2 211 (replace_Znth (ind) (h_val) (lh_2)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph_2 0 l_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node_2 k_cur )
  **  (sll p_next l_tail )
|--
  EX (i_v: Z)  (l1: (@list Z))  (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) &((i_v_2)  # "blist" ->ₛ "next") l1 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node_2: ((@list Z) -> (@option Z))) (l1_2: (@list Z)) (l2_2: (@list Z)) (top_ph_2: Z) (bucks_ph_2: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval: Z) (PreH1 : (vp <= UINT_MAX)) (PreH2 : (vp >= 0)) (PreH3 : (retval = 0)) (PreH4 : (k <> k_cur)) (PreH5 : (0 <= ind)) (PreH6 : (ind < 211)) (PreH7 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH8 : (map_composable m1 m2 )) (PreH9 : (node_value_map m_node_2 m1 )) (PreH10 : (l2_2 = (cons (i_v_2) (l_tail)))) (PreH11 : ((m_node_2 (k_cur)) = (Some (i_v_2)))) (PreH12 : ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2)))))))) (PreH13 : ((Znth (0) ((app (l1_2) (l2_2))) (0)) = (Znth (ind) (lh_2) (0)))) (PreH14 : (l1_2 <> (@nil Z))) (PreH15 : (l1_2 = (cons (h_val) (t_l1)))) (PreH16 : (h_val = (Znth (ind) (lh_2) (0)))) (PreH17 : (contain_all_addrs m_node_2 l_2 )) (PreH18 : (repr_all_heads lh_2 b_2 )) (PreH19 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH20 : (not_key k l1_2 m_node_2 )) (PreH21 : (bucket_cells_nonnull bucks_ph_2 )) (PreH22 : (i <> 0)) (PreH23 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH24 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH25 : (retval = 0)) ,
  (PtrArray.full bucks_ph_2 211 (replace_Znth (ind) (h_val) (lh_2)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  (dll top_ph_2 0 l_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  (store_map_missing_i store_name m_node_2 k_cur )
|--
  EX (l1: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l_tail))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l_tail))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph_2 ) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ”
  &&  (dll top_ph_2 0 l )
  **  (PtrArray.missing_i bucks_ph_2 ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR))) &((i_v_2)  # "blist" ->ₛ "next") l1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
).

Definition hashtbl_find_entail_wit_6_2 := 
(
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node_2: ((@list Z) -> (@option Z))) (l1_2: (@list Z)) (l2_2: (@list Z)) (top_ph_2: Z) (bucks_ph_2: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node_2 m1 )) (PreH8 : (l2_2 = (cons (i_v_2) (l_tail)))) (PreH9 : ((m_node_2 (k_cur)) = (Some (i_v_2)))) (PreH10 : ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2)))))))) (PreH11 : ((Znth (0) ((app (l1_2) (l2_2))) (0)) = (Znth (ind) (lh_2) (0)))) (PreH12 : (l1_2 = (@nil Z))) (PreH13 : (i = (bucks_ph_2 + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node_2 l_2 )) (PreH15 : (repr_all_heads lh_2 b_2 )) (PreH16 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH17 : (not_key k l1_2 m_node_2 )) (PreH18 : (bucket_cells_nonnull bucks_ph_2 )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph_2)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.missing_i bucks_ph_2 ind 0 211 lh_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR))) i l1_2 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node_2 k_cur )
  **  (sll p_next l_tail )
|--
  EX (i_v: Z)  (l1: (@list Z))  (l2: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) &((i_v_2)  # "blist" ->ₛ "next") l1 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node_2: ((@list Z) -> (@option Z))) (l1_2: (@list Z)) (l2_2: (@list Z)) (top_ph_2: Z) (bucks_ph_2: Z) (l_2: (@list Z)) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v_2: Z) (retval: Z) (PreH1 : (vp <= UINT_MAX)) (PreH2 : (vp >= 0)) (PreH3 : (retval = 0)) (PreH4 : (k <> k_cur)) (PreH5 : (0 <= ind)) (PreH6 : (ind < 211)) (PreH7 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH8 : (map_composable m1 m2 )) (PreH9 : (node_value_map m_node_2 m1 )) (PreH10 : (l2_2 = (cons (i_v_2) (l_tail)))) (PreH11 : ((m_node_2 (k_cur)) = (Some (i_v_2)))) (PreH12 : ((b_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) ((app (l1_2) (l2_2)))))))) (PreH13 : ((Znth (0) ((app (l1_2) (l2_2))) (0)) = (Znth (ind) (lh_2) (0)))) (PreH14 : (l1_2 = (@nil Z))) (PreH15 : (i = (bucks_ph_2 + (ind * sizeof(PTR))))) (PreH16 : (contain_all_addrs m_node_2 l_2 )) (PreH17 : (repr_all_heads lh_2 b_2 )) (PreH18 : (contain_all_correct_addrs m_node_2 b_2 )) (PreH19 : (not_key k l1_2 m_node_2 )) (PreH20 : (bucket_cells_nonnull bucks_ph_2 )) (PreH21 : (i <> 0)) (PreH22 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH23 : ((m2 (&((i_v_2)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH24 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v_2)
  **  (dll top_ph_2 0 l_2 )
  **  (PtrArray.missing_i bucks_ph_2 ind 0 211 lh_2 )
  **  (store_map_missing_i store_sll b_2 ind )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR))) i l1_2 )
  **  (store_map_missing_i store_uint m2 &((i_v_2)  # "blist" ->ₛ "val") )
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v_2)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  (store_map_missing_i store_name m_node_2 k_cur )
|--
  EX (l1: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (lh: (@list Z))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l_tail))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l_tail))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph_2 ) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ”
  &&  (dll top_ph_2 0 l )
  **  (PtrArray.missing_i bucks_ph_2 ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  (sllbseg (bucks_ph_2 + (ind * sizeof(PTR))) &((i_v_2)  # "blist" ->ₛ "next") l1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
).

Definition hashtbl_find_return_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (i_v: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (lh: (@list Z)) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v = 0)) (PreH2 : (0 <= ind)) (PreH3 : (ind < 211)) (PreH4 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH5 : (map_composable m1 m2 )) (PreH6 : (node_value_map m_node m1 )) (PreH7 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH8 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH9 : (contain_all_addrs m_node l )) (PreH10 : (repr_all_heads lh b )) (PreH11 : (contain_all_correct_addrs m_node b )) (PreH12 : (not_key k l1 m_node )) (PreH13 : (bucket_cells_nonnull bucks_ph )) (PreH14 : (i <> 0)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (store_map store_name m_node )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l2 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (0 = 0) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0))
  ||
  (EX (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (p))) ” 
  &&  “ ((m2 (p)) = (Some (v))) ” 
  &&  “ (0 = v) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 1))
.

Definition hashtbl_find_return_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (i_v) ((replace_Znth (ind) (h_val) (lh)))) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |-> 1)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (h_val) (lh)) 0))
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (vp = 0) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0))
  ||
  (EX (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (p))) ” 
  &&  “ ((m2 (p)) = (Some (v))) ” 
  &&  “ (vp = v) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 1))
.

Definition hashtbl_find_return_wit_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (i_v) ((replace_Znth (ind) (p_next) (lh)))) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |-> 1)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (vp = 0) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 0))
  ||
  (EX (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (p))) ” 
  &&  “ ((m2 (p)) = (Some (v))) ” 
  &&  “ (vp = v) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |-> 1))
.

Definition hashtbl_find_partial_solve_wit_1 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) ,
  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  “ (map_composable m1 m2 ) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
.

Definition hashtbl_find_partial_solve_wit_2 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (bucks_ph: Z) (top_ph: Z) (m_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m_node m1 )) (PreH2 : (contain_all_addrs m_node l )) (PreH3 : (repr_all_heads lh b )) (PreH4 : (contain_all_correct_addrs m_node b )) (PreH5 : (bucket_cells_nonnull bucks_ph )) (PreH6 : (map_composable m1 m2 )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
|--
  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (map_composable m1 m2 ) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
  **  (store_map store_uint m2 )
  **  ((valid_pre) # Int  |->_)
.

Definition hashtbl_find_partial_solve_wit_3 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (PreH1 : (0 <= ind)) (PreH2 : (ind < 211)) (PreH3 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH4 : (map_composable m1 m2 )) (PreH5 : (node_value_map m_node m1 )) (PreH6 : (l2 = (cons (i_v) (l_tail)))) (PreH7 : ((m_node (k_cur)) = (Some (i_v)))) (PreH8 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH9 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH10 : (l1 <> (@nil Z))) (PreH11 : (l1 = (cons (h_val) (t_l1)))) (PreH12 : (h_val = (Znth (ind) (lh) (0)))) (PreH13 : (contain_all_addrs m_node l )) (PreH14 : (repr_all_heads lh b )) (PreH15 : (contain_all_correct_addrs m_node b )) (PreH16 : (not_key k l1 m_node )) (PreH17 : (bucket_cells_nonnull bucks_ph )) (PreH18 : (i <> 0)) (PreH19 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH20 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) ,
  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |-> h_val)
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_4 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (PreH1 : (0 <= ind)) (PreH2 : (ind < 211)) (PreH3 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH4 : (map_composable m1 m2 )) (PreH5 : (node_value_map m_node m1 )) (PreH6 : (l2 = (cons (i_v) (l_tail)))) (PreH7 : ((m_node (k_cur)) = (Some (i_v)))) (PreH8 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH9 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH10 : (l1 = (@nil Z))) (PreH11 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH12 : (contain_all_addrs m_node l )) (PreH13 : (repr_all_heads lh b )) (PreH14 : (contain_all_correct_addrs m_node b )) (PreH15 : (not_key k l1 m_node )) (PreH16 : (bucket_cells_nonnull bucks_ph )) (PreH17 : (i <> 0)) (PreH18 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH19 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) ,
  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  (store_string key_pre k )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_string kp k_cur )
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ”
  &&  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_5 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |-> (Znth ind (replace_Znth (ind) (h_val) (lh)) 0))
  **  (PtrArray.missing_i bucks_ph ind 0 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_6 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |-> p_next)
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.missing_i bucks_ph ind 0 211 lh )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_7 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 = (@nil Z))) (PreH13 : (i = (bucks_ph + (ind * sizeof(PTR))))) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b )) (PreH16 : (contain_all_correct_addrs m_node b )) (PreH17 : (not_key k l1 m_node )) (PreH18 : (bucket_cells_nonnull bucks_ph )) (PreH19 : (i <> 0)) (PreH20 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH21 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH22 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (p_next) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 = (@nil Z)) ” 
  &&  “ (i = (bucks_ph + (ind * sizeof(PTR)))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_ph ind 0 211 (replace_Znth (ind) (p_next) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg (bucks_ph + (ind * sizeof(PTR))) i l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> p_next)
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_partial_solve_wit_8 := 
forall (valid_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_node: ((@list Z) -> (@option Z))) (l1: (@list Z)) (l2: (@list Z)) (top_ph: Z) (bucks_ph: Z) (l: (@list Z)) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (kp: Z) (vp: Z) (p_next: Z) (k_cur: (@list Z)) (l_tail: (@list Z)) (h_val: Z) (t_l1: (@list Z)) (ind: Z) (i: Z) (i_v: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_cur)) (PreH3 : (0 <= ind)) (PreH4 : (ind < 211)) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m_node m1 )) (PreH8 : (l2 = (cons (i_v) (l_tail)))) (PreH9 : ((m_node (k_cur)) = (Some (i_v)))) (PreH10 : ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2)))))))) (PreH11 : ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0)))) (PreH12 : (l1 <> (@nil Z))) (PreH13 : (l1 = (cons (h_val) (t_l1)))) (PreH14 : (h_val = (Znth (ind) (lh) (0)))) (PreH15 : (contain_all_addrs m_node l )) (PreH16 : (repr_all_heads lh b )) (PreH17 : (contain_all_correct_addrs m_node b )) (PreH18 : (not_key k l1 m_node )) (PreH19 : (bucket_cells_nonnull bucks_ph )) (PreH20 : (i <> 0)) (PreH21 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH22 : ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp)))) (PreH23 : (retval <> 0)) ,
  (PtrArray.full bucks_ph 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (h_val) (lh)) 0))
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
|--
  “ (retval = 1) ” 
  &&  “ (k = k_cur) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m_node m1 ) ” 
  &&  “ (l2 = (cons (i_v) (l_tail))) ” 
  &&  “ ((m_node (k_cur)) = (Some (i_v))) ” 
  &&  “ ((b (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l1) (l2))))))) ” 
  &&  “ ((Znth (0) ((app (l1) (l2))) (0)) = (Znth (ind) (lh) (0))) ” 
  &&  “ (l1 <> (@nil Z)) ” 
  &&  “ (l1 = (cons (h_val) (t_l1))) ” 
  &&  “ (h_val = (Znth (ind) (lh) (0))) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (not_key k l1 m_node ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((m2 (&((i_v)  # "blist" ->ₛ "val"))) = (Some (vp))) ” 
  &&  “ (retval <> 0) ”
  &&  (((bucks_ph + (ind * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i bucks_ph ind 0 211 (replace_Znth (ind) (h_val) (lh)) )
  **  (store_string key_pre k )
  **  (store_string kp k_cur )
  **  ((i) # Ptr  |-> p_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (store_map_missing_i store_sll b ind )
  **  (sllbseg &((h_val)  # "blist" ->ₛ "next") i t_l1 )
  **  (store_map_missing_i store_uint m2 &((i_v)  # "blist" ->ₛ "val") )
  **  ((valid_pre) # Int  |->_)
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> kp)
  **  ((&((i_v)  # "blist" ->ₛ "val")) # UInt  |-> vp)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (h_val) (lh)) 0))
  **  (store_map_missing_i store_name m_node k_cur )
  **  (sll p_next l_tail )
.

Definition hashtbl_find_which_implies_wit_1 := 
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (m_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
) \/
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (bucks_ph: Z)  (top_ph: Z)  (m_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m_node m1 ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m_node b ) ” 
  &&  “ (bucket_cells_nonnull bucks_ph ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_ph)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> bucks_ph)
  **  (dll top_ph 0 l )
  **  (PtrArray.full bucks_ph 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m_node )
).

(*----- Function hashtbl_findref -----*)

Definition hashtbl_findref_safety_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b0 )) (PreH7 : (contain_all_correct_addrs m_node b0 )) (PreH8 : (bucket_cells_nonnull h_bucks )) ,
  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  “ (211 <> 0) ”
.

Definition hashtbl_findref_safety_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node m )) (PreH5 : (contain_all_addrs m_node l )) (PreH6 : (repr_all_heads lh b0 )) (PreH7 : (contain_all_correct_addrs m_node b0 )) (PreH8 : (bucket_cells_nonnull h_bucks )) ,
  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m_node )
  **  ((( &( "i" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition hashtbl_findref_safety_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH2 : (node_value_map m_node m )) (PreH3 : (contain_all_addrs m_node l )) (PreH4 : (repr_all_heads lh b0 )) (PreH5 : (contain_all_correct_addrs m_node b0 )) (PreH6 : (bucket_cells_nonnull h_bucks )) (PreH7 : (0 <= ind)) (PreH8 : (ind < 211)) (PreH9 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH10 : (l0 = (app (l_prev) (l_res)))) (PreH11 : (not_key k l_prev m_node )) (PreH12 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_findref_safety_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ False ”
.

Definition hashtbl_findref_safety_wit_5 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ False ”
.

Definition hashtbl_findref_safety_wit_6 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v = 0)) (PreH2 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH3 : (node_value_map m_node m )) (PreH4 : (contain_all_addrs m_node l )) (PreH5 : (repr_all_heads lh b0 )) (PreH6 : (contain_all_correct_addrs m_node b0 )) (PreH7 : (bucket_cells_nonnull h_bucks )) (PreH8 : (0 <= ind)) (PreH9 : (ind < 211)) (PreH10 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH11 : (l0 = (app (l_prev) (l_res)))) (PreH12 : (not_key k l_prev m_node )) (PreH13 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_findref_entail_wit_1 := 
(
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top_2: Z) (h_bucks: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (m_node_2: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node_2 m )) (PreH5 : (contain_all_addrs m_node_2 l_2 )) (PreH6 : (repr_all_heads lh_2 b0_2 )) (PreH7 : (contain_all_correct_addrs m_node_2 b0_2 )) (PreH8 : (bucket_cells_nonnull h_bucks )) ,
  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_2)
  **  (dll top_2 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b0_2 )
  **  (store_map store_name m_node_2 )
|--
  EX (top: Z)  (i_v: Z)  (l_prev: (@list Z))  (l_res: (@list Z))  (l0: (@list Z))  (h_bucks_2: Z)  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks_2 ) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ ((b0 ((retval % ( 211 ) ))) = (Some ((pair ((Znth ((retval % ( 211 ) )) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ ((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (sllbseg (h_bucks_2 + ((retval % ( 211 ) ) * sizeof(PTR))) (h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) l_prev )
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 (retval % ( 211 ) ) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks_2 (retval % ( 211 ) ) 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top_2: Z) (h_bucks: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (m_node_2: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m_node_2 m )) (PreH5 : (contain_all_addrs m_node_2 l_2 )) (PreH6 : (repr_all_heads lh_2 b0_2 )) (PreH7 : (contain_all_correct_addrs m_node_2 b0_2 )) (PreH8 : (bucket_cells_nonnull h_bucks )) ,
  (store_string key_pre k )
  **  (dll top_2 0 l_2 )
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b0_2 )
  **  (store_map store_name m_node_2 )
|--
  EX (i_v: Z)  (l_res: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ ((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ” 
  &&  “ ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ ((b0 ((retval % ( 211 ) ))) = (Some ((pair ((Znth ((retval % ( 211 ) )) (lh) (0))) ((app ((@nil Z)) (l_res))))))) ” 
  &&  “ (not_key k (@nil Z) m_node ) ” 
  &&  “ ((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ”
  &&  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 (retval % ( 211 ) ) )
  **  (dll top_2 0 l )
  **  (PtrArray.missing_i h_bucks (retval % ( 211 ) ) 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
).

Definition hashtbl_findref_entail_wit_2_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ (retval = 0) ” 
  &&  “ (k <> k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_2_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (k = k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval_2 = 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (k <> k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_3_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (k <> k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval_2 <> 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_3_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_list_current)) (PreH3 : (i_v <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH6 : (l_res = (cons (i_v) (l_resres)))) (PreH7 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node m )) (PreH11 : (contain_all_addrs m_node l )) (PreH12 : (repr_all_heads lh b0 )) (PreH13 : (contain_all_correct_addrs m_node b0 )) (PreH14 : (bucket_cells_nonnull h_bucks )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH18 : (l0 = (app (l_prev) (l_res)))) (PreH19 : (not_key k l_prev m_node )) (PreH20 : (i <> 0)) (PreH21 : (retval <> 0)) ,
  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ (i_v = i_v) ” 
  &&  “ (ind <= UINT_MAX) ” 
  &&  “ (ind >= 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_entail_wit_5 := 
(
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top_2: Z) (i_v_2: Z) (i: Z) (l_prev_2: (@list Z)) (l_res_2: (@list Z)) (l0_2: (@list Z)) (h_bucks_2: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (m_node_2: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list_current)) (PreH3 : (i_v_2 <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node_2 (k_list_current)) = (Some (i_v_2)))) (PreH6 : (l_res_2 = (cons (i_v_2) (l_resres)))) (PreH7 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v_2 <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node_2 m )) (PreH11 : (contain_all_addrs m_node_2 l_2 )) (PreH12 : (repr_all_heads lh_2 b0_2 )) (PreH13 : (contain_all_correct_addrs m_node_2 b0_2 )) (PreH14 : (bucket_cells_nonnull h_bucks_2 )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) (l0_2)))))) (PreH18 : (l0_2 = (app (l_prev_2) (l_res_2)))) (PreH19 : (not_key k l_prev_2 m_node_2 )) (PreH20 : (i <> 0)) (PreH21 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v_2)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks_2)
  **  (sllbseg (h_bucks_2 + (ind * sizeof(PTR))) i l_prev_2 )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node_2 k_list_current )
  **  (store_map_missing_i store_sll b0_2 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_2)
  **  (dll top_2 0 l_2 )
  **  (PtrArray.missing_i h_bucks_2 ind 0 211 lh_2 )
|--
  EX (top: Z)  (i_v: Z)  (l_prev: (@list Z))  (l_res: (@list Z))  (l0: (@list Z))  (h_bucks: Z)  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) &((i_v_2)  # "blist" ->ₛ "next") l_prev )
  **  ((&((i_v_2)  # "blist" ->ₛ "next")) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top_2: Z) (i_v_2: Z) (i: Z) (l_prev_2: (@list Z)) (l_res_2: (@list Z)) (l0_2: (@list Z)) (h_bucks_2: Z) (lh_2: (@list Z)) (b0_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (m_node_2: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list_current)) (PreH3 : (i_v_2 <> 0)) (PreH4 : (i <> 0)) (PreH5 : ((m_node_2 (k_list_current)) = (Some (i_v_2)))) (PreH6 : (l_res_2 = (cons (i_v_2) (l_resres)))) (PreH7 : (&((i_v_2)  # "blist" ->ₛ "next") <> 0)) (PreH8 : (i_v_2 <> 0)) (PreH9 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH10 : (node_value_map m_node_2 m )) (PreH11 : (contain_all_addrs m_node_2 l_2 )) (PreH12 : (repr_all_heads lh_2 b0_2 )) (PreH13 : (contain_all_correct_addrs m_node_2 b0_2 )) (PreH14 : (bucket_cells_nonnull h_bucks_2 )) (PreH15 : (0 <= ind)) (PreH16 : (ind < 211)) (PreH17 : ((b0_2 (ind)) = (Some ((pair ((Znth (ind) (lh_2) (0))) (l0_2)))))) (PreH18 : (l0_2 = (app (l_prev_2) (l_res_2)))) (PreH19 : (not_key k l_prev_2 m_node_2 )) (PreH20 : (i <> 0)) (PreH21 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v_2)
  **  (sllbseg (h_bucks_2 + (ind * sizeof(PTR))) i l_prev_2 )
  **  ((&((i_v_2)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node_2 k_list_current )
  **  (store_map_missing_i store_sll b0_2 ind )
  **  (dll top_2 0 l_2 )
  **  (PtrArray.missing_i h_bucks_2 ind 0 211 lh_2 )
|--
  EX (l_prev: (@list Z))  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks_2 ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) ((app (l_prev) (l_resres))))))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (&((i_v_2)  # "blist" ->ₛ "next") <> 0) ”
  &&  (sllbseg (h_bucks_2 + (ind * sizeof(PTR))) &((i_v_2)  # "blist" ->ₛ "next") l_prev )
  **  (store_map_missing_i store_sll b0 ind )
  **  (dll top_2 0 l )
  **  (PtrArray.missing_i h_bucks_2 ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
).

Definition hashtbl_findref_return_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v = 0)) (PreH2 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH3 : (node_value_map m_node m )) (PreH4 : (contain_all_addrs m_node l )) (PreH5 : (repr_all_heads lh b0 )) (PreH6 : (contain_all_correct_addrs m_node b0 )) (PreH7 : (bucket_cells_nonnull h_bucks )) (PreH8 : (0 <= ind)) (PreH9 : (ind < 211)) (PreH10 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH11 : (l0 = (app (l_prev) (l_res)))) (PreH12 : (not_key k l_prev m_node )) (PreH13 : (i <> 0)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
|--
  (“ ((m (k)) = None) ” 
  &&  “ (0 = 0) ”
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  “ ((m (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ (0 = &((p)  # "blist" ->ₛ "val")) ”
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_return_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (head: Z) (l_prevres: (@list Z)) (PreH1 : (i <> 0)) (PreH2 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH3 : (l_prev = (cons (head) (l_prevres)))) (PreH4 : (ind <= UINT_MAX)) (PreH5 : (ind >= 0)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list_current)) (PreH8 : (i_v <> 0)) (PreH9 : (i <> 0)) (PreH10 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH11 : (l_res = (cons (i_v) (l_resres)))) (PreH12 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH13 : (i_v <> 0)) (PreH14 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH15 : (node_value_map m_node m )) (PreH16 : (contain_all_addrs m_node l )) (PreH17 : (repr_all_heads lh b0 )) (PreH18 : (contain_all_correct_addrs m_node b0 )) (PreH19 : (bucket_cells_nonnull h_bucks )) (PreH20 : (0 <= ind)) (PreH21 : (ind < 211)) (PreH22 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH23 : (l0 = (app (l_prev) (l_res)))) (PreH24 : (not_key k l_prev m_node )) (PreH25 : (i <> 0)) (PreH26 : (retval <> 0)) ,
  (PtrArray.full h_bucks 211 (replace_Znth (ind) (i_v) ((replace_Znth (ind) (head) (lh)))) )
  **  ((i) # Ptr  |-> i_v_next)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (head) (lh)) 0))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg &((head)  # "blist" ->ₛ "next") i l_prevres )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
|--
  (“ ((m (k)) = None) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "val") = 0) ”
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  “ ((m (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "val") = &((p)  # "blist" ->ₛ "val")) ”
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_return_wit_3 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (l_prev = (@nil Z))) (PreH2 : ((h_bucks + (ind * sizeof(PTR))) = i)) (PreH3 : (i <> 0)) (PreH4 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH5 : (ind <= UINT_MAX)) (PreH6 : (ind >= 0)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list_current)) (PreH9 : (i_v <> 0)) (PreH10 : (i <> 0)) (PreH11 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH12 : (l_res = (cons (i_v) (l_resres)))) (PreH13 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH14 : (i_v <> 0)) (PreH15 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH16 : (node_value_map m_node m )) (PreH17 : (contain_all_addrs m_node l )) (PreH18 : (repr_all_heads lh b0 )) (PreH19 : (contain_all_correct_addrs m_node b0 )) (PreH20 : (bucket_cells_nonnull h_bucks )) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (not_key k l_prev m_node )) (PreH26 : (i <> 0)) (PreH27 : (retval <> 0)) ,
  (PtrArray.full h_bucks 211 (replace_Znth (ind) (i_v) ((replace_Znth (ind) (i_v_next) (lh)))) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (i_v_next) (lh)) 0))
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
|--
  (“ ((m (k)) = None) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "val") = 0) ”
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
  ||
  (EX (p: Z) ,
  “ ((m (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "val") = &((p)  # "blist" ->ₛ "val")) ”
  &&  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k ))
.

Definition hashtbl_findref_partial_solve_wit_1 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) ,
  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k )
|--
  (store_hash_skeleton h_pre m )
  **  (store_string key_pre k )
.

Definition hashtbl_findref_partial_solve_wit_2 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m_node m )) (PreH2 : (contain_all_addrs m_node l )) (PreH3 : (repr_all_heads lh b0 )) (PreH4 : (contain_all_correct_addrs m_node b0 )) (PreH5 : (bucket_cells_nonnull h_bucks )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m_node )
  **  (store_string key_pre k )
|--
  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m_node )
.

Definition hashtbl_findref_partial_solve_wit_3_pure := 
(
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v <> 0)) (PreH2 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH3 : (node_value_map m_node m )) (PreH4 : (contain_all_addrs m_node l )) (PreH5 : (repr_all_heads lh b0 )) (PreH6 : (contain_all_correct_addrs m_node b0 )) (PreH7 : (bucket_cells_nonnull h_bucks )) (PreH8 : (0 <= ind)) (PreH9 : (ind < 211)) (PreH10 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH11 : (l0 = (app (l_prev) (l_res)))) (PreH12 : (not_key k l_prev m_node )) (PreH13 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
|--
  EX (k_list_current: (@list Z)) ,
  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ”
) \/
(
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (ind <= UINT_MAX)) (PreH2 : (ind >= 0)) (PreH3 : (i_v <> 0)) (PreH4 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH5 : (node_value_map m_node m )) (PreH6 : (contain_all_addrs m_node l )) (PreH7 : (repr_all_heads lh b0 )) (PreH8 : (contain_all_correct_addrs m_node b0 )) (PreH9 : (bucket_cells_nonnull h_bucks )) (PreH10 : (0 <= ind)) (PreH11 : (ind < 211)) (PreH12 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH13 : (l0 = (app (l_prev) (l_res)))) (PreH14 : (not_key k l_prev m_node )) (PreH15 : (i <> 0)) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
|--
  EX (k_list_current: (@list Z)) ,
  “ ((m_node (k_list_current)) = (Some (i_v))) ”
).

Definition hashtbl_findref_partial_solve_wit_3_aux := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (PreH1 : (i_v <> 0)) (PreH2 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH3 : (node_value_map m_node m )) (PreH4 : (contain_all_addrs m_node l )) (PreH5 : (repr_all_heads lh b0 )) (PreH6 : (contain_all_correct_addrs m_node b0 )) (PreH7 : (bucket_cells_nonnull h_bucks )) (PreH8 : (0 <= ind)) (PreH9 : (ind < 211)) (PreH10 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH11 : (l0 = (app (l_prev) (l_res)))) (PreH12 : (not_key k l_prev m_node )) (PreH13 : (i <> 0)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((i) # Ptr  |-> i_v)
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
  **  (store_map store_name m_node )
|--
  EX (k_list_current: (@list Z)) ,
  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ”
  &&  ((i) # Ptr  |-> i_v)
  **  (store_map store_name m_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  (sll i_v l_res )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
.

Definition hashtbl_findref_partial_solve_wit_3 := hashtbl_findref_partial_solve_wit_3_pure -> hashtbl_findref_partial_solve_wit_3_aux.

Definition hashtbl_findref_partial_solve_wit_4 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (PreH1 : (i_v <> 0)) (PreH2 : (i <> 0)) (PreH3 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH4 : (l_res = (cons (i_v) (l_resres)))) (PreH5 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH6 : (i_v <> 0)) (PreH7 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH8 : (node_value_map m_node m )) (PreH9 : (contain_all_addrs m_node l )) (PreH10 : (repr_all_heads lh b0 )) (PreH11 : (contain_all_correct_addrs m_node b0 )) (PreH12 : (bucket_cells_nonnull h_bucks )) (PreH13 : (0 <= ind)) (PreH14 : (ind < 211)) (PreH15 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH16 : (l0 = (app (l_prev) (l_res)))) (PreH17 : (not_key k l_prev m_node )) (PreH18 : (i <> 0)) ,
  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list_current )
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
  **  (store_string key_pre k )
|--
  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((i) # Ptr  |-> i_v)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_partial_solve_wit_5_pure := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (i_v = i_v)) (PreH2 : (ind <= UINT_MAX)) (PreH3 : (ind >= 0)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list_current)) (PreH6 : (i_v <> 0)) (PreH7 : (i <> 0)) (PreH8 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH9 : (l_res = (cons (i_v) (l_resres)))) (PreH10 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH11 : (i_v <> 0)) (PreH12 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH13 : (node_value_map m_node m )) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b0 )) (PreH16 : (contain_all_correct_addrs m_node b0 )) (PreH17 : (bucket_cells_nonnull h_bucks )) (PreH18 : (0 <= ind)) (PreH19 : (ind < 211)) (PreH20 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH21 : (l0 = (app (l_prev) (l_res)))) (PreH22 : (not_key k l_prev m_node )) (PreH23 : (i <> 0)) (PreH24 : (retval <> 0)) ,
  ((( &( "b" ) )) # Ptr  |-> i_v)
  **  ((( &( "i" ) )) # Ptr  |-> i)
  **  ((i) # Ptr  |-> i_v_next)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ (i_v_next = i_v_next) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ”
.

Definition hashtbl_findref_partial_solve_wit_5_aux := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (i_v = i_v)) (PreH2 : (ind <= UINT_MAX)) (PreH3 : (ind >= 0)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list_current)) (PreH6 : (i_v <> 0)) (PreH7 : (i <> 0)) (PreH8 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH9 : (l_res = (cons (i_v) (l_resres)))) (PreH10 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH11 : (i_v <> 0)) (PreH12 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH13 : (node_value_map m_node m )) (PreH14 : (contain_all_addrs m_node l )) (PreH15 : (repr_all_heads lh b0 )) (PreH16 : (contain_all_correct_addrs m_node b0 )) (PreH17 : (bucket_cells_nonnull h_bucks )) (PreH18 : (0 <= ind)) (PreH19 : (ind < 211)) (PreH20 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH21 : (l0 = (app (l_prev) (l_res)))) (PreH22 : (not_key k l_prev m_node )) (PreH23 : (i <> 0)) (PreH24 : (retval <> 0)) ,
  ((i) # Ptr  |-> i_v_next)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
|--
  “ (i_v_next = i_v_next) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (ind <= UINT_MAX) ” 
  &&  “ (ind >= 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  ((i) # Ptr  |-> i_v_next)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (PtrArray.missing_i h_bucks ind 0 211 lh )
.

Definition hashtbl_findref_partial_solve_wit_5 := hashtbl_findref_partial_solve_wit_5_pure -> hashtbl_findref_partial_solve_wit_5_aux.

Definition hashtbl_findref_partial_solve_wit_6 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (l_prev = (@nil Z))) (PreH2 : ((h_bucks + (ind * sizeof(PTR))) = i)) (PreH3 : (i <> 0)) (PreH4 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH5 : (ind <= UINT_MAX)) (PreH6 : (ind >= 0)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list_current)) (PreH9 : (i_v <> 0)) (PreH10 : (i <> 0)) (PreH11 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH12 : (l_res = (cons (i_v) (l_resres)))) (PreH13 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH14 : (i_v <> 0)) (PreH15 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH16 : (node_value_map m_node m )) (PreH17 : (contain_all_addrs m_node l )) (PreH18 : (repr_all_heads lh b0 )) (PreH19 : (contain_all_correct_addrs m_node b0 )) (PreH20 : (bucket_cells_nonnull h_bucks )) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (not_key k l_prev m_node )) (PreH26 : (i <> 0)) (PreH27 : (retval <> 0)) ,
  (PtrArray.full h_bucks 211 (replace_Znth (ind) (i_v_next) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
|--
  “ (l_prev = (@nil Z)) ” 
  &&  “ ((h_bucks + (ind * sizeof(PTR))) = i) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (ind <= UINT_MAX) ” 
  &&  “ (ind >= 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (((h_bucks + (ind * sizeof(PTR)))) # Ptr  |-> (Znth ind (replace_Znth (ind) (i_v_next) (lh)) 0))
  **  (PtrArray.missing_i h_bucks ind 0 211 (replace_Znth (ind) (i_v_next) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
.

Definition hashtbl_findref_partial_solve_wit_7 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (head: Z) (l_prevres: (@list Z)) (PreH1 : (i_v_next = i_v_next)) (PreH2 : (i <> 0)) (PreH3 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH4 : (l_prev = (cons (head) (l_prevres)))) (PreH5 : (ind <= UINT_MAX)) (PreH6 : (ind >= 0)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list_current)) (PreH9 : (i_v <> 0)) (PreH10 : (i <> 0)) (PreH11 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH12 : (l_res = (cons (i_v) (l_resres)))) (PreH13 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH14 : (i_v <> 0)) (PreH15 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH16 : (node_value_map m_node m )) (PreH17 : (contain_all_addrs m_node l )) (PreH18 : (repr_all_heads lh b0 )) (PreH19 : (contain_all_correct_addrs m_node b0 )) (PreH20 : (bucket_cells_nonnull h_bucks )) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (not_key k l_prev m_node )) (PreH26 : (i <> 0)) (PreH27 : (retval <> 0)) ,
  (PtrArray.full h_bucks 211 (replace_Znth (ind) (head) (lh)) )
  **  ((i) # Ptr  |-> i_v_next)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg &((head)  # "blist" ->ₛ "next") i l_prevres )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
|--
  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (l_prev = (cons (head) (l_prevres))) ” 
  &&  “ (ind <= UINT_MAX) ” 
  &&  “ (ind >= 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (((h_bucks + (ind * sizeof(PTR)))) # Ptr  |-> (Znth ind (replace_Znth (ind) (head) (lh)) 0))
  **  (PtrArray.missing_i h_bucks ind 0 211 (replace_Znth (ind) (head) (lh)) )
  **  ((i) # Ptr  |-> i_v_next)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg &((head)  # "blist" ->ₛ "next") i l_prevres )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
.

Definition hashtbl_findref_partial_solve_wit_8 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (head: Z) (l_prevres: (@list Z)) (PreH1 : (i <> 0)) (PreH2 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH3 : (l_prev = (cons (head) (l_prevres)))) (PreH4 : (ind <= UINT_MAX)) (PreH5 : (ind >= 0)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list_current)) (PreH8 : (i_v <> 0)) (PreH9 : (i <> 0)) (PreH10 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH11 : (l_res = (cons (i_v) (l_resres)))) (PreH12 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH13 : (i_v <> 0)) (PreH14 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH15 : (node_value_map m_node m )) (PreH16 : (contain_all_addrs m_node l )) (PreH17 : (repr_all_heads lh b0 )) (PreH18 : (contain_all_correct_addrs m_node b0 )) (PreH19 : (bucket_cells_nonnull h_bucks )) (PreH20 : (0 <= ind)) (PreH21 : (ind < 211)) (PreH22 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH23 : (l0 = (app (l_prev) (l_res)))) (PreH24 : (not_key k l_prev m_node )) (PreH25 : (i <> 0)) (PreH26 : (retval <> 0)) ,
  (PtrArray.full h_bucks 211 (replace_Znth (ind) (head) (lh)) )
  **  ((i) # Ptr  |-> i_v_next)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (head) (lh)) 0))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg &((head)  # "blist" ->ₛ "next") i l_prevres )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
|--
  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (l_prev = (cons (head) (l_prevres))) ” 
  &&  “ (ind <= UINT_MAX) ” 
  &&  “ (ind >= 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (((h_bucks + (ind * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i h_bucks ind 0 211 (replace_Znth (ind) (head) (lh)) )
  **  ((i) # Ptr  |-> i_v_next)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (head) (lh)) 0))
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg &((head)  # "blist" ->ₛ "next") i l_prevres )
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
.

Definition hashtbl_findref_partial_solve_wit_9 := 
forall (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m: ((@list Z) -> (@option Z))) (top: Z) (i_v: Z) (i: Z) (l_prev: (@list Z)) (l_res: (@list Z)) (l0: (@list Z)) (h_bucks: Z) (lh: (@list Z)) (b0: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (ind: Z) (i_v_key: Z) (i_v_next: Z) (l_resres: (@list Z)) (k_list_current: (@list Z)) (retval: Z) (PreH1 : (l_prev = (@nil Z))) (PreH2 : ((h_bucks + (ind * sizeof(PTR))) = i)) (PreH3 : (i <> 0)) (PreH4 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH5 : (ind <= UINT_MAX)) (PreH6 : (ind >= 0)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list_current)) (PreH9 : (i_v <> 0)) (PreH10 : (i <> 0)) (PreH11 : ((m_node (k_list_current)) = (Some (i_v)))) (PreH12 : (l_res = (cons (i_v) (l_resres)))) (PreH13 : (&((i_v)  # "blist" ->ₛ "next") <> 0)) (PreH14 : (i_v <> 0)) (PreH15 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH16 : (node_value_map m_node m )) (PreH17 : (contain_all_addrs m_node l )) (PreH18 : (repr_all_heads lh b0 )) (PreH19 : (contain_all_correct_addrs m_node b0 )) (PreH20 : (bucket_cells_nonnull h_bucks )) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (not_key k l_prev m_node )) (PreH26 : (i <> 0)) (PreH27 : (retval <> 0)) ,
  (PtrArray.full h_bucks 211 (replace_Znth (ind) (i_v_next) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (i_v_next) (lh)) 0))
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
|--
  “ (l_prev = (@nil Z)) ” 
  &&  “ ((h_bucks + (ind * sizeof(PTR))) = i) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (ind <= UINT_MAX) ” 
  &&  “ (ind >= 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list_current) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (i_v <> 0) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((b0 (ind)) = (Some ((pair ((Znth (ind) (lh) (0))) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (not_key k l_prev m_node ) ” 
  &&  “ (i <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (((h_bucks + (ind * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i h_bucks ind 0 211 (replace_Znth (ind) (i_v_next) (lh)) )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> (Znth ind (replace_Znth (ind) (i_v_next) (lh)) 0))
  **  (store_string key_pre k )
  **  (store_string i_v_key k_list_current )
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_map_missing_i store_name m_node k_list_current )
  **  (store_map_missing_i store_sll b0 ind )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
.

Definition hashtbl_findref_which_implies_wit_1 := 
(
forall (h_pre: Z) (m: ((@list Z) -> (@option Z))) ,
  (store_hash_skeleton h_pre m )
|--
  EX (top: Z)  (h_bucks: Z)  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m_node )
) \/
(
forall (h_pre: Z) (m: ((@list Z) -> (@option Z))) ,
  (store_hash_skeleton h_pre m )
|--
  EX (top: Z)  (h_bucks: Z)  (lh: (@list Z))  (b0: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m_node m ) ” 
  &&  “ (contain_all_addrs m_node l ) ” 
  &&  “ (repr_all_heads lh b0 ) ” 
  &&  “ (contain_all_correct_addrs m_node b0 ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b0 )
  **  (store_map store_name m_node )
).

Definition hashtbl_findref_which_implies_wit_2 := 
(
forall (l_prev: (@list Z)) (l_res: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (k_list_current_2: (@list Z)) (i: Z) (i_v: Z) (ind: Z) (h: Z) (h_bucks: Z) (PreH1 : (i_v <> 0)) (PreH2 : (i <> 0)) (PreH3 : ((m_node (k_list_current_2)) = (Some (i_v)))) ,
  ((i) # Ptr  |-> i_v)
  **  (store_map store_name m_node )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  (sll i_v l_res )
|--
  EX (i_v_key: Z)  (i_v_next: Z)  (l_resres: (@list Z))  (k_list_current: (@list Z)) ,
  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l_resres))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
  **  ((&((i_v)  # "blist" ->ₛ "next")) # Ptr  |-> i_v_next)
  **  (sll i_v_next l_resres )
  **  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list_current )
  **  (store_map_missing_i store_name m_node k_list_current )
) \/
(
forall (l_res: (@list Z)) (m_node: ((@list Z) -> (@option Z))) (k_list_current_2: (@list Z)) (i: Z) (i_v: Z) (x: Z) (l0: (@list Z)) (PreH1 : (i_v = x)) (PreH2 : (l_res = (cons (x) (l0)))) (PreH3 : (i_v = x)) (PreH4 : (i_v <> 0)) (PreH5 : (i <> 0)) (PreH6 : ((m_node (k_list_current_2)) = (Some (i_v)))) ,
  (store_map store_name m_node )
|--
  EX (i_v_key: Z)  (k_list_current: (@list Z)) ,
  “ (i_v <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ ((m_node (k_list_current)) = (Some (i_v))) ” 
  &&  “ (l_res = (cons (i_v) (l0))) ” 
  &&  “ (&((i_v)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((&((i_v)  # "blist" ->ₛ "key")) # Ptr  |-> i_v_key)
  **  (store_string i_v_key k_list_current )
  **  (store_map_missing_i store_name m_node k_list_current )
).

Definition hashtbl_findref_which_implies_wit_3 := 
forall (l_prev: (@list Z)) (i: Z) (i_v: Z) (b: Z) (b_next: Z) (ind: Z) (h: Z) (h_bucks: Z) (PreH1 : (i_v = b_next)) (PreH2 : (i <> 0)) (PreH3 : (&((b)  # "blist" ->ₛ "next") <> 0)) ,
  ((i) # Ptr  |-> i_v)
  **  ((&((b)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (sllbseg (h_bucks + (ind * sizeof(PTR))) i l_prev )
|--
  (“ (l_prev = (@nil Z)) ” 
  &&  “ ((h_bucks + (ind * sizeof(PTR))) = i) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((b)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  ((&((b)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (((h_bucks + (ind * sizeof(PTR)))) # Ptr  |-> b_next))
  ||
  (EX (head: Z)  (l_prevres: (@list Z)) ,
  “ (i_v = b_next) ” 
  &&  “ (i <> 0) ” 
  &&  “ (&((b)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (l_prev = (cons (head) (l_prevres))) ”
  &&  ((i) # Ptr  |-> i_v)
  **  ((&((b)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (((h_bucks + (ind * sizeof(PTR)))) # Ptr  |-> head)
  **  (sllbseg &((head)  # "blist" ->ₛ "next") i l_prevres ))
.

(*----- Function hashtbl_remove -----*)

Definition hashtbl_remove_safety_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_addrs m1_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m1_node b )) (PreH8 : (bucket_cells_nonnull h_bucks )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
  **  ((( &( "it" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  “ (211 <> 0) ”
.

Definition hashtbl_remove_safety_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_addrs m1_node l )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (contain_all_correct_addrs m1_node b )) (PreH8 : (bucket_cells_nonnull h_bucks )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
  **  ((( &( "it" ) )) # Ptr  |->_)
  **  ((( &( "ind" ) )) # UInt  |->_)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition hashtbl_remove_safety_wit_3 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) (PreH2 : (node_value_map m1_node m1 )) (PreH3 : (not_key k l_prev m1_node )) (PreH4 : (NoDup l_res )) (PreH5 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH6 : (0 <= ind)) (PreH7 : (ind < 211)) (PreH8 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH9 : (l0 = (app (l_prev) (l_res)))) (PreH10 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH11 : (repr_all_heads lh bucket_map )) (PreH12 : (contain_all_correct_addrs m1_node bucket_map )) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (it <> 0)) (PreH15 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH16 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH17 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_4 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_list)) (PreH3 : (itv <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res = (cons (itv) (l_resres)))) (PreH6 : (dl_down = (cons (itv) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node m1 )) (PreH9 : (not_key k l_prev m1_node )) (PreH10 : (NoDup l_res )) (PreH11 : ((m1_node (k_list)) = (Some (itv)))) (PreH12 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node m1 )) (PreH18 : (not_key k l_prev m1_node )) (PreH19 : (NoDup l_res )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH26 : (repr_all_heads lh bucket_map )) (PreH27 : (contain_all_correct_addrs m1_node bucket_map )) (PreH28 : (bucket_cells_nonnull h_pre_bucks )) (PreH29 : (it <> 0)) (PreH30 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH31 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH32 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH33 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ False ”
.

Definition hashtbl_remove_safety_wit_5 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list)) (PreH3 : (itv <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res = (cons (itv) (l_resres)))) (PreH6 : (dl_down = (cons (itv) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node m1 )) (PreH9 : (not_key k l_prev m1_node )) (PreH10 : (NoDup l_res )) (PreH11 : ((m1_node (k_list)) = (Some (itv)))) (PreH12 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node m1 )) (PreH18 : (not_key k l_prev m1_node )) (PreH19 : (NoDup l_res )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH26 : (repr_all_heads lh bucket_map )) (PreH27 : (contain_all_correct_addrs m1_node bucket_map )) (PreH28 : (bucket_cells_nonnull h_pre_bucks )) (PreH29 : (it <> 0)) (PreH30 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH31 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH32 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH33 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ False ”
.

Definition hashtbl_remove_safety_wit_6 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (top <> itv)) (PreH2 : (retval = 1)) (PreH3 : (k = k_list)) (PreH4 : (itv <> 0)) (PreH5 : (it <> 0)) (PreH6 : (l_res = (cons (itv) (l_resres)))) (PreH7 : (dl_down = (cons (itv) (dl_downres)))) (PreH8 : (map_composable m1 m2 )) (PreH9 : (node_value_map m1_node m1 )) (PreH10 : (not_key k l_prev m1_node )) (PreH11 : (NoDup l_res )) (PreH12 : ((m1_node (k_list)) = (Some (itv)))) (PreH13 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH16 : (itv <> 0)) (PreH17 : (map_composable m1 m2 )) (PreH18 : (node_value_map m1_node m1 )) (PreH19 : (not_key k l_prev m1_node )) (PreH20 : (NoDup l_res )) (PreH21 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH22 : (0 <= ind)) (PreH23 : (ind < 211)) (PreH24 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH25 : (l0 = (app (l_prev) (l_res)))) (PreH26 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH27 : (repr_all_heads lh bucket_map )) (PreH28 : (contain_all_correct_addrs m1_node bucket_map )) (PreH29 : (bucket_cells_nonnull h_pre_bucks )) (PreH30 : (it <> 0)) (PreH31 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH32 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH33 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH34 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_7 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (top = itv)) (PreH2 : (retval = 1)) (PreH3 : (k = k_list)) (PreH4 : (itv <> 0)) (PreH5 : (it <> 0)) (PreH6 : (l_res = (cons (itv) (l_resres)))) (PreH7 : (dl_down = (cons (itv) (dl_downres)))) (PreH8 : (map_composable m1 m2 )) (PreH9 : (node_value_map m1_node m1 )) (PreH10 : (not_key k l_prev m1_node )) (PreH11 : (NoDup l_res )) (PreH12 : ((m1_node (k_list)) = (Some (itv)))) (PreH13 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH16 : (itv <> 0)) (PreH17 : (map_composable m1 m2 )) (PreH18 : (node_value_map m1_node m1 )) (PreH19 : (not_key k l_prev m1_node )) (PreH20 : (NoDup l_res )) (PreH21 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH22 : (0 <= ind)) (PreH23 : (ind < 211)) (PreH24 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH25 : (l0 = (app (l_prev) (l_res)))) (PreH26 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH27 : (repr_all_heads lh bucket_map )) (PreH28 : (contain_all_correct_addrs m1_node bucket_map )) (PreH29 : (bucket_cells_nonnull h_pre_bucks )) (PreH30 : (it <> 0)) (PreH31 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH32 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH33 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH34 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_8 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (dl_prev <> 0)) (PreH2 : (top = itv)) (PreH3 : (retval = 1)) (PreH4 : (k = k_list)) (PreH5 : (itv <> 0)) (PreH6 : (it <> 0)) (PreH7 : (l_res = (cons (itv) (l_resres)))) (PreH8 : (dl_down = (cons (itv) (dl_downres)))) (PreH9 : (map_composable m1 m2 )) (PreH10 : (node_value_map m1_node m1 )) (PreH11 : (not_key k l_prev m1_node )) (PreH12 : (NoDup l_res )) (PreH13 : ((m1_node (k_list)) = (Some (itv)))) (PreH14 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH15 : (bucket_cells_nonnull h_pre_bucks )) (PreH16 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH17 : (itv <> 0)) (PreH18 : (map_composable m1 m2 )) (PreH19 : (node_value_map m1_node m1 )) (PreH20 : (not_key k l_prev m1_node )) (PreH21 : (NoDup l_res )) (PreH22 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH23 : (0 <= ind)) (PreH24 : (ind < 211)) (PreH25 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH26 : (l0 = (app (l_prev) (l_res)))) (PreH27 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH28 : (repr_all_heads lh bucket_map )) (PreH29 : (contain_all_correct_addrs m1_node bucket_map )) (PreH30 : (bucket_cells_nonnull h_pre_bucks )) (PreH31 : (it <> 0)) (PreH32 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH33 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH34 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH35 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ False ”
.

Definition hashtbl_remove_safety_wit_9 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (dl_prev = 0)) (PreH2 : (top = itv)) (PreH3 : (retval = 1)) (PreH4 : (k = k_list)) (PreH5 : (itv <> 0)) (PreH6 : (it <> 0)) (PreH7 : (l_res = (cons (itv) (l_resres)))) (PreH8 : (dl_down = (cons (itv) (dl_downres)))) (PreH9 : (map_composable m1 m2 )) (PreH10 : (node_value_map m1_node m1 )) (PreH11 : (not_key k l_prev m1_node )) (PreH12 : (NoDup l_res )) (PreH13 : ((m1_node (k_list)) = (Some (itv)))) (PreH14 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH15 : (bucket_cells_nonnull h_pre_bucks )) (PreH16 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH17 : (itv <> 0)) (PreH18 : (map_composable m1 m2 )) (PreH19 : (node_value_map m1_node m1 )) (PreH20 : (not_key k l_prev m1_node )) (PreH21 : (NoDup l_res )) (PreH22 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH23 : (0 <= ind)) (PreH24 : (ind < 211)) (PreH25 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH26 : (l0 = (app (l_prev) (l_res)))) (PreH27 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH28 : (repr_all_heads lh bucket_map )) (PreH29 : (contain_all_correct_addrs m1_node bucket_map )) (PreH30 : (bucket_cells_nonnull h_pre_bucks )) (PreH31 : (it <> 0)) (PreH32 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH33 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH34 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH35 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_10 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (dl_prev = 0)) (PreH2 : (top <> itv)) (PreH3 : (retval = 1)) (PreH4 : (k = k_list)) (PreH5 : (itv <> 0)) (PreH6 : (it <> 0)) (PreH7 : (l_res = (cons (itv) (l_resres)))) (PreH8 : (dl_down = (cons (itv) (dl_downres)))) (PreH9 : (map_composable m1 m2 )) (PreH10 : (node_value_map m1_node m1 )) (PreH11 : (not_key k l_prev m1_node )) (PreH12 : (NoDup l_res )) (PreH13 : ((m1_node (k_list)) = (Some (itv)))) (PreH14 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH15 : (bucket_cells_nonnull h_pre_bucks )) (PreH16 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH17 : (itv <> 0)) (PreH18 : (map_composable m1 m2 )) (PreH19 : (node_value_map m1_node m1 )) (PreH20 : (not_key k l_prev m1_node )) (PreH21 : (NoDup l_res )) (PreH22 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH23 : (0 <= ind)) (PreH24 : (ind < 211)) (PreH25 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH26 : (l0 = (app (l_prev) (l_res)))) (PreH27 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH28 : (repr_all_heads lh bucket_map )) (PreH29 : (contain_all_correct_addrs m1_node bucket_map )) (PreH30 : (bucket_cells_nonnull h_pre_bucks )) (PreH31 : (it <> 0)) (PreH32 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH33 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH34 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH35 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_11 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (PreH1 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH2 : (dl_up = (cons (top) (l0_2)))) (PreH3 : (dl_prev <> 0)) (PreH4 : (top <> itv)) (PreH5 : (retval = 1)) (PreH6 : (k = k_list)) (PreH7 : (itv <> 0)) (PreH8 : (it <> 0)) (PreH9 : (l_res = (cons (itv) (l_resres)))) (PreH10 : (dl_down = (cons (itv) (dl_downres)))) (PreH11 : (map_composable m1 m2 )) (PreH12 : (node_value_map m1_node m1 )) (PreH13 : (not_key k l_prev m1_node )) (PreH14 : (NoDup l_res )) (PreH15 : ((m1_node (k_list)) = (Some (itv)))) (PreH16 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH17 : (bucket_cells_nonnull h_pre_bucks )) (PreH18 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH19 : (itv <> 0)) (PreH20 : (map_composable m1 m2 )) (PreH21 : (node_value_map m1_node m1 )) (PreH22 : (not_key k l_prev m1_node )) (PreH23 : (NoDup l_res )) (PreH24 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH25 : (0 <= ind)) (PreH26 : (ind < 211)) (PreH27 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH28 : (l0 = (app (l_prev) (l_res)))) (PreH29 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH30 : (repr_all_heads lh bucket_map )) (PreH31 : (contain_all_correct_addrs m1_node bucket_map )) (PreH32 : (bucket_cells_nonnull h_pre_bucks )) (PreH33 : (it <> 0)) (PreH34 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH35 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH36 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH37 : (retval <> 0)) ,
  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_12 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (b_down <> 0)) (PreH3 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH4 : (dl_up = (cons (top) (l0_2)))) (PreH5 : (dl_prev <> 0)) (PreH6 : (top <> itv)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list)) (PreH9 : (itv <> 0)) (PreH10 : (it <> 0)) (PreH11 : (l_res = (cons (itv) (l_resres)))) (PreH12 : (dl_down = (cons (itv) (dl_downres)))) (PreH13 : (map_composable m1 m2 )) (PreH14 : (node_value_map m1_node m1 )) (PreH15 : (not_key k l_prev m1_node )) (PreH16 : (NoDup l_res )) (PreH17 : ((m1_node (k_list)) = (Some (itv)))) (PreH18 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH19 : (bucket_cells_nonnull h_pre_bucks )) (PreH20 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH21 : (itv <> 0)) (PreH22 : (map_composable m1 m2 )) (PreH23 : (node_value_map m1_node m1 )) (PreH24 : (not_key k l_prev m1_node )) (PreH25 : (NoDup l_res )) (PreH26 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH27 : (0 <= ind)) (PreH28 : (ind < 211)) (PreH29 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH30 : (l0 = (app (l_prev) (l_res)))) (PreH31 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH32 : (repr_all_heads lh bucket_map )) (PreH33 : (contain_all_correct_addrs m1_node bucket_map )) (PreH34 : (bucket_cells_nonnull h_pre_bucks )) (PreH35 : (it <> 0)) (PreH36 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH37 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH38 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH39 : (retval <> 0)) ,
  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_remove_safety_wit_13 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (dl_up = (cons (top) (l0_2)))) (PreH3 : (b_down <> 0)) (PreH4 : (dl_prev = 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_remove_safety_wit_14 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (b_down <> 0)) (PreH3 : (dl_prev = 0)) (PreH4 : (top = itv)) (PreH5 : (retval = 1)) (PreH6 : (k = k_list)) (PreH7 : (itv <> 0)) (PreH8 : (it <> 0)) (PreH9 : (l_res = (cons (itv) (l_resres)))) (PreH10 : (dl_down = (cons (itv) (dl_downres)))) (PreH11 : (map_composable m1 m2 )) (PreH12 : (node_value_map m1_node m1 )) (PreH13 : (not_key k l_prev m1_node )) (PreH14 : (NoDup l_res )) (PreH15 : ((m1_node (k_list)) = (Some (itv)))) (PreH16 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH17 : (bucket_cells_nonnull h_pre_bucks )) (PreH18 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH19 : (itv <> 0)) (PreH20 : (map_composable m1 m2 )) (PreH21 : (node_value_map m1_node m1 )) (PreH22 : (not_key k l_prev m1_node )) (PreH23 : (NoDup l_res )) (PreH24 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH25 : (0 <= ind)) (PreH26 : (ind < 211)) (PreH27 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH28 : (l0 = (app (l_prev) (l_res)))) (PreH29 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH30 : (repr_all_heads lh bucket_map )) (PreH31 : (contain_all_correct_addrs m1_node bucket_map )) (PreH32 : (bucket_cells_nonnull h_pre_bucks )) (PreH33 : (it <> 0)) (PreH34 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH35 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH36 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH37 : (retval <> 0)) ,
  ((( &( "res" ) )) # UInt  |-> val)
  **  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_remove_safety_wit_15 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down = 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top = itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_remove_safety_wit_16 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (PreH1 : (dl_up = (cons (top) (l0_2)))) (PreH2 : (b_down = 0)) (PreH3 : (dl_prev = 0)) (PreH4 : (top <> itv)) (PreH5 : (retval = 1)) (PreH6 : (k = k_list)) (PreH7 : (itv <> 0)) (PreH8 : (it <> 0)) (PreH9 : (l_res = (cons (itv) (l_resres)))) (PreH10 : (dl_down = (cons (itv) (dl_downres)))) (PreH11 : (map_composable m1 m2 )) (PreH12 : (node_value_map m1_node m1 )) (PreH13 : (not_key k l_prev m1_node )) (PreH14 : (NoDup l_res )) (PreH15 : ((m1_node (k_list)) = (Some (itv)))) (PreH16 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH17 : (bucket_cells_nonnull h_pre_bucks )) (PreH18 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH19 : (itv <> 0)) (PreH20 : (map_composable m1 m2 )) (PreH21 : (node_value_map m1_node m1 )) (PreH22 : (not_key k l_prev m1_node )) (PreH23 : (NoDup l_res )) (PreH24 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH25 : (0 <= ind)) (PreH26 : (ind < 211)) (PreH27 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH28 : (l0 = (app (l_prev) (l_res)))) (PreH29 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH30 : (repr_all_heads lh bucket_map )) (PreH31 : (contain_all_correct_addrs m1_node bucket_map )) (PreH32 : (bucket_cells_nonnull h_pre_bucks )) (PreH33 : (it <> 0)) (PreH34 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH35 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH36 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH37 : (retval <> 0)) ,
  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  ((( &( "res" ) )) # UInt  |-> val)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_remove_safety_wit_17 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (PreH1 : (b_down = 0)) (PreH2 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH3 : (dl_up = (cons (top) (l0_2)))) (PreH4 : (dl_prev <> 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  ((( &( "res" ) )) # UInt  |-> val)
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hashtbl_remove_safety_wit_18 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (itv = 0)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (not_key k l_prev m1_node )) (PreH5 : (NoDup l_res )) (PreH6 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH7 : (0 <= ind)) (PreH8 : (ind < 211)) (PreH9 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH10 : (l0 = (app (l_prev) (l_res)))) (PreH11 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH12 : (repr_all_heads lh bucket_map )) (PreH13 : (contain_all_correct_addrs m1_node bucket_map )) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (it <> 0)) (PreH16 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH17 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH18 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_safety_wit_19 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (itv = 0)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (not_key k l_prev m1_node )) (PreH5 : (NoDup l_res )) (PreH6 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH7 : (0 <= ind)) (PreH8 : (ind < 211)) (PreH9 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH10 : (l0 = (app (l_prev) (l_res)))) (PreH11 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH12 : (repr_all_heads lh bucket_map )) (PreH13 : (contain_all_correct_addrs m1_node bucket_map )) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (it <> 0)) (PreH16 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH17 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH18 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_remove_entail_wit_1 := 
(
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_2: Z) (h_bucks: Z) (lh_2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node_2: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m1_node_2 m1 )) (PreH5 : (contain_all_addrs m1_node_2 l )) (PreH6 : (repr_all_heads lh_2 b )) (PreH7 : (contain_all_correct_addrs m1_node_2 b )) (PreH8 : (bucket_cells_nonnull h_bucks )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_2)
  **  (dll top_2 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node_2 )
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
|--
  EX (dl_prev: Z)  (top: Z)  (itv: Z)  (h_pre_bucks: Z)  (lh: (@list Z))  (dl_up: (@list Z))  (dl_down: (@list Z))  (buck: Z)  (l0: (@list Z))  (bucket_map: (Z -> (@option (Z * (@list Z)))))  (l_res: (@list Z))  (l_prev: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ ((bucket_map ((retval % ( 211 ) ))) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ ((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map (retval % ( 211 ) ) )
  **  (sllbseg (h_pre_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) (h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks (retval % ( 211 ) ) 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_2: Z) (h_bucks: Z) (lh_2: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node_2: ((@list Z) -> (@option Z))) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval = (hash_string_k (k)))) (PreH4 : (node_value_map m1_node_2 m1 )) (PreH5 : (contain_all_addrs m1_node_2 l )) (PreH6 : (repr_all_heads lh_2 b )) (PreH7 : (contain_all_correct_addrs m1_node_2 b )) (PreH8 : (bucket_cells_nonnull h_bucks )) (PreH9 : (map_composable m1 m2 )) ,
  (store_string key_pre k )
  **  (dll top_2 0 l )
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node_2 )
  **  (store_map store_uint m2 )
|--
  EX (dl_prev: Z)  (itv: Z)  (lh: (@list Z))  (dl_up: (@list Z))  (dl_down: (@list Z))  (buck: Z)  (bucket_map: (Z -> (@option (Z * (@list Z)))))  (l_res: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ ((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k (@nil Z) m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((retval % ( 211 ) ) = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= (retval % ( 211 ) )) ” 
  &&  “ ((retval % ( 211 ) ) < 211) ” 
  &&  “ ((bucket_map ((retval % ( 211 ) ))) = (Some ((pair (buck) ((app ((@nil Z)) (l_res))))))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ ((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR))) <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top_2 = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top_2 <> 0)) ”
  &&  (((h_bucks + ((retval % ( 211 ) ) * sizeof(PTR)))) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map (retval % ( 211 ) ) )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_bucks (retval % ( 211 ) ) 0 211 lh )
  **  (store_map store_name m1_node )
  **  (dllseg top_2 itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  (store_map store_uint m2 )
).

Definition hashtbl_remove_entail_wit_2_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list)) (PreH3 : (itv <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res = (cons (itv) (l_resres)))) (PreH6 : (dl_down = (cons (itv) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node m1 )) (PreH9 : (not_key k l_prev m1_node )) (PreH10 : (NoDup l_res )) (PreH11 : ((m1_node (k_list)) = (Some (itv)))) (PreH12 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node m1 )) (PreH18 : (not_key k l_prev m1_node )) (PreH19 : (NoDup l_res )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH26 : (repr_all_heads lh bucket_map )) (PreH27 : (contain_all_correct_addrs m1_node bucket_map )) (PreH28 : (bucket_cells_nonnull h_pre_bucks )) (PreH29 : (it <> 0)) (PreH30 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH31 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH32 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH33 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (retval = 0) ” 
  &&  “ (k <> k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval = 0) ”
  &&  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_2_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (k = k_list)) (PreH3 : (itv <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res = (cons (itv) (l_resres)))) (PreH6 : (dl_down = (cons (itv) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node m1 )) (PreH9 : (not_key k l_prev m1_node )) (PreH10 : (NoDup l_res )) (PreH11 : ((m1_node (k_list)) = (Some (itv)))) (PreH12 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node m1 )) (PreH18 : (not_key k l_prev m1_node )) (PreH19 : (NoDup l_res )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH26 : (repr_all_heads lh bucket_map )) (PreH27 : (contain_all_correct_addrs m1_node bucket_map )) (PreH28 : (bucket_cells_nonnull h_pre_bucks )) (PreH29 : (it <> 0)) (PreH30 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH31 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH32 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH33 : (retval_2 = 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (k <> k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval = 0) ”
  &&  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_3_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (k <> k_list)) (PreH3 : (itv <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res = (cons (itv) (l_resres)))) (PreH6 : (dl_down = (cons (itv) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node m1 )) (PreH9 : (not_key k l_prev m1_node )) (PreH10 : (NoDup l_res )) (PreH11 : ((m1_node (k_list)) = (Some (itv)))) (PreH12 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node m1 )) (PreH18 : (not_key k l_prev m1_node )) (PreH19 : (NoDup l_res )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH26 : (repr_all_heads lh bucket_map )) (PreH27 : (contain_all_correct_addrs m1_node bucket_map )) (PreH28 : (bucket_cells_nonnull h_pre_bucks )) (PreH29 : (it <> 0)) (PreH30 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH31 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH32 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH33 : (retval_2 <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_3_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (k = k_list)) (PreH3 : (itv <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res = (cons (itv) (l_resres)))) (PreH6 : (dl_down = (cons (itv) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node m1 )) (PreH9 : (not_key k l_prev m1_node )) (PreH10 : (NoDup l_res )) (PreH11 : ((m1_node (k_list)) = (Some (itv)))) (PreH12 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks )) (PreH14 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node m1 )) (PreH18 : (not_key k l_prev m1_node )) (PreH19 : (NoDup l_res )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH24 : (l0 = (app (l_prev) (l_res)))) (PreH25 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH26 : (repr_all_heads lh bucket_map )) (PreH27 : (contain_all_correct_addrs m1_node bucket_map )) (PreH28 : (bucket_cells_nonnull h_pre_bucks )) (PreH29 : (it <> 0)) (PreH30 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH31 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH32 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH33 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_entail_wit_4 := 
(
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev_2: Z) (top_2: Z) (itv_2: Z) (it: Z) (h_pre_bucks_2: Z) (lh_2: (@list Z)) (dl_up_2: (@list Z)) (dl_down_2: (@list Z)) (buck_2: Z) (l0_2: (@list Z)) (bucket_map_2: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res_2: (@list Z)) (l_prev_2: (@list Z)) (m1_node_2: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (k <> k_list)) (PreH3 : (itv_2 <> 0)) (PreH4 : (it <> 0)) (PreH5 : (l_res_2 = (cons (itv_2) (l_resres)))) (PreH6 : (dl_down_2 = (cons (itv_2) (dl_downres)))) (PreH7 : (map_composable m1 m2 )) (PreH8 : (node_value_map m1_node_2 m1 )) (PreH9 : (not_key k l_prev_2 m1_node_2 )) (PreH10 : (NoDup l_res_2 )) (PreH11 : ((m1_node_2 (k_list)) = (Some (itv_2)))) (PreH12 : ((m2 (&((itv_2)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH13 : (bucket_cells_nonnull h_pre_bucks_2 )) (PreH14 : (&((itv_2)  # "blist" ->ₛ "next") <> 0)) (PreH15 : (itv_2 <> 0)) (PreH16 : (map_composable m1 m2 )) (PreH17 : (node_value_map m1_node_2 m1 )) (PreH18 : (not_key k l_prev_2 m1_node_2 )) (PreH19 : (NoDup l_res_2 )) (PreH20 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH21 : (0 <= ind)) (PreH22 : (ind < 211)) (PreH23 : ((bucket_map_2 (ind)) = (Some ((pair (buck_2) (l0_2)))))) (PreH24 : (l0_2 = (app (l_prev_2) (l_res_2)))) (PreH25 : (contain_all_addrs m1_node_2 (app (dl_up_2) (dl_down_2)) )) (PreH26 : (repr_all_heads lh_2 bucket_map_2 )) (PreH27 : (contain_all_correct_addrs m1_node_2 bucket_map_2 )) (PreH28 : (bucket_cells_nonnull h_pre_bucks_2 )) (PreH29 : (it <> 0)) (PreH30 : ((itv_2 = 0) -> ((l_res_2 = (@nil Z)) /\ (dl_down_2 = (@nil Z))))) (PreH31 : ((top_2 = itv_2) -> ((dl_prev_2 = 0) /\ (dl_up_2 = (@nil Z))))) (PreH32 : ((dl_up_2 <> (@nil Z)) -> (top_2 <> 0))) (PreH33 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  ((it) # Ptr  |-> itv_2)
  **  (store_map_missing_i store_sll bucket_map_2 ind )
  **  (sllbseg (h_pre_bucks_2 + (ind * sizeof(PTR))) it l_prev_2 )
  **  ((&((itv_2)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv_2)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv_2)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv_2)  # "blist" ->ₛ "val") )
  **  ((&((itv_2)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv_2)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_2)
  **  (dll b_down itv_2 dl_downres )
  **  (store_map_missing_i store_name m1_node_2 k_list )
  **  (PtrArray.missing_i h_pre_bucks_2 ind 0 211 lh_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_2)
  **  (dllseg top_2 itv_2 0 dl_prev_2 dl_up_2 )
  **  ((removed_pre) # Int  |->_)
|--
  EX (dl_prev: Z)  (top: Z)  (itv: Z)  (h_pre_bucks: Z)  (lh: (@list Z))  (dl_up: (@list Z))  (dl_down: (@list Z))  (buck: Z)  (l0: (@list Z))  (bucket_map: (Z -> (@option (Z * (@list Z)))))  (l_res: (@list Z))  (l_prev: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((&((itv_2)  # "blist" ->ₛ "next")) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) &((itv_2)  # "blist" ->ₛ "next") l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
) \/
(
forall (key_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev_2: Z) (top_2: Z) (itv_2: Z) (it: Z) (h_pre_bucks_2: Z) (lh_2: (@list Z)) (dl_up_2: (@list Z)) (dl_down_2: (@list Z)) (buck_2: Z) (l0_2: (@list Z)) (bucket_map_2: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res_2: (@list Z)) (l_prev_2: (@list Z)) (m1_node_2: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (val <= UINT_MAX)) (PreH2 : (val >= 0)) (PreH3 : (retval = 0)) (PreH4 : (k <> k_list)) (PreH5 : (itv_2 <> 0)) (PreH6 : (it <> 0)) (PreH7 : (l_res_2 = (cons (itv_2) (l_resres)))) (PreH8 : (dl_down_2 = (cons (itv_2) (dl_downres)))) (PreH9 : (map_composable m1 m2 )) (PreH10 : (node_value_map m1_node_2 m1 )) (PreH11 : (not_key k l_prev_2 m1_node_2 )) (PreH12 : (NoDup l_res_2 )) (PreH13 : ((m1_node_2 (k_list)) = (Some (itv_2)))) (PreH14 : ((m2 (&((itv_2)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH15 : (bucket_cells_nonnull h_pre_bucks_2 )) (PreH16 : (&((itv_2)  # "blist" ->ₛ "next") <> 0)) (PreH17 : (itv_2 <> 0)) (PreH18 : (map_composable m1 m2 )) (PreH19 : (node_value_map m1_node_2 m1 )) (PreH20 : (not_key k l_prev_2 m1_node_2 )) (PreH21 : (NoDup l_res_2 )) (PreH22 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH23 : (0 <= ind)) (PreH24 : (ind < 211)) (PreH25 : ((bucket_map_2 (ind)) = (Some ((pair (buck_2) (l0_2)))))) (PreH26 : (l0_2 = (app (l_prev_2) (l_res_2)))) (PreH27 : (contain_all_addrs m1_node_2 (app (dl_up_2) (dl_down_2)) )) (PreH28 : (repr_all_heads lh_2 bucket_map_2 )) (PreH29 : (contain_all_correct_addrs m1_node_2 bucket_map_2 )) (PreH30 : (bucket_cells_nonnull h_pre_bucks_2 )) (PreH31 : (it <> 0)) (PreH32 : ((itv_2 = 0) -> ((l_res_2 = (@nil Z)) /\ (dl_down_2 = (@nil Z))))) (PreH33 : ((top_2 = itv_2) -> ((dl_prev_2 = 0) /\ (dl_up_2 = (@nil Z))))) (PreH34 : ((dl_up_2 <> (@nil Z)) -> (top_2 <> 0))) (PreH35 : (retval = 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((it) # Ptr  |-> itv_2)
  **  (store_map_missing_i store_sll bucket_map_2 ind )
  **  (sllbseg (h_pre_bucks_2 + (ind * sizeof(PTR))) it l_prev_2 )
  **  ((&((itv_2)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv_2)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv_2)  # "blist" ->ₛ "val") )
  **  ((&((itv_2)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv_2)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_2)
  **  (dll b_down itv_2 dl_downres )
  **  (store_map_missing_i store_name m1_node_2 k_list )
  **  (PtrArray.missing_i h_pre_bucks_2 ind 0 211 lh_2 )
  **  (dllseg top_2 itv_2 0 dl_prev_2 dl_up_2 )
|--
  EX (dl_prev: Z)  (lh: (@list Z))  (dl_up: (@list Z))  (dl_down: (@list Z))  (buck: Z)  (bucket_map: (Z -> (@option (Z * (@list Z)))))  (l_prev: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_resres ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) ((app (l_prev) (l_resres))))))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks_2 ) ” 
  &&  “ (&((itv_2)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ ((b_next = 0) -> ((l_resres = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top_2 = b_next) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top_2 <> 0)) ”
  &&  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks_2 + (ind * sizeof(PTR))) &((itv_2)  # "blist" ->ₛ "next") l_prev )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks_2 ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  (dllseg top_2 b_next 0 dl_prev dl_up )
  **  (dll b_next dl_prev dl_down )
  **  (store_map store_uint m2 )
).

Definition hashtbl_remove_return_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (itv = 0)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (not_key k l_prev m1_node )) (PreH5 : (NoDup l_res )) (PreH6 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH7 : (0 <= ind)) (PreH8 : (ind < 211)) (PreH9 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH10 : (l0 = (app (l_prev) (l_res)))) (PreH11 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH12 : (repr_all_heads lh bucket_map )) (PreH13 : (contain_all_correct_addrs m1_node bucket_map )) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (it <> 0)) (PreH16 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH17 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH18 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 )
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (0 = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (0 = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (b_down <> 0)) (PreH3 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH4 : (dl_up = (cons (top) (l0_2)))) (PreH5 : (dl_prev <> 0)) (PreH6 : (top <> itv)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list)) (PreH9 : (itv <> 0)) (PreH10 : (it <> 0)) (PreH11 : (l_res = (cons (itv) (l_resres)))) (PreH12 : (dl_down = (cons (itv) (dl_downres)))) (PreH13 : (map_composable m1 m2 )) (PreH14 : (node_value_map m1_node m1 )) (PreH15 : (not_key k l_prev m1_node )) (PreH16 : (NoDup l_res )) (PreH17 : ((m1_node (k_list)) = (Some (itv)))) (PreH18 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH19 : (bucket_cells_nonnull h_pre_bucks )) (PreH20 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH21 : (itv <> 0)) (PreH22 : (map_composable m1 m2 )) (PreH23 : (node_value_map m1_node m1 )) (PreH24 : (not_key k l_prev m1_node )) (PreH25 : (NoDup l_res )) (PreH26 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH27 : (0 <= ind)) (PreH28 : (ind < 211)) (PreH29 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH30 : (l0 = (app (l_prev) (l_res)))) (PreH31 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH32 : (repr_all_heads lh bucket_map )) (PreH33 : (contain_all_correct_addrs m1_node bucket_map )) (PreH34 : (bucket_cells_nonnull h_pre_bucks )) (PreH35 : (it <> 0)) (PreH36 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH37 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH38 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH39 : (retval <> 0)) ,
  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |-> 1)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (val = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (val = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_3 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (dl_up = (cons (top) (l0_2)))) (PreH3 : (b_down <> 0)) (PreH4 : (dl_prev = 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |-> 1)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (val = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (val = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_4 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (b_down <> 0)) (PreH3 : (dl_prev = 0)) (PreH4 : (top = itv)) (PreH5 : (retval = 1)) (PreH6 : (k = k_list)) (PreH7 : (itv <> 0)) (PreH8 : (it <> 0)) (PreH9 : (l_res = (cons (itv) (l_resres)))) (PreH10 : (dl_down = (cons (itv) (dl_downres)))) (PreH11 : (map_composable m1 m2 )) (PreH12 : (node_value_map m1_node m1 )) (PreH13 : (not_key k l_prev m1_node )) (PreH14 : (NoDup l_res )) (PreH15 : ((m1_node (k_list)) = (Some (itv)))) (PreH16 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH17 : (bucket_cells_nonnull h_pre_bucks )) (PreH18 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH19 : (itv <> 0)) (PreH20 : (map_composable m1 m2 )) (PreH21 : (node_value_map m1_node m1 )) (PreH22 : (not_key k l_prev m1_node )) (PreH23 : (NoDup l_res )) (PreH24 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH25 : (0 <= ind)) (PreH26 : (ind < 211)) (PreH27 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH28 : (l0 = (app (l_prev) (l_res)))) (PreH29 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH30 : (repr_all_heads lh bucket_map )) (PreH31 : (contain_all_correct_addrs m1_node bucket_map )) (PreH32 : (bucket_cells_nonnull h_pre_bucks )) (PreH33 : (it <> 0)) (PreH34 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH35 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH36 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH37 : (retval <> 0)) ,
  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |-> 1)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (val = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (val = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_5 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down = 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top = itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |-> 1)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (val = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (val = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_6 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (PreH1 : (dl_up = (cons (top) (l0_2)))) (PreH2 : (b_down = 0)) (PreH3 : (dl_prev = 0)) (PreH4 : (top <> itv)) (PreH5 : (retval = 1)) (PreH6 : (k = k_list)) (PreH7 : (itv <> 0)) (PreH8 : (it <> 0)) (PreH9 : (l_res = (cons (itv) (l_resres)))) (PreH10 : (dl_down = (cons (itv) (dl_downres)))) (PreH11 : (map_composable m1 m2 )) (PreH12 : (node_value_map m1_node m1 )) (PreH13 : (not_key k l_prev m1_node )) (PreH14 : (NoDup l_res )) (PreH15 : ((m1_node (k_list)) = (Some (itv)))) (PreH16 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH17 : (bucket_cells_nonnull h_pre_bucks )) (PreH18 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH19 : (itv <> 0)) (PreH20 : (map_composable m1 m2 )) (PreH21 : (node_value_map m1_node m1 )) (PreH22 : (not_key k l_prev m1_node )) (PreH23 : (NoDup l_res )) (PreH24 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH25 : (0 <= ind)) (PreH26 : (ind < 211)) (PreH27 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH28 : (l0 = (app (l_prev) (l_res)))) (PreH29 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH30 : (repr_all_heads lh bucket_map )) (PreH31 : (contain_all_correct_addrs m1_node bucket_map )) (PreH32 : (bucket_cells_nonnull h_pre_bucks )) (PreH33 : (it <> 0)) (PreH34 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH35 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH36 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH37 : (retval <> 0)) ,
  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |-> 1)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (val = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (val = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_return_wit_7 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (PreH1 : (b_down = 0)) (PreH2 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH3 : (dl_up = (cons (top) (l0_2)))) (PreH4 : (dl_prev <> 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |-> 1)
|--
  (“ ((m1 (k)) = None) ” 
  &&  “ (val = 0) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 0)
  **  (store_map store_uint m2 ))
  ||
  (EX (p_down: Z)  (p_up: Z)  (key0: Z)  (v: Z)  (p: Z) ,
  “ ((m1 (k)) = (Some (&((p)  # "blist" ->ₛ "val")))) ” 
  &&  “ ((m2 (&((p)  # "blist" ->ₛ "val"))) = (Some (v))) ” 
  &&  “ (val = v) ”
  &&  (store_hash_skeleton h_pre (KP.remove_map (m1) (k)) )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |-> 1)
  **  (store_map store_uint (PV.remove_map (m2) (&((p)  # "blist" ->ₛ "val"))) )
  **  ((&((p)  # "blist" ->ₛ "key")) # Ptr  |-> key0)
  **  (store_string key0 k )
  **  ((&((p)  # "blist" ->ₛ "up")) # Ptr  |-> p_up)
  **  ((&((p)  # "blist" ->ₛ "down")) # Ptr  |-> p_down)
  **  ((&((p)  # "blist" ->ₛ "val")) # UInt  |-> v))
.

Definition hashtbl_remove_partial_solve_wit_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) ,
  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |->_)
|--
  “ (map_composable m1 m2 ) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_2 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node m1 )) (PreH2 : (contain_all_addrs m1_node l )) (PreH3 : (repr_all_heads lh b )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (bucket_cells_nonnull h_bucks )) (PreH6 : (map_composable m1 m2 )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
  **  (store_map store_uint m2 )
  **  (store_string key_pre k )
  **  ((removed_pre) # Int  |->_)
|--
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_addrs m1_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ” 
  &&  “ (map_composable m1 m2 ) ”
  &&  (store_string key_pre k )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
  **  (store_map store_uint m2 )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_3_pure := 
(
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (itv <> 0)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (not_key k l_prev m1_node )) (PreH5 : (NoDup l_res )) (PreH6 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH7 : (0 <= ind)) (PreH8 : (ind < 211)) (PreH9 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH10 : (l0 = (app (l_prev) (l_res)))) (PreH11 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH12 : (repr_all_heads lh bucket_map )) (PreH13 : (contain_all_correct_addrs m1_node bucket_map )) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (it <> 0)) (PreH16 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH17 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH18 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
|--
  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (current_bucket_suffix m1_node bucket_map ind l_prev l_res ) ”
) \/
(
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (ind <= UINT_MAX)) (PreH2 : (ind >= 0)) (PreH3 : (itv <> 0)) (PreH4 : (map_composable m1 m2 )) (PreH5 : (node_value_map m1_node m1 )) (PreH6 : (not_key k l_prev m1_node )) (PreH7 : (NoDup l_res )) (PreH8 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH9 : (0 <= ind)) (PreH10 : (ind < 211)) (PreH11 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH12 : (l0 = (app (l_prev) (l_res)))) (PreH13 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH14 : (repr_all_heads lh bucket_map )) (PreH15 : (contain_all_correct_addrs m1_node bucket_map )) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (it <> 0)) (PreH18 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH19 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH20 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
|--
  “ (current_bucket_suffix m1_node bucket_map ind l_prev l_res ) ”
).

Definition hashtbl_remove_partial_solve_wit_3_pure_split_goal_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (ind <= UINT_MAX)) (PreH2 : (ind >= 0)) (PreH3 : (itv <> 0)) (PreH4 : (map_composable m1 m2 )) (PreH5 : (node_value_map m1_node m1 )) (PreH6 : (not_key k l_prev m1_node )) (PreH7 : (NoDup l_res )) (PreH8 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH9 : (0 <= ind)) (PreH10 : (ind < 211)) (PreH11 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH12 : (l0 = (app (l_prev) (l_res)))) (PreH13 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH14 : (repr_all_heads lh bucket_map )) (PreH15 : (contain_all_correct_addrs m1_node bucket_map )) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (it <> 0)) (PreH18 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH19 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH20 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
|--
  “ (current_bucket_suffix m1_node bucket_map ind l_prev l_res ) ”
.

Definition hashtbl_remove_partial_solve_wit_3_aux := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (itv <> 0)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (not_key k l_prev m1_node )) (PreH5 : (NoDup l_res )) (PreH6 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH7 : (0 <= ind)) (PreH8 : (ind < 211)) (PreH9 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH10 : (l0 = (app (l_prev) (l_res)))) (PreH11 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH12 : (repr_all_heads lh bucket_map )) (PreH13 : (contain_all_correct_addrs m1_node bucket_map )) (PreH14 : (bucket_cells_nonnull h_pre_bucks )) (PreH15 : (it <> 0)) (PreH16 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH17 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH18 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  (store_map store_name m1_node )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  (dll itv dl_prev dl_down )
  **  ((removed_pre) # Int  |->_)
  **  (store_map store_uint m2 )
|--
  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (current_bucket_suffix m1_node bucket_map ind l_prev l_res ) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (store_map store_name m1_node )
  **  (dll itv dl_prev dl_down )
  **  (store_map store_uint m2 )
  **  (sll itv l_res )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_3 := hashtbl_remove_partial_solve_wit_3_pure -> hashtbl_remove_partial_solve_wit_3_aux.

Definition hashtbl_remove_partial_solve_wit_4 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (PreH1 : (itv <> 0)) (PreH2 : (it <> 0)) (PreH3 : (l_res = (cons (itv) (l_resres)))) (PreH4 : (dl_down = (cons (itv) (dl_downres)))) (PreH5 : (map_composable m1 m2 )) (PreH6 : (node_value_map m1_node m1 )) (PreH7 : (not_key k l_prev m1_node )) (PreH8 : (NoDup l_res )) (PreH9 : ((m1_node (k_list)) = (Some (itv)))) (PreH10 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH11 : (bucket_cells_nonnull h_pre_bucks )) (PreH12 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH13 : (itv <> 0)) (PreH14 : (map_composable m1 m2 )) (PreH15 : (node_value_map m1_node m1 )) (PreH16 : (not_key k l_prev m1_node )) (PreH17 : (NoDup l_res )) (PreH18 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH19 : (0 <= ind)) (PreH20 : (ind < 211)) (PreH21 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH22 : (l0 = (app (l_prev) (l_res)))) (PreH23 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH24 : (repr_all_heads lh bucket_map )) (PreH25 : (contain_all_correct_addrs m1_node bucket_map )) (PreH26 : (bucket_cells_nonnull h_pre_bucks )) (PreH27 : (it <> 0)) (PreH28 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH29 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH30 : ((dl_up <> (@nil Z)) -> (top <> 0))) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  (store_string b_key k_list )
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (store_string key_pre k )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ”
  &&  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_5_pure := 
(
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0_2: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0: (@list Z)) (PreH1 : (dl_prev <> 0)) (PreH2 : (top <> itv)) (PreH3 : (retval = 1)) (PreH4 : (k = k_list)) (PreH5 : (itv <> 0)) (PreH6 : (it <> 0)) (PreH7 : (l_res = (cons (itv) (l_resres)))) (PreH8 : (dl_down = (cons (itv) (dl_downres)))) (PreH9 : (map_composable m1 m2 )) (PreH10 : (node_value_map m1_node m1 )) (PreH11 : (not_key k l_prev m1_node )) (PreH12 : (NoDup l_res )) (PreH13 : ((m1_node (k_list)) = (Some (itv)))) (PreH14 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH15 : (bucket_cells_nonnull h_pre_bucks )) (PreH16 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH17 : (itv <> 0)) (PreH18 : (map_composable m1 m2 )) (PreH19 : (node_value_map m1_node m1 )) (PreH20 : (not_key k l_prev m1_node )) (PreH21 : (NoDup l_res )) (PreH22 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH23 : (0 <= ind)) (PreH24 : (ind < 211)) (PreH25 : ((bucket_map (ind)) = (Some ((pair (buck) (l0_2)))))) (PreH26 : (l0_2 = (app (l_prev) (l_res)))) (PreH27 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH28 : (repr_all_heads lh bucket_map )) (PreH29 : (contain_all_correct_addrs m1_node bucket_map )) (PreH30 : (bucket_cells_nonnull h_pre_bucks )) (PreH31 : (it <> 0)) (PreH32 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH33 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH34 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH35 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (dl_prev <> 0) ” 
  &&  “ ((cons (top) (l0)) = (cons (top) (l0))) ” 
  &&  “ (top <> 0) ”
) \/
(
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0_2: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z_2: Z) (l0_3: (@list Z)) (PreH1 : (val <= UINT_MAX)) (PreH2 : (ind <= UINT_MAX)) (PreH3 : (val >= 0)) (PreH4 : (ind >= 0)) (PreH5 : (dl_up = (cons (top) (l0_3)))) (PreH6 : (dl_prev <> 0)) (PreH7 : (top <> itv)) (PreH8 : (retval = 1)) (PreH9 : (k = k_list)) (PreH10 : (itv <> 0)) (PreH11 : (it <> 0)) (PreH12 : (l_res = (cons (itv) (l_resres)))) (PreH13 : (dl_down = (cons (itv) (dl_downres)))) (PreH14 : (map_composable m1 m2 )) (PreH15 : (node_value_map m1_node m1 )) (PreH16 : (not_key k l_prev m1_node )) (PreH17 : (NoDup l_res )) (PreH18 : ((m1_node (k_list)) = (Some (itv)))) (PreH19 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH20 : (bucket_cells_nonnull h_pre_bucks )) (PreH21 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH22 : (itv <> 0)) (PreH23 : (map_composable m1 m2 )) (PreH24 : (node_value_map m1_node m1 )) (PreH25 : (not_key k l_prev m1_node )) (PreH26 : (NoDup l_res )) (PreH27 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH28 : (0 <= ind)) (PreH29 : (ind < 211)) (PreH30 : ((bucket_map (ind)) = (Some ((pair (buck) (l0_2)))))) (PreH31 : (l0_2 = (app (l_prev) (l_res)))) (PreH32 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH33 : (repr_all_heads lh bucket_map )) (PreH34 : (contain_all_correct_addrs m1_node bucket_map )) (PreH35 : (bucket_cells_nonnull h_pre_bucks )) (PreH36 : (it <> 0)) (PreH37 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH38 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH39 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH40 : (retval <> 0)) ,
  (dllseg z_2 itv top dl_prev l0_3 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z_2)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (top <> 0) ”
).

Definition hashtbl_remove_partial_solve_wit_5_pure_split_goal_1 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0_2: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z_2: Z) (l0_3: (@list Z)) (PreH1 : (val <= UINT_MAX)) (PreH2 : (ind <= UINT_MAX)) (PreH3 : (val >= 0)) (PreH4 : (ind >= 0)) (PreH5 : (dl_up = (cons (top) (l0_3)))) (PreH6 : (dl_prev <> 0)) (PreH7 : (top <> itv)) (PreH8 : (retval = 1)) (PreH9 : (k = k_list)) (PreH10 : (itv <> 0)) (PreH11 : (it <> 0)) (PreH12 : (l_res = (cons (itv) (l_resres)))) (PreH13 : (dl_down = (cons (itv) (dl_downres)))) (PreH14 : (map_composable m1 m2 )) (PreH15 : (node_value_map m1_node m1 )) (PreH16 : (not_key k l_prev m1_node )) (PreH17 : (NoDup l_res )) (PreH18 : ((m1_node (k_list)) = (Some (itv)))) (PreH19 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH20 : (bucket_cells_nonnull h_pre_bucks )) (PreH21 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH22 : (itv <> 0)) (PreH23 : (map_composable m1 m2 )) (PreH24 : (node_value_map m1_node m1 )) (PreH25 : (not_key k l_prev m1_node )) (PreH26 : (NoDup l_res )) (PreH27 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH28 : (0 <= ind)) (PreH29 : (ind < 211)) (PreH30 : ((bucket_map (ind)) = (Some ((pair (buck) (l0_2)))))) (PreH31 : (l0_2 = (app (l_prev) (l_res)))) (PreH32 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH33 : (repr_all_heads lh bucket_map )) (PreH34 : (contain_all_correct_addrs m1_node bucket_map )) (PreH35 : (bucket_cells_nonnull h_pre_bucks )) (PreH36 : (it <> 0)) (PreH37 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH38 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH39 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH40 : (retval <> 0)) ,
  (dllseg z_2 itv top dl_prev l0_3 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z_2)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (top <> 0) ”
.

Definition hashtbl_remove_partial_solve_wit_5_aux := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0_2: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (dl_prev <> 0)) (PreH2 : (top <> itv)) (PreH3 : (retval = 1)) (PreH4 : (k = k_list)) (PreH5 : (itv <> 0)) (PreH6 : (it <> 0)) (PreH7 : (l_res = (cons (itv) (l_resres)))) (PreH8 : (dl_down = (cons (itv) (dl_downres)))) (PreH9 : (map_composable m1 m2 )) (PreH10 : (node_value_map m1_node m1 )) (PreH11 : (not_key k l_prev m1_node )) (PreH12 : (NoDup l_res )) (PreH13 : ((m1_node (k_list)) = (Some (itv)))) (PreH14 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH15 : (bucket_cells_nonnull h_pre_bucks )) (PreH16 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH17 : (itv <> 0)) (PreH18 : (map_composable m1 m2 )) (PreH19 : (node_value_map m1_node m1 )) (PreH20 : (not_key k l_prev m1_node )) (PreH21 : (NoDup l_res )) (PreH22 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH23 : (0 <= ind)) (PreH24 : (ind < 211)) (PreH25 : ((bucket_map (ind)) = (Some ((pair (buck) (l0_2)))))) (PreH26 : (l0_2 = (app (l_prev) (l_res)))) (PreH27 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH28 : (repr_all_heads lh bucket_map )) (PreH29 : (contain_all_correct_addrs m1_node bucket_map )) (PreH30 : (bucket_cells_nonnull h_pre_bucks )) (PreH31 : (it <> 0)) (PreH32 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH33 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH34 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH35 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  EX (z: Z)  (l0: (@list Z)) ,
  “ (dl_prev <> 0) ” 
  &&  “ ((cons (top) (l0)) = (cons (top) (l0))) ” 
  &&  “ (top <> 0) ” 
  &&  “ (dl_up = (cons (top) (l0))) ” 
  &&  “ (dl_prev <> 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0_2))))) ” 
  &&  “ (l0_2 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (dllseg z itv top dl_prev l0 )
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_5 := hashtbl_remove_partial_solve_wit_5_pure -> hashtbl_remove_partial_solve_wit_5_aux.

Definition hashtbl_remove_partial_solve_wit_6_pure := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (PreH1 : (b_down <> 0)) (PreH2 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH3 : (dl_up = (cons (top) (l0_2)))) (PreH4 : (dl_prev <> 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down <> 0) ”
.

Definition hashtbl_remove_partial_solve_wit_6_aux := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (PreH1 : (b_down <> 0)) (PreH2 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH3 : (dl_up = (cons (top) (l0_2)))) (PreH4 : (dl_prev <> 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down <> 0) ” 
  &&  “ (b_down <> 0) ” 
  &&  “ ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z)))))) ” 
  &&  “ (dl_up = (cons (top) (l0_2))) ” 
  &&  “ (dl_prev <> 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  (dll b_down itv dl_downres )
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_6 := hashtbl_remove_partial_solve_wit_6_pure -> hashtbl_remove_partial_solve_wit_6_aux.

Definition hashtbl_remove_partial_solve_wit_7_pure := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down <> 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top <> itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down <> 0) ”
.

Definition hashtbl_remove_partial_solve_wit_7_aux := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down <> 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top <> itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  EX (z: Z)  (l0_2: (@list Z)) ,
  “ (b_down <> 0) ” 
  &&  “ (dl_up = (cons (top) (l0_2))) ” 
  &&  “ (b_down <> 0) ” 
  &&  “ (dl_prev = 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  (dll b_down itv dl_downres )
  **  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_7 := hashtbl_remove_partial_solve_wit_7_pure -> hashtbl_remove_partial_solve_wit_7_aux.

Definition hashtbl_remove_partial_solve_wit_8_pure := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down <> 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top = itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((( &( "b" ) )) # Ptr  |-> itv)
  **  ((( &( "it" ) )) # Ptr  |-> it)
  **  ((( &( "removed" ) )) # Ptr  |-> removed_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  ((( &( "ind" ) )) # UInt  |-> ind)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down <> 0) ”
.

Definition hashtbl_remove_partial_solve_wit_8_aux := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down <> 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top = itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down <> 0) ” 
  &&  “ (b_down <> 0) ” 
  &&  “ (dl_prev = 0) ” 
  &&  “ (top = itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  (dll b_down itv dl_downres )
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> itv)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_8 := hashtbl_remove_partial_solve_wit_8_pure -> hashtbl_remove_partial_solve_wit_8_aux.

Definition hashtbl_remove_partial_solve_wit_9 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (b_down <> 0)) (PreH3 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH4 : (dl_up = (cons (top) (l0_2)))) (PreH5 : (dl_prev <> 0)) (PreH6 : (top <> itv)) (PreH7 : (retval = 1)) (PreH8 : (k = k_list)) (PreH9 : (itv <> 0)) (PreH10 : (it <> 0)) (PreH11 : (l_res = (cons (itv) (l_resres)))) (PreH12 : (dl_down = (cons (itv) (dl_downres)))) (PreH13 : (map_composable m1 m2 )) (PreH14 : (node_value_map m1_node m1 )) (PreH15 : (not_key k l_prev m1_node )) (PreH16 : (NoDup l_res )) (PreH17 : ((m1_node (k_list)) = (Some (itv)))) (PreH18 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH19 : (bucket_cells_nonnull h_pre_bucks )) (PreH20 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH21 : (itv <> 0)) (PreH22 : (map_composable m1 m2 )) (PreH23 : (node_value_map m1_node m1 )) (PreH24 : (not_key k l_prev m1_node )) (PreH25 : (NoDup l_res )) (PreH26 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH27 : (0 <= ind)) (PreH28 : (ind < 211)) (PreH29 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH30 : (l0 = (app (l_prev) (l_res)))) (PreH31 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH32 : (repr_all_heads lh bucket_map )) (PreH33 : (contain_all_correct_addrs m1_node bucket_map )) (PreH34 : (bucket_cells_nonnull h_pre_bucks )) (PreH35 : (it <> 0)) (PreH36 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH37 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH38 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH39 : (retval <> 0)) ,
  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (dl_downres = (cons (b_down) (dl_down_tail))) ” 
  &&  “ (b_down <> 0) ” 
  &&  “ ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z)))))) ” 
  &&  “ (dl_up = (cons (top) (l0_2))) ” 
  &&  “ (dl_prev <> 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_10 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (z: Z) (l0_2: (@list Z)) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (dl_up = (cons (top) (l0_2)))) (PreH3 : (b_down <> 0)) (PreH4 : (dl_prev = 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (dl_downres = (cons (b_down) (dl_down_tail))) ” 
  &&  “ (dl_up = (cons (top) (l0_2))) ” 
  &&  “ (b_down <> 0) ” 
  &&  “ (dl_prev = 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_11 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (b_down_down: Z) (dl_down_tail: (@list Z)) (PreH1 : (dl_downres = (cons (b_down) (dl_down_tail)))) (PreH2 : (b_down <> 0)) (PreH3 : (dl_prev = 0)) (PreH4 : (top = itv)) (PreH5 : (retval = 1)) (PreH6 : (k = k_list)) (PreH7 : (itv <> 0)) (PreH8 : (it <> 0)) (PreH9 : (l_res = (cons (itv) (l_resres)))) (PreH10 : (dl_down = (cons (itv) (dl_downres)))) (PreH11 : (map_composable m1 m2 )) (PreH12 : (node_value_map m1_node m1 )) (PreH13 : (not_key k l_prev m1_node )) (PreH14 : (NoDup l_res )) (PreH15 : ((m1_node (k_list)) = (Some (itv)))) (PreH16 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH17 : (bucket_cells_nonnull h_pre_bucks )) (PreH18 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH19 : (itv <> 0)) (PreH20 : (map_composable m1 m2 )) (PreH21 : (node_value_map m1_node m1 )) (PreH22 : (not_key k l_prev m1_node )) (PreH23 : (NoDup l_res )) (PreH24 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH25 : (0 <= ind)) (PreH26 : (ind < 211)) (PreH27 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH28 : (l0 = (app (l_prev) (l_res)))) (PreH29 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH30 : (repr_all_heads lh bucket_map )) (PreH31 : (contain_all_correct_addrs m1_node bucket_map )) (PreH32 : (bucket_cells_nonnull h_pre_bucks )) (PreH33 : (it <> 0)) (PreH34 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH35 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH36 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH37 : (retval <> 0)) ,
  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (dl_downres = (cons (b_down) (dl_down_tail))) ” 
  &&  “ (b_down <> 0) ” 
  &&  “ (dl_prev = 0) ” 
  &&  “ (top = itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down_down b_down dl_down_tail )
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_12 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down = 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top = itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down = 0) ” 
  &&  “ (dl_prev = 0) ” 
  &&  “ (top = itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> b_down)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_13 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (PreH1 : (b_down = 0)) (PreH2 : (dl_prev = 0)) (PreH3 : (top <> itv)) (PreH4 : (retval = 1)) (PreH5 : (k = k_list)) (PreH6 : (itv <> 0)) (PreH7 : (it <> 0)) (PreH8 : (l_res = (cons (itv) (l_resres)))) (PreH9 : (dl_down = (cons (itv) (dl_downres)))) (PreH10 : (map_composable m1 m2 )) (PreH11 : (node_value_map m1_node m1 )) (PreH12 : (not_key k l_prev m1_node )) (PreH13 : (NoDup l_res )) (PreH14 : ((m1_node (k_list)) = (Some (itv)))) (PreH15 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH16 : (bucket_cells_nonnull h_pre_bucks )) (PreH17 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH18 : (itv <> 0)) (PreH19 : (map_composable m1 m2 )) (PreH20 : (node_value_map m1_node m1 )) (PreH21 : (not_key k l_prev m1_node )) (PreH22 : (NoDup l_res )) (PreH23 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH24 : (0 <= ind)) (PreH25 : (ind < 211)) (PreH26 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH27 : (l0 = (app (l_prev) (l_res)))) (PreH28 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH29 : (repr_all_heads lh bucket_map )) (PreH30 : (contain_all_correct_addrs m1_node bucket_map )) (PreH31 : (bucket_cells_nonnull h_pre_bucks )) (PreH32 : (it <> 0)) (PreH33 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH34 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH35 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH36 : (retval <> 0)) ,
  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dllseg top itv 0 dl_prev dl_up )
  **  ((removed_pre) # Int  |->_)
|--
  EX (z: Z)  (l0_2: (@list Z)) ,
  “ (dl_up = (cons (top) (l0_2))) ” 
  &&  “ (b_down = 0) ” 
  &&  “ (dl_prev = 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (dllseg z itv top dl_prev l0_2 )
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> z)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_partial_solve_wit_14 := 
forall (removed_pre: Z) (key_pre: Z) (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (dl_prev: Z) (top: Z) (itv: Z) (it: Z) (h_pre_bucks: Z) (lh: (@list Z)) (dl_up: (@list Z)) (dl_down: (@list Z)) (buck: Z) (l0: (@list Z)) (bucket_map: (Z -> (@option (Z * (@list Z))))) (ind: Z) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b_down: Z) (b_key: Z) (b_next: Z) (val: Z) (k_list: (@list Z)) (dl_downres: (@list Z)) (l_resres: (@list Z)) (retval: Z) (l0_2: (@list Z)) (dl_prev_prev: Z) (dl_up_prefix: (@list Z)) (PreH1 : (b_down = 0)) (PreH2 : ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z))))))) (PreH3 : (dl_up = (cons (top) (l0_2)))) (PreH4 : (dl_prev <> 0)) (PreH5 : (top <> itv)) (PreH6 : (retval = 1)) (PreH7 : (k = k_list)) (PreH8 : (itv <> 0)) (PreH9 : (it <> 0)) (PreH10 : (l_res = (cons (itv) (l_resres)))) (PreH11 : (dl_down = (cons (itv) (dl_downres)))) (PreH12 : (map_composable m1 m2 )) (PreH13 : (node_value_map m1_node m1 )) (PreH14 : (not_key k l_prev m1_node )) (PreH15 : (NoDup l_res )) (PreH16 : ((m1_node (k_list)) = (Some (itv)))) (PreH17 : ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val)))) (PreH18 : (bucket_cells_nonnull h_pre_bucks )) (PreH19 : (&((itv)  # "blist" ->ₛ "next") <> 0)) (PreH20 : (itv <> 0)) (PreH21 : (map_composable m1 m2 )) (PreH22 : (node_value_map m1_node m1 )) (PreH23 : (not_key k l_prev m1_node )) (PreH24 : (NoDup l_res )) (PreH25 : (ind = ((hash_string_k (k)) % ( 211 ) ))) (PreH26 : (0 <= ind)) (PreH27 : (ind < 211)) (PreH28 : ((bucket_map (ind)) = (Some ((pair (buck) (l0)))))) (PreH29 : (l0 = (app (l_prev) (l_res)))) (PreH30 : (contain_all_addrs m1_node (app (dl_up) (dl_down)) )) (PreH31 : (repr_all_heads lh bucket_map )) (PreH32 : (contain_all_correct_addrs m1_node bucket_map )) (PreH33 : (bucket_cells_nonnull h_pre_bucks )) (PreH34 : (it <> 0)) (PreH35 : ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z))))) (PreH36 : ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z))))) (PreH37 : ((dl_up <> (@nil Z)) -> (top <> 0))) (PreH38 : (retval <> 0)) ,
  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
|--
  “ (b_down = 0) ” 
  &&  “ ((cons (top) (l0_2)) = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z)))))) ” 
  &&  “ (dl_up = (cons (top) (l0_2))) ” 
  &&  “ (dl_prev <> 0) ” 
  &&  “ (top <> itv) ” 
  &&  “ (retval = 1) ” 
  &&  “ (k = k_list) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (itv) (l_resres))) ” 
  &&  “ (dl_down = (cons (itv) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (itv))) ” 
  &&  “ ((m2 (&((itv)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((itv)  # "blist" ->ₛ "next") <> 0) ” 
  &&  “ (itv <> 0) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ (ind = ((hash_string_k (k)) % ( 211 ) )) ” 
  &&  “ (0 <= ind) ” 
  &&  “ (ind < 211) ” 
  &&  “ ((bucket_map (ind)) = (Some ((pair (buck) (l0))))) ” 
  &&  “ (l0 = (app (l_prev) (l_res))) ” 
  &&  “ (contain_all_addrs m1_node (app (dl_up) (dl_down)) ) ” 
  &&  “ (repr_all_heads lh bucket_map ) ” 
  &&  “ (contain_all_correct_addrs m1_node bucket_map ) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (it <> 0) ” 
  &&  “ ((itv = 0) -> ((l_res = (@nil Z)) /\ (dl_down = (@nil Z)))) ” 
  &&  “ ((top = itv) -> ((dl_prev = 0) /\ (dl_up = (@nil Z)))) ” 
  &&  “ ((dl_up <> (@nil Z)) -> (top <> 0)) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((itv)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
  **  (store_string key_pre k )
  **  (store_string b_key k_list )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b_next)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (sll b_next l_resres )
  **  ((&((itv)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  ((&((itv)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((itv)  # "blist" ->ₛ "val") )
  **  ((&((itv)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((itv)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down itv dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
  **  (PtrArray.missing_i h_pre_bucks ind 0 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((removed_pre) # Int  |->_)
.

Definition hashtbl_remove_which_implies_wit_1 := 
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (top: Z)  (h_bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_addrs m1_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
) \/
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (top: Z)  (h_bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_addrs m1_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
).

Definition hashtbl_remove_which_implies_wit_2 := 
(
forall (h_pre: Z) (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucket_map: (Z -> (@option (Z * (@list Z))))) (dl_prev: Z) (dl_down: (@list Z)) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b: Z) (it: Z) (ind: Z) (h_pre_bucks: Z) (PreH1 : (b <> 0)) (PreH2 : (it <> 0)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (not_key k l_prev m1_node )) (PreH6 : (NoDup l_res )) (PreH7 : (current_bucket_suffix m1_node bucket_map ind l_prev l_res )) (PreH8 : (bucket_cells_nonnull h_pre_bucks )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  (store_map store_name m1_node )
  **  (dll b dl_prev dl_down )
  **  (store_map store_uint m2 )
  **  (sll b l_res )
|--
  EX (b_down: Z)  (b_key: Z)  (b_next: Z)  (val: Z)  (k_list: (@list Z))  (dl_downres: (@list Z))  (l_resres: (@list Z)) ,
  “ (b <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (b) (l_resres))) ” 
  &&  “ (dl_down = (cons (b) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (b))) ” 
  &&  “ ((m2 (&((b)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((b)  # "blist" ->ₛ "next") <> 0) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  ((it) # Ptr  |-> b)
  **  (store_map_missing_i store_sll bucket_map ind )
  **  (sllbseg (h_pre_bucks + (ind * sizeof(PTR))) it l_prev )
  **  ((&((b)  # "blist" ->ₛ "next")) # Ptr  |-> b_next)
  **  (sll b_next l_resres )
  **  ((&((b)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  (store_string b_key k_list )
  **  ((&((b)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((b)  # "blist" ->ₛ "val") )
  **  ((&((b)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((b)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down b dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
) \/
(
forall (k: (@list Z)) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (bucket_map: (Z -> (@option (Z * (@list Z))))) (dl_prev: Z) (dl_down: (@list Z)) (l_res: (@list Z)) (l_prev: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (b: Z) (it: Z) (ind: Z) (h_pre_bucks: Z) (x: Z) (l0: (@list Z)) (PreH1 : (b = x)) (PreH2 : (l_res = (cons (x) (l0)))) (PreH3 : (b = x)) (PreH4 : (b <> 0)) (PreH5 : (it <> 0)) (PreH6 : (map_composable m1 m2 )) (PreH7 : (node_value_map m1_node m1 )) (PreH8 : (not_key k l_prev m1_node )) (PreH9 : (NoDup l_res )) (PreH10 : (current_bucket_suffix m1_node bucket_map ind l_prev l_res )) (PreH11 : (bucket_cells_nonnull h_pre_bucks )) ,
  (store_map_missing_i store_sll bucket_map ind )
  **  (store_map store_name m1_node )
  **  (dll b dl_prev dl_down )
  **  (store_map store_uint m2 )
|--
  EX (b_down: Z)  (b_key: Z)  (val: Z)  (k_list: (@list Z))  (dl_downres: (@list Z)) ,
  “ (b <> 0) ” 
  &&  “ (it <> 0) ” 
  &&  “ (l_res = (cons (b) (l0))) ” 
  &&  “ (dl_down = (cons (b) (dl_downres))) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (not_key k l_prev m1_node ) ” 
  &&  “ (NoDup l_res ) ” 
  &&  “ ((m1_node (k_list)) = (Some (b))) ” 
  &&  “ ((m2 (&((b)  # "blist" ->ₛ "val"))) = (Some (val))) ” 
  &&  “ (bucket_cells_nonnull h_pre_bucks ) ” 
  &&  “ (&((b)  # "blist" ->ₛ "next") <> 0) ”
  &&  (store_map_missing_i store_sll bucket_map ind )
  **  ((&((b)  # "blist" ->ₛ "key")) # Ptr  |-> b_key)
  **  (store_string b_key k_list )
  **  ((&((b)  # "blist" ->ₛ "val")) # UInt  |-> val)
  **  (store_map_missing_i store_uint m2 &((b)  # "blist" ->ₛ "val") )
  **  ((&((b)  # "blist" ->ₛ "down")) # Ptr  |-> b_down)
  **  ((&((b)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev)
  **  (dll b_down b dl_downres )
  **  (store_map_missing_i store_name m1_node k_list )
).

Definition hashtbl_remove_which_implies_wit_3 := 
(
forall (top_next: Z) (top: Z) (dl_prev: Z) (dl_up_tail: (@list Z)) (dl_up: (@list Z)) (b: Z) (PreH1 : (dl_prev <> 0)) (PreH2 : (top <> 0)) (PreH3 : (dl_up = (cons (top) (dl_up_tail)))) ,
  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> top_next)
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (dllseg top_next b top dl_prev dl_up_tail )
|--
  EX (dl_prev_prev: Z)  (dl_up_prefix: (@list Z)) ,
  “ (dl_up = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z)))))) ”
  &&  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
) \/
(
forall (top_next: Z) (top: Z) (dl_prev: Z) (dl_up_tail: (@list Z)) (dl_up: (@list Z)) (b: Z) (PreH1 : (dl_prev <> 0)) (PreH2 : (top <> 0)) (PreH3 : (dl_up = (cons (top) (dl_up_tail)))) ,
  ((&((top)  # "blist" ->ₛ "down")) # Ptr  |-> top_next)
  **  ((&((top)  # "blist" ->ₛ "up")) # Ptr  |-> 0)
  **  (dllseg top_next b top dl_prev dl_up_tail )
|--
  EX (dl_prev_prev: Z)  (dl_up_prefix: (@list Z)) ,
  “ (dl_up = (app (dl_up_prefix) ((cons (dl_prev) ((@nil Z)))))) ”
  &&  (dllseg top dl_prev 0 dl_prev_prev dl_up_prefix )
  **  ((&((dl_prev)  # "blist" ->ₛ "down")) # Ptr  |-> b)
  **  ((&((dl_prev)  # "blist" ->ₛ "up")) # Ptr  |-> dl_prev_prev)
).

Definition hashtbl_remove_which_implies_wit_4 := 
(
forall (dl_downres: (@list Z)) (b_down: Z) (b: Z) (PreH1 : (b_down <> 0)) ,
  (dll b_down b dl_downres )
|--
  EX (b_down_down: Z)  (dl_down_tail: (@list Z)) ,
  “ (dl_downres = (cons (b_down) (dl_down_tail))) ”
  &&  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> b)
  **  (dll b_down_down b_down dl_down_tail )
) \/
(
forall (dl_downres: (@list Z)) (b_down: Z) (b: Z) (PreH1 : (b_down <> 0)) ,
  (dll b_down b dl_downres )
|--
  EX (b_down_down: Z)  (dl_down_tail: (@list Z)) ,
  “ (dl_downres = (cons (b_down) (dl_down_tail))) ”
  &&  ((&((b_down)  # "blist" ->ₛ "down")) # Ptr  |-> b_down_down)
  **  ((&((b_down)  # "blist" ->ₛ "up")) # Ptr  |-> b)
  **  (dll b_down_down b_down dl_down_tail )
).

(*----- Function hashtbl_free_blist -----*)

Definition hashtbl_free_blist_safety_wit_1 := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (key_list_for_addrs m1 l ks )) ,
  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_free_blist_return_wit_1 := 
(
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
|--
  (store_map store_name (KP.remove_keys (m1) (ks)) )
  **  (store_map store_uint m2 )
) \/
(
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
|--
  (store_map store_name (KP.remove_keys (m1) (ks)) )
  **  (store_map store_uint m2 )
).

Definition hashtbl_free_blist_return_wit_1_split_goal_spatial := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
|--
  (store_map store_name (KP.remove_keys (m1) (ks)) )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_return_wit_2 := 
(
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (bl_pre = 0)) (PreH2 : (key_list_for_addrs m1 l ks )) ,
  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  (store_map store_name (KP.remove_keys (m1) (ks)) )
  **  (store_map store_uint m2 )
) \/
(
forall (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  “ (l = (@nil Z)) ”
  &&  (store_map store_name (KP.remove_keys (m1) (ks)) )
  **  (store_map store_uint m2 )
).

Definition hashtbl_free_blist_return_wit_2_split_goal_1 := 
forall (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  “ (l = (@nil Z)) ”
.

Definition hashtbl_free_blist_return_wit_2_split_goal_spatial := 
forall (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  (store_map store_name (KP.remove_keys (m1) (ks)) )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_partial_solve_wit_1_pure := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (bl_pre <> 0)) (PreH2 : (key_list_for_addrs m1 l ks )) ,
  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  “ (key_list_for_addrs m1 l ks ) ” 
  &&  “ (bl_pre <> 0) ”
.

Definition hashtbl_free_blist_partial_solve_wit_1_aux := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (PreH1 : (bl_pre <> 0)) (PreH2 : (key_list_for_addrs m1 l ks )) ,
  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
|--
  “ (key_list_for_addrs m1 l ks ) ” 
  &&  “ (bl_pre <> 0) ” 
  &&  “ (bl_pre <> 0) ” 
  &&  “ (key_list_for_addrs m1 l ks ) ”
  &&  (sll bl_pre l )
  **  (store_map store_name m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_partial_solve_wit_1 := hashtbl_free_blist_partial_solve_wit_1_pure -> hashtbl_free_blist_partial_solve_wit_1_aux.

Definition hashtbl_free_blist_partial_solve_wit_2_pure := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_key: Z) (bl_next: Z) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  ((( &( "bl" ) )) # Ptr  |-> bl_pre)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
  **  (store_map store_name (KP.remove_map (m1) (k1)) )
  **  (store_map store_uint m2 )
|--
  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 ) ”
.

Definition hashtbl_free_blist_partial_solve_wit_2_aux := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_key: Z) (bl_next: Z) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
  **  (store_map store_name (KP.remove_map (m1) (k1)) )
  **  (store_map store_uint m2 )
|--
  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 ) ” 
  &&  “ (l = (cons (bl_pre) (l1))) ” 
  &&  “ (ks = (cons (k1) (ks1))) ” 
  &&  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 ) ” 
  &&  “ ((m1 (k1)) = (Some (bl_pre))) ” 
  &&  “ (bl_pre <> 0) ” 
  &&  “ (key_list_for_addrs m1 l ks ) ”
  &&  (sll bl_next l1 )
  **  (store_map store_name (KP.remove_map (m1) (k1)) )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
.

Definition hashtbl_free_blist_partial_solve_wit_2 := hashtbl_free_blist_partial_solve_wit_2_pure -> hashtbl_free_blist_partial_solve_wit_2_aux.

Definition hashtbl_free_blist_partial_solve_wit_3 := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_key: Z) (bl_next: Z) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
|--
  “ (l = (cons (bl_pre) (l1))) ” 
  &&  “ (ks = (cons (k1) (ks1))) ” 
  &&  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 ) ” 
  &&  “ ((m1 (k1)) = (Some (bl_pre))) ” 
  &&  “ (bl_pre <> 0) ” 
  &&  “ (key_list_for_addrs m1 l ks ) ”
  &&  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
  **  (store_string bl_key k1 )
  **  ((&((bl_pre)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
.

Definition hashtbl_free_blist_partial_solve_wit_4 := 
forall (bl_pre: Z) (ks: (@list (@list Z))) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl_next: Z) (k1: (@list Z)) (ks1: (@list (@list Z))) (l1: (@list Z)) (PreH1 : (l = (cons (bl_pre) (l1)))) (PreH2 : (ks = (cons (k1) (ks1)))) (PreH3 : (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 )) (PreH4 : ((m1 (k1)) = (Some (bl_pre)))) (PreH5 : (bl_pre <> 0)) (PreH6 : (key_list_for_addrs m1 l ks )) ,
  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
  **  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
|--
  “ (l = (cons (bl_pre) (l1))) ” 
  &&  “ (ks = (cons (k1) (ks1))) ” 
  &&  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 ) ” 
  &&  “ ((m1 (k1)) = (Some (bl_pre))) ” 
  &&  “ (bl_pre <> 0) ” 
  &&  “ (key_list_for_addrs m1 l ks ) ”
  &&  ((&((bl_pre)  # "blist" ->ₛ "next")) # Ptr  |->_)
  **  (store_map store_name (KP.remove_keys ((KP.remove_map (m1) (k1))) (ks1)) )
  **  (store_map store_uint m2 )
.

Definition hashtbl_free_blist_which_implies_wit_1 := 
(
forall (ks: (@list (@list Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl: Z) (PreH1 : (key_list_for_addrs m1 l ks )) (PreH2 : (bl <> 0)) ,
  (sll bl l )
  **  (store_map store_name m1 )
|--
  EX (bl_key: Z)  (bl_next: Z)  (k1: (@list Z))  (ks1: (@list (@list Z)))  (l1: (@list Z)) ,
  “ (l = (cons (bl) (l1))) ” 
  &&  “ (ks = (cons (k1) (ks1))) ” 
  &&  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l1 ks1 ) ” 
  &&  “ ((m1 (k1)) = (Some (bl))) ”
  &&  ((&((bl)  # "blist" ->ₛ "next")) # Ptr  |-> bl_next)
  **  (sll bl_next l1 )
  **  ((&((bl)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
  **  (store_map store_name (KP.remove_map (m1) (k1)) )
) \/
(
forall (ks: (@list (@list Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (bl: Z) (x: Z) (l0: (@list Z)) (PreH1 : (bl = x)) (PreH2 : (l = (cons (x) (l0)))) (PreH3 : (bl = x)) (PreH4 : (key_list_for_addrs m1 l ks )) (PreH5 : (bl <> 0)) ,
  (store_map store_name m1 )
|--
  EX (bl_key: Z)  (k1: (@list Z))  (ks1: (@list (@list Z))) ,
  “ (l = (cons (bl) (l0))) ” 
  &&  “ (ks = (cons (k1) (ks1))) ” 
  &&  “ (key_list_for_addrs (KP.remove_map (m1) (k1)) l0 ks1 ) ” 
  &&  “ ((m1 (k1)) = (Some (bl))) ”
  &&  ((&((bl)  # "blist" ->ₛ "key")) # Ptr  |-> bl_key)
  **  (store_string bl_key k1 )
  **  (store_map store_name (KP.remove_map (m1) (k1)) )
).

(*----- Function hashtbl_clear -----*)

Definition hashtbl_clear_safety_wit_1 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node m1 )) (PreH2 : (contain_all_addrs m1_node l )) (PreH3 : (repr_all_heads lh b )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (bucket_cells_nonnull h_bucks )) (PreH6 : (map_composable m1 m2 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_clear_safety_wit_2 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top: Z) (h_bucks: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (l: (@list Z)) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node m1 )) (PreH2 : (contain_all_addrs m1_node l )) (PreH3 : (repr_all_heads lh b )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (bucket_cells_nonnull h_bucks )) (PreH6 : (map_composable m1 m2 )) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
  **  (store_map store_uint m2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_clear_safety_wit_3 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) (PreH2 : (node_value_map m1_node m1 )) (PreH3 : (contain_all_correct_addrs m1_node b )) (PreH4 : (repr_all_heads lh b )) (PreH5 : (remaining_after_bucket_index m1_node m_rem i )) (PreH6 : (i >= 0)) (PreH7 : (i < 211)) (PreH8 : (key_list_for_addrs m_rem li ks_i )) (PreH9 : (current_bucket_key_list m_rem b i li ks_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition hashtbl_clear_safety_wit_4 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) (PreH2 : (node_value_map m1_node m1 )) (PreH3 : (contain_all_correct_addrs m1_node b )) (PreH4 : (repr_all_heads lh b )) (PreH5 : (remaining_after_bucket_index m1_node m_rem i )) (PreH6 : (i >= 211)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
|--
  “ (211 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 211) ”
.

Definition hashtbl_clear_safety_wit_5 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node m_rem i )) (PreH7 : (i >= 0)) (PreH8 : (i < 211)) (PreH9 : (key_list_for_addrs m_rem li ks_i )) (PreH10 : (current_bucket_key_list m_rem b i li ks_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  “ False ”
.

Definition hashtbl_clear_safety_wit_6 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i < 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node m_rem i )) (PreH7 : (i >= 211)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
|--
  “ False ”
.

Definition hashtbl_clear_safety_wit_7 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i < 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node m_rem i )) (PreH7 : (i >= 0)) (PreH8 : (i < 211)) (PreH9 : (key_list_for_addrs m_rem li ks_i )) (PreH10 : (current_bucket_key_list m_rem b i li ks_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_clear_safety_wit_8 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i < 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_correct_addrs m1_node b )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (remaining_after_bucket_index m1_node m_rem i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem li ks_i )) (PreH11 : (current_bucket_key_list m_rem b i li ks_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  “ False ”
.

Definition hashtbl_clear_safety_wit_9 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_correct_addrs m1_node b )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (remaining_after_bucket_index m1_node m_rem i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem li ks_i )) (PreH11 : (current_bucket_key_list m_rem b i li ks_i )) ,
  (PtrArray.full h_pre_bucks 211 (replace_Znth (i) (buck_i) (lh)) )
  **  (store_map store_name (KP.remove_keys (m_rem) (ks_i)) )
  **  (store_map store_uint m2 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (store_map_missing_first_i_Z store_sll b i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_clear_safety_wit_10 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_correct_addrs m1_node b )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (remaining_after_bucket_index m1_node m_rem i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem li ks_i )) (PreH11 : (current_bucket_key_list m_rem b i li ks_i )) ,
  (PtrArray.full h_pre_bucks 211 (replace_Znth (i) (0) ((replace_Znth (i) (buck_i) (lh)))) )
  **  (store_map store_name (KP.remove_keys (m_rem) (ks_i)) )
  **  (store_map store_uint m2 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (store_map_missing_first_i_Z store_sll b i )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition hashtbl_clear_safety_wit_11 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node m_rem i )) (PreH7 : (i >= 211)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_clear_safety_wit_12 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node m_rem i )) (PreH7 : (i >= 211)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hashtbl_clear_entail_wit_1 := 
(
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_2: Z) (h_bucks: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (m1_node_2: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node_2 m1 )) (PreH2 : (contain_all_addrs m1_node_2 l_2 )) (PreH3 : (repr_all_heads lh_2 b_2 )) (PreH4 : (contain_all_correct_addrs m1_node_2 b_2 )) (PreH5 : (bucket_cells_nonnull h_bucks )) (PreH6 : (map_composable m1 m2 )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_2)
  **  (dll top_2 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m1_node_2 )
  **  (store_map store_uint m2 )
|--
  EX (buck_i: Z)  (h_pre_bucks: Z)  (li: (@list Z))  (ks_i: (@list (@list Z)))  (l: (@list Z))  (top: Z)  (m_rem: ((@list Z) -> (@option Z)))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem 0 ) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (0 < 211) ” 
  &&  “ (key_list_for_addrs m_rem li ks_i ) ” 
  &&  “ (current_bucket_key_list m_rem b 0 li ks_i ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks 0 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b 0 )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (0 * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
) \/
(
forall (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (top_2: Z) (h_bucks: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (l_2: (@list Z)) (m1_node_2: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node_2 m1 )) (PreH2 : (contain_all_addrs m1_node_2 l_2 )) (PreH3 : (repr_all_heads lh_2 b_2 )) (PreH4 : (contain_all_correct_addrs m1_node_2 b_2 )) (PreH5 : (bucket_cells_nonnull h_bucks )) (PreH6 : (map_composable m1 m2 )) ,
  (PtrArray.missing_i h_bucks 0 0 211 lh_2 )
  **  (dll top_2 0 l_2 )
  **  (store_map store_sll b_2 )
  **  (store_map store_name m1_node_2 )
  **  (store_map store_uint m2 )
|--
  EX (li: (@list Z))  (ks_i: (@list (@list Z)))  (l: (@list Z))  (m_rem: ((@list Z) -> (@option Z)))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem 0 ) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (0 < 211) ” 
  &&  “ (key_list_for_addrs m_rem li ks_i ) ” 
  &&  “ (current_bucket_key_list m_rem b 0 li ks_i ) ”
  &&  (dll top_2 0 l )
  **  (PtrArray.missing_i h_bucks 0 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b 0 )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (sll (Znth 0 lh_2 0) li )
).

Definition hashtbl_clear_entail_wit_2 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i_2: Z) (h_pre_bucks_3: Z) (li_2: (@list Z)) (ks_i_2: (@list (@list Z))) (l_2: (@list Z)) (top_2: Z) (m_rem_2: ((@list Z) -> (@option Z))) (i: Z) (lh_2: (@list Z)) (b_2: (Z -> (@option (Z * (@list Z))))) (m1_node_2: ((@list Z) -> (@option Z))) (PreH1 : (i >= 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node_2 m1 )) (PreH5 : (contain_all_correct_addrs m1_node_2 b_2 )) (PreH6 : (repr_all_heads lh_2 b_2 )) (PreH7 : (remaining_after_bucket_index m1_node_2 m_rem_2 i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem_2 li_2 ks_i_2 )) (PreH11 : (current_bucket_key_list m_rem_2 b_2 i li_2 ks_i_2 )) ,
  (PtrArray.full h_pre_bucks_3 211 (replace_Znth (i) (0) ((replace_Znth (i) (buck_i_2) (lh_2)))) )
  **  (store_map store_name (KP.remove_keys (m_rem_2) (ks_i_2)) )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top_2)
  **  (dll top_2 0 l_2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_3)
  **  (store_map_missing_first_i_Z store_sll b_2 i )
|--
  (EX (buck_i: Z)  (h_pre_bucks: Z)  (li: (@list Z))  (ks_i: (@list (@list Z)))  (l: (@list Z))  (top: Z)  (m_rem: ((@list Z) -> (@option Z)))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem (i + 1 ) ) ” 
  &&  “ ((i + 1 ) >= 0) ” 
  &&  “ ((i + 1 ) < 211) ” 
  &&  “ (key_list_for_addrs m_rem li ks_i ) ” 
  &&  “ (current_bucket_key_list m_rem b (i + 1 ) li ks_i ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks (i + 1 ) 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b (i + 1 ) )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + ((i + 1 ) * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li ))
  ||
  (EX (h_pre_bucks_2: Z)  (l: (@list Z))  (top: Z)  (m_rem: ((@list Z) -> (@option Z)))  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem (i + 1 ) ) ” 
  &&  “ ((i + 1 ) >= 211) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks_2)
  **  (PtrArray.full h_pre_bucks_2 211 lh ))
.

Definition hashtbl_clear_return_wit_1 := 
(
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (l_2: (@list Z)) (top: Z) (m_rem_2: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node_2: ((@list Z) -> (@option Z))) (PreH1 : (i >= 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node_2 m1 )) (PreH4 : (contain_all_correct_addrs m1_node_2 b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node_2 m_rem_2 i )) (PreH7 : (i >= 211)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  (dll top 0 l_2 )
  **  (store_map store_name m_rem_2 )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
|--
  EX (list_head: Z)  (l: (@list Z))  (m_rem: ((@list Z) -> (@option Z)))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem 211 ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  (dll list_head 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
) \/
(
forall (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_rem_2: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node_2: ((@list Z) -> (@option Z))) (PreH1 : (i >= 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node_2 m1 )) (PreH4 : (contain_all_correct_addrs m1_node_2 b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node_2 m_rem_2 i )) (PreH7 : (i >= 211)) ,
  TT && emp 
|--
  EX (m1_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem_2 211 ) ”
  &&  emp
).

Definition hashtbl_clear_partial_solve_wit_1 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) ,
  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
|--
  “ (map_composable m1 m2 ) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
.

Definition hashtbl_clear_partial_solve_wit_2_pure := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_correct_addrs m1_node b )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (remaining_after_bucket_index m1_node m_rem i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem li ks_i )) (PreH11 : (current_bucket_key_list m_rem b i li ks_i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  “ (key_list_for_addrs m_rem li ks_i ) ”
.

Definition hashtbl_clear_partial_solve_wit_2_aux := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_correct_addrs m1_node b )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (remaining_after_bucket_index m1_node m_rem i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem li ks_i )) (PreH11 : (current_bucket_key_list m_rem b i li ks_i )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
  **  (sll buck_i li )
|--
  “ (key_list_for_addrs m_rem li ks_i ) ” 
  &&  “ (i >= 0) ” 
  &&  “ (i < 211) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem i ) ” 
  &&  “ (i >= 0) ” 
  &&  “ (i < 211) ” 
  &&  “ (key_list_for_addrs m_rem li ks_i ) ” 
  &&  “ (current_bucket_key_list m_rem b i li ks_i ) ”
  &&  (sll buck_i li )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 lh )
  **  (store_map_missing_first_i_Z store_sll b i )
  **  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |-> buck_i)
.

Definition hashtbl_clear_partial_solve_wit_2 := hashtbl_clear_partial_solve_wit_2_pure -> hashtbl_clear_partial_solve_wit_2_aux.

Definition hashtbl_clear_partial_solve_wit_3 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (buck_i: Z) (h_pre_bucks: Z) (li: (@list Z)) (ks_i: (@list (@list Z))) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 0)) (PreH2 : (i < 211)) (PreH3 : (map_composable m1 m2 )) (PreH4 : (node_value_map m1_node m1 )) (PreH5 : (contain_all_correct_addrs m1_node b )) (PreH6 : (repr_all_heads lh b )) (PreH7 : (remaining_after_bucket_index m1_node m_rem i )) (PreH8 : (i >= 0)) (PreH9 : (i < 211)) (PreH10 : (key_list_for_addrs m_rem li ks_i )) (PreH11 : (current_bucket_key_list m_rem b i li ks_i )) ,
  (PtrArray.full h_pre_bucks 211 (replace_Znth (i) (buck_i) (lh)) )
  **  (store_map store_name (KP.remove_keys (m_rem) (ks_i)) )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (store_map_missing_first_i_Z store_sll b i )
|--
  “ (i >= 0) ” 
  &&  “ (i < 211) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem i ) ” 
  &&  “ (i >= 0) ” 
  &&  “ (i < 211) ” 
  &&  “ (key_list_for_addrs m_rem li ks_i ) ” 
  &&  “ (current_bucket_key_list m_rem b i li ks_i ) ”
  &&  (((h_pre_bucks + (i * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i h_pre_bucks i 0 211 (replace_Znth (i) (buck_i) (lh)) )
  **  (store_map store_name (KP.remove_keys (m_rem) (ks_i)) )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (store_map_missing_first_i_Z store_sll b i )
.

Definition hashtbl_clear_partial_solve_wit_4 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (h_pre_bucks: Z) (l: (@list Z)) (top: Z) (m_rem: ((@list Z) -> (@option Z))) (i: Z) (lh: (@list Z)) (b: (Z -> (@option (Z * (@list Z))))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (i >= 211)) (PreH2 : (map_composable m1 m2 )) (PreH3 : (node_value_map m1_node m1 )) (PreH4 : (contain_all_correct_addrs m1_node b )) (PreH5 : (repr_all_heads lh b )) (PreH6 : (remaining_after_bucket_index m1_node m_rem i )) (PreH7 : (i >= 211)) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
  **  (PtrArray.full h_pre_bucks 211 lh )
|--
  “ (i >= 211) ” 
  &&  “ (map_composable m1 m2 ) ” 
  &&  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem i ) ” 
  &&  “ (i >= 211) ”
  &&  (PtrArray.full h_pre_bucks 211 lh )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_pre_bucks)
.

Definition hashtbl_clear_which_implies_wit_1 := 
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (top: Z)  (h_bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_addrs m1_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
) \/
(
forall (m1: ((@list Z) -> (@option Z))) (h: Z) ,
  (store_hash_skeleton h m1 )
|--
  EX (top: Z)  (h_bucks: Z)  (lh: (@list Z))  (b: (Z -> (@option (Z * (@list Z)))))  (l: (@list Z))  (m1_node: ((@list Z) -> (@option Z))) ,
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (contain_all_addrs m1_node l ) ” 
  &&  “ (repr_all_heads lh b ) ” 
  &&  “ (contain_all_correct_addrs m1_node b ) ” 
  &&  “ (bucket_cells_nonnull h_bucks ) ”
  &&  ((&((h)  # "hashtbl" ->ₛ "top")) # Ptr  |-> top)
  **  (dll top 0 l )
  **  ((&((h)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> h_bucks)
  **  (PtrArray.full h_bucks 211 lh )
  **  (store_map store_sll b )
  **  (store_map store_name m1_node )
).

(*----- Function free_hashtbl -----*)

Definition free_hashtbl_return_wit_1 := 
forall (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (m_rem: ((@list Z) -> (@option Z))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node m1 )) (PreH2 : (remaining_after_bucket_index m1_node m_rem 211 )) (PreH3 : (map_composable m1 m2 )) ,
  TT && emp 
|--
  TT && emp 
.

Definition free_hashtbl_partial_solve_wit_1_pure := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) ,
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
|--
  “ (map_composable m1 m2 ) ”
.

Definition free_hashtbl_partial_solve_wit_1_aux := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (PreH1 : (map_composable m1 m2 )) ,
  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
|--
  “ (map_composable m1 m2 ) ” 
  &&  “ (map_composable m1 m2 ) ”
  &&  (store_hash_skeleton h_pre m1 )
  **  (store_map store_uint m2 )
.

Definition free_hashtbl_partial_solve_wit_1 := free_hashtbl_partial_solve_wit_1_pure -> free_hashtbl_partial_solve_wit_1_aux.

Definition free_hashtbl_partial_solve_wit_2 := 
forall (h_pre: Z) (m2: (Z -> (@option Z))) (m1: ((@list Z) -> (@option Z))) (list_head: Z) (l: (@list Z)) (m_rem: ((@list Z) -> (@option Z))) (m1_node: ((@list Z) -> (@option Z))) (PreH1 : (node_value_map m1_node m1 )) (PreH2 : (remaining_after_bucket_index m1_node m_rem 211 )) (PreH3 : (map_composable m1 m2 )) ,
  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  (dll list_head 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
|--
  “ (node_value_map m1_node m1 ) ” 
  &&  “ (remaining_after_bucket_index m1_node m_rem 211 ) ” 
  &&  “ (map_composable m1 m2 ) ”
  &&  ((&((h_pre)  # "hashtbl" ->ₛ "top")) # Ptr  |-> 0)
  **  ((&((h_pre)  # "hashtbl" ->ₛ "bucks")) # Ptr  |-> 0)
  **  (dll list_head 0 l )
  **  (store_map store_name m_rem )
  **  (store_map store_uint m2 )
.

Module Type VC_Correct.

Include hashtbl_Strategy_Correct.

Axiom proof_of_create_bucks_safety_wit_1 : create_bucks_safety_wit_1.
Axiom proof_of_create_bucks_safety_wit_2 : create_bucks_safety_wit_2.
Axiom proof_of_create_bucks_safety_wit_3 : create_bucks_safety_wit_3.
Axiom proof_of_create_bucks_safety_wit_4 : create_bucks_safety_wit_4.
Axiom proof_of_create_bucks_entail_wit_1 : create_bucks_entail_wit_1.
Axiom proof_of_create_bucks_entail_wit_2 : create_bucks_entail_wit_2.
Axiom proof_of_create_bucks_return_wit_1 : create_bucks_return_wit_1.
Axiom proof_of_create_bucks_partial_solve_wit_1 : create_bucks_partial_solve_wit_1.
Axiom proof_of_create_bucks_partial_solve_wit_2 : create_bucks_partial_solve_wit_2.
Axiom proof_of_init_hashtbl_safety_wit_1 : init_hashtbl_safety_wit_1.
Axiom proof_of_init_hashtbl_safety_wit_2 : init_hashtbl_safety_wit_2.
Axiom proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Axiom proof_of_init_hashtbl_partial_solve_wit_1 : init_hashtbl_partial_solve_wit_1.
Axiom proof_of_create_hashtbl_entail_wit_1 : create_hashtbl_entail_wit_1.
Axiom proof_of_create_hashtbl_return_wit_1 : create_hashtbl_return_wit_1.
Axiom proof_of_create_hashtbl_partial_solve_wit_1 : create_hashtbl_partial_solve_wit_1.
Axiom proof_of_create_hashtbl_partial_solve_wit_2 : create_hashtbl_partial_solve_wit_2.
Axiom proof_of_hashtbl_add_safety_wit_1 : hashtbl_add_safety_wit_1.
Axiom proof_of_hashtbl_add_safety_wit_2 : hashtbl_add_safety_wit_2.
Axiom proof_of_hashtbl_add_safety_wit_3 : hashtbl_add_safety_wit_3.
Axiom proof_of_hashtbl_add_safety_wit_4 : hashtbl_add_safety_wit_4.
Axiom proof_of_hashtbl_add_entail_wit_1 : hashtbl_add_entail_wit_1.
Axiom proof_of_hashtbl_add_return_wit_1 : hashtbl_add_return_wit_1.
Axiom proof_of_hashtbl_add_return_wit_2 : hashtbl_add_return_wit_2.
Axiom proof_of_hashtbl_add_partial_solve_wit_1 : hashtbl_add_partial_solve_wit_1.
Axiom proof_of_hashtbl_add_partial_solve_wit_2 : hashtbl_add_partial_solve_wit_2.
Axiom proof_of_hashtbl_add_partial_solve_wit_3 : hashtbl_add_partial_solve_wit_3.
Axiom proof_of_hashtbl_add_partial_solve_wit_4_pure : hashtbl_add_partial_solve_wit_4_pure.
Axiom proof_of_hashtbl_add_partial_solve_wit_4 : hashtbl_add_partial_solve_wit_4.
Axiom proof_of_hashtbl_add_partial_solve_wit_5 : hashtbl_add_partial_solve_wit_5.
Axiom proof_of_hashtbl_add_partial_solve_wit_6 : hashtbl_add_partial_solve_wit_6.
Axiom proof_of_hashtbl_add_partial_solve_wit_7 : hashtbl_add_partial_solve_wit_7.
Axiom proof_of_hashtbl_add_partial_solve_wit_8 : hashtbl_add_partial_solve_wit_8.
Axiom proof_of_hashtbl_add_which_implies_wit_1 : hashtbl_add_which_implies_wit_1.
Axiom proof_of_hashtbl_add_which_implies_wit_2 : hashtbl_add_which_implies_wit_2.
Axiom proof_of_hashtbl_find_safety_wit_1 : hashtbl_find_safety_wit_1.
Axiom proof_of_hashtbl_find_safety_wit_2 : hashtbl_find_safety_wit_2.
Axiom proof_of_hashtbl_find_safety_wit_3 : hashtbl_find_safety_wit_3.
Axiom proof_of_hashtbl_find_safety_wit_4 : hashtbl_find_safety_wit_4.
Axiom proof_of_hashtbl_find_safety_wit_5 : hashtbl_find_safety_wit_5.
Axiom proof_of_hashtbl_find_safety_wit_6 : hashtbl_find_safety_wit_6.
Axiom proof_of_hashtbl_find_safety_wit_7 : hashtbl_find_safety_wit_7.
Axiom proof_of_hashtbl_find_safety_wit_8 : hashtbl_find_safety_wit_8.
Axiom proof_of_hashtbl_find_safety_wit_9 : hashtbl_find_safety_wit_9.
Axiom proof_of_hashtbl_find_safety_wit_10 : hashtbl_find_safety_wit_10.
Axiom proof_of_hashtbl_find_safety_wit_11 : hashtbl_find_safety_wit_11.
Axiom proof_of_hashtbl_find_entail_wit_1 : hashtbl_find_entail_wit_1.
Axiom proof_of_hashtbl_find_entail_wit_2 : hashtbl_find_entail_wit_2.
Axiom proof_of_hashtbl_find_entail_wit_3 : hashtbl_find_entail_wit_3.
Axiom proof_of_hashtbl_find_entail_wit_4_1 : hashtbl_find_entail_wit_4_1.
Axiom proof_of_hashtbl_find_entail_wit_4_2 : hashtbl_find_entail_wit_4_2.
Axiom proof_of_hashtbl_find_entail_wit_4_3 : hashtbl_find_entail_wit_4_3.
Axiom proof_of_hashtbl_find_entail_wit_4_4 : hashtbl_find_entail_wit_4_4.
Axiom proof_of_hashtbl_find_entail_wit_5_1 : hashtbl_find_entail_wit_5_1.
Axiom proof_of_hashtbl_find_entail_wit_5_2 : hashtbl_find_entail_wit_5_2.
Axiom proof_of_hashtbl_find_entail_wit_5_3 : hashtbl_find_entail_wit_5_3.
Axiom proof_of_hashtbl_find_entail_wit_5_4 : hashtbl_find_entail_wit_5_4.
Axiom proof_of_hashtbl_find_entail_wit_6_1 : hashtbl_find_entail_wit_6_1.
Axiom proof_of_hashtbl_find_entail_wit_6_2 : hashtbl_find_entail_wit_6_2.
Axiom proof_of_hashtbl_find_return_wit_1 : hashtbl_find_return_wit_1.
Axiom proof_of_hashtbl_find_return_wit_2 : hashtbl_find_return_wit_2.
Axiom proof_of_hashtbl_find_return_wit_3 : hashtbl_find_return_wit_3.
Axiom proof_of_hashtbl_find_partial_solve_wit_1 : hashtbl_find_partial_solve_wit_1.
Axiom proof_of_hashtbl_find_partial_solve_wit_2 : hashtbl_find_partial_solve_wit_2.
Axiom proof_of_hashtbl_find_partial_solve_wit_3 : hashtbl_find_partial_solve_wit_3.
Axiom proof_of_hashtbl_find_partial_solve_wit_4 : hashtbl_find_partial_solve_wit_4.
Axiom proof_of_hashtbl_find_partial_solve_wit_5 : hashtbl_find_partial_solve_wit_5.
Axiom proof_of_hashtbl_find_partial_solve_wit_6 : hashtbl_find_partial_solve_wit_6.
Axiom proof_of_hashtbl_find_partial_solve_wit_7 : hashtbl_find_partial_solve_wit_7.
Axiom proof_of_hashtbl_find_partial_solve_wit_8 : hashtbl_find_partial_solve_wit_8.
Axiom proof_of_hashtbl_find_which_implies_wit_1 : hashtbl_find_which_implies_wit_1.
Axiom proof_of_hashtbl_findref_safety_wit_1 : hashtbl_findref_safety_wit_1.
Axiom proof_of_hashtbl_findref_safety_wit_2 : hashtbl_findref_safety_wit_2.
Axiom proof_of_hashtbl_findref_safety_wit_3 : hashtbl_findref_safety_wit_3.
Axiom proof_of_hashtbl_findref_safety_wit_4 : hashtbl_findref_safety_wit_4.
Axiom proof_of_hashtbl_findref_safety_wit_5 : hashtbl_findref_safety_wit_5.
Axiom proof_of_hashtbl_findref_safety_wit_6 : hashtbl_findref_safety_wit_6.
Axiom proof_of_hashtbl_findref_entail_wit_1 : hashtbl_findref_entail_wit_1.
Axiom proof_of_hashtbl_findref_entail_wit_2_1 : hashtbl_findref_entail_wit_2_1.
Axiom proof_of_hashtbl_findref_entail_wit_2_2 : hashtbl_findref_entail_wit_2_2.
Axiom proof_of_hashtbl_findref_entail_wit_3_1 : hashtbl_findref_entail_wit_3_1.
Axiom proof_of_hashtbl_findref_entail_wit_3_2 : hashtbl_findref_entail_wit_3_2.
Axiom proof_of_hashtbl_findref_entail_wit_4 : hashtbl_findref_entail_wit_4.
Axiom proof_of_hashtbl_findref_entail_wit_5 : hashtbl_findref_entail_wit_5.
Axiom proof_of_hashtbl_findref_return_wit_1 : hashtbl_findref_return_wit_1.
Axiom proof_of_hashtbl_findref_return_wit_2 : hashtbl_findref_return_wit_2.
Axiom proof_of_hashtbl_findref_return_wit_3 : hashtbl_findref_return_wit_3.
Axiom proof_of_hashtbl_findref_partial_solve_wit_1 : hashtbl_findref_partial_solve_wit_1.
Axiom proof_of_hashtbl_findref_partial_solve_wit_2 : hashtbl_findref_partial_solve_wit_2.
Axiom proof_of_hashtbl_findref_partial_solve_wit_3_pure : hashtbl_findref_partial_solve_wit_3_pure.
Axiom proof_of_hashtbl_findref_partial_solve_wit_3 : hashtbl_findref_partial_solve_wit_3.
Axiom proof_of_hashtbl_findref_partial_solve_wit_4 : hashtbl_findref_partial_solve_wit_4.
Axiom proof_of_hashtbl_findref_partial_solve_wit_5_pure : hashtbl_findref_partial_solve_wit_5_pure.
Axiom proof_of_hashtbl_findref_partial_solve_wit_5 : hashtbl_findref_partial_solve_wit_5.
Axiom proof_of_hashtbl_findref_partial_solve_wit_6 : hashtbl_findref_partial_solve_wit_6.
Axiom proof_of_hashtbl_findref_partial_solve_wit_7 : hashtbl_findref_partial_solve_wit_7.
Axiom proof_of_hashtbl_findref_partial_solve_wit_8 : hashtbl_findref_partial_solve_wit_8.
Axiom proof_of_hashtbl_findref_partial_solve_wit_9 : hashtbl_findref_partial_solve_wit_9.
Axiom proof_of_hashtbl_findref_which_implies_wit_1 : hashtbl_findref_which_implies_wit_1.
Axiom proof_of_hashtbl_findref_which_implies_wit_2 : hashtbl_findref_which_implies_wit_2.
Axiom proof_of_hashtbl_findref_which_implies_wit_3 : hashtbl_findref_which_implies_wit_3.
Axiom proof_of_hashtbl_remove_safety_wit_1 : hashtbl_remove_safety_wit_1.
Axiom proof_of_hashtbl_remove_safety_wit_2 : hashtbl_remove_safety_wit_2.
Axiom proof_of_hashtbl_remove_safety_wit_3 : hashtbl_remove_safety_wit_3.
Axiom proof_of_hashtbl_remove_safety_wit_4 : hashtbl_remove_safety_wit_4.
Axiom proof_of_hashtbl_remove_safety_wit_5 : hashtbl_remove_safety_wit_5.
Axiom proof_of_hashtbl_remove_safety_wit_6 : hashtbl_remove_safety_wit_6.
Axiom proof_of_hashtbl_remove_safety_wit_7 : hashtbl_remove_safety_wit_7.
Axiom proof_of_hashtbl_remove_safety_wit_8 : hashtbl_remove_safety_wit_8.
Axiom proof_of_hashtbl_remove_safety_wit_9 : hashtbl_remove_safety_wit_9.
Axiom proof_of_hashtbl_remove_safety_wit_10 : hashtbl_remove_safety_wit_10.
Axiom proof_of_hashtbl_remove_safety_wit_11 : hashtbl_remove_safety_wit_11.
Axiom proof_of_hashtbl_remove_safety_wit_12 : hashtbl_remove_safety_wit_12.
Axiom proof_of_hashtbl_remove_safety_wit_13 : hashtbl_remove_safety_wit_13.
Axiom proof_of_hashtbl_remove_safety_wit_14 : hashtbl_remove_safety_wit_14.
Axiom proof_of_hashtbl_remove_safety_wit_15 : hashtbl_remove_safety_wit_15.
Axiom proof_of_hashtbl_remove_safety_wit_16 : hashtbl_remove_safety_wit_16.
Axiom proof_of_hashtbl_remove_safety_wit_17 : hashtbl_remove_safety_wit_17.
Axiom proof_of_hashtbl_remove_safety_wit_18 : hashtbl_remove_safety_wit_18.
Axiom proof_of_hashtbl_remove_safety_wit_19 : hashtbl_remove_safety_wit_19.
Axiom proof_of_hashtbl_remove_entail_wit_1 : hashtbl_remove_entail_wit_1.
Axiom proof_of_hashtbl_remove_entail_wit_2_1 : hashtbl_remove_entail_wit_2_1.
Axiom proof_of_hashtbl_remove_entail_wit_2_2 : hashtbl_remove_entail_wit_2_2.
Axiom proof_of_hashtbl_remove_entail_wit_3_1 : hashtbl_remove_entail_wit_3_1.
Axiom proof_of_hashtbl_remove_entail_wit_3_2 : hashtbl_remove_entail_wit_3_2.
Axiom proof_of_hashtbl_remove_entail_wit_4 : hashtbl_remove_entail_wit_4.
Axiom proof_of_hashtbl_remove_return_wit_1 : hashtbl_remove_return_wit_1.
Axiom proof_of_hashtbl_remove_return_wit_2 : hashtbl_remove_return_wit_2.
Axiom proof_of_hashtbl_remove_return_wit_3 : hashtbl_remove_return_wit_3.
Axiom proof_of_hashtbl_remove_return_wit_4 : hashtbl_remove_return_wit_4.
Axiom proof_of_hashtbl_remove_return_wit_5 : hashtbl_remove_return_wit_5.
Axiom proof_of_hashtbl_remove_return_wit_6 : hashtbl_remove_return_wit_6.
Axiom proof_of_hashtbl_remove_return_wit_7 : hashtbl_remove_return_wit_7.
Axiom proof_of_hashtbl_remove_partial_solve_wit_1 : hashtbl_remove_partial_solve_wit_1.
Axiom proof_of_hashtbl_remove_partial_solve_wit_2 : hashtbl_remove_partial_solve_wit_2.
Axiom proof_of_hashtbl_remove_partial_solve_wit_3_pure : hashtbl_remove_partial_solve_wit_3_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_3 : hashtbl_remove_partial_solve_wit_3.
Axiom proof_of_hashtbl_remove_partial_solve_wit_4 : hashtbl_remove_partial_solve_wit_4.
Axiom proof_of_hashtbl_remove_partial_solve_wit_5_pure : hashtbl_remove_partial_solve_wit_5_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_5 : hashtbl_remove_partial_solve_wit_5.
Axiom proof_of_hashtbl_remove_partial_solve_wit_6_pure : hashtbl_remove_partial_solve_wit_6_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_6 : hashtbl_remove_partial_solve_wit_6.
Axiom proof_of_hashtbl_remove_partial_solve_wit_7_pure : hashtbl_remove_partial_solve_wit_7_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_7 : hashtbl_remove_partial_solve_wit_7.
Axiom proof_of_hashtbl_remove_partial_solve_wit_8_pure : hashtbl_remove_partial_solve_wit_8_pure.
Axiom proof_of_hashtbl_remove_partial_solve_wit_8 : hashtbl_remove_partial_solve_wit_8.
Axiom proof_of_hashtbl_remove_partial_solve_wit_9 : hashtbl_remove_partial_solve_wit_9.
Axiom proof_of_hashtbl_remove_partial_solve_wit_10 : hashtbl_remove_partial_solve_wit_10.
Axiom proof_of_hashtbl_remove_partial_solve_wit_11 : hashtbl_remove_partial_solve_wit_11.
Axiom proof_of_hashtbl_remove_partial_solve_wit_12 : hashtbl_remove_partial_solve_wit_12.
Axiom proof_of_hashtbl_remove_partial_solve_wit_13 : hashtbl_remove_partial_solve_wit_13.
Axiom proof_of_hashtbl_remove_partial_solve_wit_14 : hashtbl_remove_partial_solve_wit_14.
Axiom proof_of_hashtbl_remove_which_implies_wit_1 : hashtbl_remove_which_implies_wit_1.
Axiom proof_of_hashtbl_remove_which_implies_wit_2 : hashtbl_remove_which_implies_wit_2.
Axiom proof_of_hashtbl_remove_which_implies_wit_3 : hashtbl_remove_which_implies_wit_3.
Axiom proof_of_hashtbl_remove_which_implies_wit_4 : hashtbl_remove_which_implies_wit_4.
Axiom proof_of_hashtbl_free_blist_safety_wit_1 : hashtbl_free_blist_safety_wit_1.
Axiom proof_of_hashtbl_free_blist_return_wit_1 : hashtbl_free_blist_return_wit_1.
Axiom proof_of_hashtbl_free_blist_return_wit_2 : hashtbl_free_blist_return_wit_2.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_1_pure : hashtbl_free_blist_partial_solve_wit_1_pure.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_1 : hashtbl_free_blist_partial_solve_wit_1.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_2_pure : hashtbl_free_blist_partial_solve_wit_2_pure.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_2 : hashtbl_free_blist_partial_solve_wit_2.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_3 : hashtbl_free_blist_partial_solve_wit_3.
Axiom proof_of_hashtbl_free_blist_partial_solve_wit_4 : hashtbl_free_blist_partial_solve_wit_4.
Axiom proof_of_hashtbl_free_blist_which_implies_wit_1 : hashtbl_free_blist_which_implies_wit_1.
Axiom proof_of_hashtbl_clear_safety_wit_1 : hashtbl_clear_safety_wit_1.
Axiom proof_of_hashtbl_clear_safety_wit_2 : hashtbl_clear_safety_wit_2.
Axiom proof_of_hashtbl_clear_safety_wit_3 : hashtbl_clear_safety_wit_3.
Axiom proof_of_hashtbl_clear_safety_wit_4 : hashtbl_clear_safety_wit_4.
Axiom proof_of_hashtbl_clear_safety_wit_5 : hashtbl_clear_safety_wit_5.
Axiom proof_of_hashtbl_clear_safety_wit_6 : hashtbl_clear_safety_wit_6.
Axiom proof_of_hashtbl_clear_safety_wit_7 : hashtbl_clear_safety_wit_7.
Axiom proof_of_hashtbl_clear_safety_wit_8 : hashtbl_clear_safety_wit_8.
Axiom proof_of_hashtbl_clear_safety_wit_9 : hashtbl_clear_safety_wit_9.
Axiom proof_of_hashtbl_clear_safety_wit_10 : hashtbl_clear_safety_wit_10.
Axiom proof_of_hashtbl_clear_safety_wit_11 : hashtbl_clear_safety_wit_11.
Axiom proof_of_hashtbl_clear_safety_wit_12 : hashtbl_clear_safety_wit_12.
Axiom proof_of_hashtbl_clear_entail_wit_1 : hashtbl_clear_entail_wit_1.
Axiom proof_of_hashtbl_clear_entail_wit_2 : hashtbl_clear_entail_wit_2.
Axiom proof_of_hashtbl_clear_return_wit_1 : hashtbl_clear_return_wit_1.
Axiom proof_of_hashtbl_clear_partial_solve_wit_1 : hashtbl_clear_partial_solve_wit_1.
Axiom proof_of_hashtbl_clear_partial_solve_wit_2_pure : hashtbl_clear_partial_solve_wit_2_pure.
Axiom proof_of_hashtbl_clear_partial_solve_wit_2 : hashtbl_clear_partial_solve_wit_2.
Axiom proof_of_hashtbl_clear_partial_solve_wit_3 : hashtbl_clear_partial_solve_wit_3.
Axiom proof_of_hashtbl_clear_partial_solve_wit_4 : hashtbl_clear_partial_solve_wit_4.
Axiom proof_of_hashtbl_clear_which_implies_wit_1 : hashtbl_clear_which_implies_wit_1.
Axiom proof_of_free_hashtbl_return_wit_1 : free_hashtbl_return_wit_1.
Axiom proof_of_free_hashtbl_partial_solve_wit_1_pure : free_hashtbl_partial_solve_wit_1_pure.
Axiom proof_of_free_hashtbl_partial_solve_wit_1 : free_hashtbl_partial_solve_wit_1.
Axiom proof_of_free_hashtbl_partial_solve_wit_2 : free_hashtbl_partial_solve_wit_2.

End VC_Correct.
